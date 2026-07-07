#!/usr/bin/env python3
"""Completeness & status audit for the lambdapi-zf port.

Faithfulness to Isabelle/ZF has two halves:
  1. STATEMENT FIDELITY — each ported statement matches the source (checked by eye).
  2. COMPLETENESS — every definition/lemma/theorem in the source `.thy` has a
     corresponding symbol in the `.lp`.  THIS TOOL CHECKS (2).

It parses `isabelle-src/<Thy>.thy` for declared names and compares them against the
`symbol`s in `<Module>.lp`.  Isabelle names that are pure simplifier/automation
plumbing (which TRANSLATE-style guidance says to skip) are reported in a separate
"automation/skip?" bucket rather than as genuine gaps.  Names that look renamed in
the port (e.g. Isabelle `case` → lp `case_sum`) are flagged as "possible rename".

Usage:
  tools/audit.py                  # detailed audit of every ported module
  tools/audit.py Order Sum        # detailed audit of the named modules
  tools/audit.py --status         # one-line-per-module dashboard + un-ported list

Exit status is always 0 (this is an informational tool, not a gate).
"""
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ISA = REPO / "isabelle-src"

# lp module name -> Isabelle theory name (default: identical).  lp modules with no
# Isabelle counterpart (local glue) map to None and are skipped for completeness.
LP_TO_THY = {"Bool_ZF": "Bool", "ZF_Base": "ZF_Base", "ZF_extra": None,
             "Nat_ZF": "Nat"}

# Isabelle automation/plumbing: present in the source but not meaningful to port
# as standalone results (simp setup, atomize, lemma bundles for the simplifier).
SKIP_RE = re.compile(r"(^atomize_)|(_simps?$)|(_simps[12]$)|(^setup)|(_cong_simp$)")

NAME = r"[A-Za-z][A-Za-z0-9_']*"
LP_SYMBOL_RE = re.compile(
    r"^(?:opaque |constant |injective |sequential |private )*symbol\s+(" + NAME + r")"
)


def strip_comments(text: str) -> str:
    # Isabelle (* ... *) comments (non-nested approximation) and \<comment>.
    return re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)


def thy_names(path: Path):
    """Return the set of declared definition/lemma/theorem names in a .thy."""
    text = strip_comments(path.read_text(errors="replace"))
    lines = text.splitlines()
    names = set()
    kw_re = re.compile(r"^\s*(definition|abbreviation|lemma|lemmas|theorem|corollary)\b(.*)")
    for i, line in enumerate(lines):
        m = kw_re.match(line)
        if not m:
            continue
        kw, rest = m.group(1), m.group(2).lstrip()
        nm = _first_name(rest)
        if not nm and kw in ("definition", "abbreviation"):
            # name may sit on the following non-blank line(s)
            for j in range(i + 1, min(i + 4, len(lines))):
                nxt = lines[j].strip()
                if nxt:
                    nm = _first_name(nxt)
                    break
        if nm:
            names.add(nm)
    return names


def _first_name(rest: str):
    """Extract a leading (possibly quoted) Isabelle identifier, else None.

    `lemma "stmt"` (anonymous) yields None; `definition "case" ::` yields case;
    `lemma foo [attr]:` yields foo."""
    rest = rest.lstrip()
    mq = re.match(r'"(' + NAME + r')"', rest)
    if mq:
        return mq.group(1)
    if rest.startswith('"'):
        return None  # anonymous statement, not a quoted name
    mi = re.match(r"(" + NAME + r")", rest)
    return mi.group(1) if mi else None


def lp_symbols(path: Path):
    syms = set()
    for line in path.read_text(errors="replace").splitlines():
        m = LP_SYMBOL_RE.match(line)
        if m:
            syms.add(m.group(1))
    return syms


def rename_hint(missing: str, syms: set):
    for s in syms:
        if missing != s and (missing in s or s in missing):
            return s
    return None


def audit_module(lp_name: str):
    thy_name = LP_TO_THY.get(lp_name, lp_name)
    if thy_name is None:
        return None
    thy = ISA / f"{thy_name}.thy"
    lp = REPO / f"{lp_name}.lp"
    if not thy.exists() or not lp.exists():
        return None
    src = thy_names(thy)
    syms = lp_symbols(lp)
    present, genuine, skip, renamed = [], [], [], []
    for n in sorted(src):
        if n in syms:
            present.append(n)
        elif SKIP_RE.search(n):
            skip.append(n)
        else:
            hint = rename_hint(n, syms)
            (renamed if hint else genuine).append((n, hint))
    return {"thy": thy_name, "total": len(src), "present": present,
            "genuine": genuine, "skip": skip, "renamed": renamed}


def ported_modules():
    out = []
    for lp in sorted(REPO.glob("*.lp")):
        if LP_TO_THY.get(lp.stem, lp.stem) is None:
            continue
        if (ISA / f"{LP_TO_THY.get(lp.stem, lp.stem)}.thy").exists():
            out.append(lp.stem)
    return out


def admit_tactics(lp_name: str) -> int:
    lp = REPO / f"{lp_name}.lp"
    return sum(1 for ln in lp.read_text(errors="replace").splitlines()
               if re.match(r"\s*admit\b", ln))


def print_detail(r):
    cov = len(r["present"])
    print(f"\n=== {r['thy']}  —  {cov}/{r['total']} present, "
          f"{len(r['genuine'])} missing"
          + (f", {len(r['renamed'])} renamed?" if r["renamed"] else "")
          + (f", {len(r['skip'])} automation" if r["skip"] else ""))
    if r["genuine"]:
        print("  MISSING (genuine):")
        for n, _ in r["genuine"]:
            print(f"    - {n}")
    if r["renamed"]:
        print("  possible renames (present under another name — verify):")
        for n, hint in r["renamed"]:
            print(f"    - {n}  ~?  {hint}")
    if r["skip"]:
        print("  automation/skip? (Isabelle simp plumbing): "
              + ", ".join(n for n, *_ in [(x,) for x in r["skip"]]))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    status = "--status" in sys.argv[1:]
    if status:
        print(f"{'module':<14}{'admits':>7}  completeness (genuine-missing)")
        print("-" * 56)
        for m in ported_modules():
            r = audit_module(m)
            cov = f"{len(r['present'])}/{r['total']}" if r else "n/a"
            miss = len(r["genuine"]) if r else 0
            flag = "" if miss == 0 else f"  ⚠ {miss} missing"
            print(f"{m:<14}{admit_tactics(m):>7}  {cov:<10}{flag}")
        # un-ported theories (a .thy with no matching .lp) — the frontier.
        ported_thys = {LP_TO_THY.get(m, m) for m in ported_modules()}
        unported = sorted(p.stem for p in ISA.glob("*.thy") if p.stem not in ported_thys)
        print("\nun-ported .thy (candidates / out-of-scope meta-theories):")
        print("  " + ", ".join(unported))
        return
    mods = args if args else ported_modules()
    for m in mods:
        r = audit_module(m)
        if r is None:
            print(f"\n=== {m}: no isabelle-src/{LP_TO_THY.get(m, m)}.thy or no {m}.lp")
        else:
            print_detail(r)


if __name__ == "__main__":
    main()
