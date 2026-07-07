#!/usr/bin/env python3
"""fidelity.py — pair each Isabelle statement with its Lambdapi counterpart.

Faithfulness has two halves (CLAUDE.md §4). `audit.py`/`status.py` cover
COMPLETENESS (is the name present?). This tool serves STATEMENT FIDELITY: it
puts the Isabelle source statement and the ported `.lp` statement side by side,
by name, so a *weakened* port — an added `Ord` hypothesis, a dropped premise, a
specialised conclusion — is visible instead of silently passing a name check.

It cannot mechanically prove two statements equivalent (the syntaxes differ);
its job is to SURFACE the pair. In the autonomous loop, feed `--json` for the
symbols you just touched to a judge subagent that rules faithful / weakened /
mismatch. By eye, scan the aligned columns for a module.

Usage:
  tools/fidelity.py Order              # every paired statement in the module
  tools/fidelity.py Order --diff       # only pairs that look suspicious/unmatched
  tools/fidelity.py Order --only NAME  # one lemma
  tools/fidelity.py Order --json       # {name: {isabelle, lp}} for a judge agent
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit  # noqa: E402

REPO = Path(__file__).resolve().parent.parent

# Readability: rewrite the Isabelle \<...> escapes to the glyphs the .lp uses.
GLYPH = {
    r"\<in>": "∈", r"\<notin>": "∉", r"\<subseteq>": "⊆", r"\<subset>": "⊂",
    r"\<Longrightarrow>": "⟹", r"\<Rightarrow>": "⇒", r"\<longrightarrow>": "⟶",
    r"\<forall>": "∀", r"\<exists>": "∃", r"\<and>": "∧", r"\<or>": "∨",
    r"\<not>": "¬", r"\<le>": "≤", r"\<ge>": "≥", r"\<noteq>": "≠",
    r"\<equiv>": "≡", r"\<longleftrightarrow>": "⟷", r"\<lbrakk>": "⟦",
    r"\<rbrakk>": "⟧", r"\<union>": "∪", r"\<inter>": "∩", r"\<times>": "×",
    r"\<langle>": "⟨", r"\<rangle>": "⟩", r"\<Union>": "⋃", r"\<Inter>": "⋂",
    r"\<circ>": "∘", r"\<mapsto>": "↦", r"\<lambda>": "λ", r"\<emptyset>": "∅",
    r"\<open>": "", r"\<close>": "", r"\<comment>": "#",
}
PROOF_KW = re.compile(r"^\s*(apply|by |by\(|done|proof|unfolding|using|supply|"
                      r"declare|sorry|oops|\.\.|\.$)")
TOP_KW = re.compile(r"^\s*(lemma|lemmas|theorem|corollary|definition|abbreviation|"
                    r"section|subsection|subsubsection|text|context|instance|"
                    r"end|begin)\b")


def deglyph(s: str) -> str:
    for k, v in GLYPH.items():
        s = s.replace(k, v)
    return re.sub(r"\s+", " ", s).strip()


def thy_statements(path: Path):
    """{name: isabelle-statement-text} for definitions/lemmas/theorems."""
    text = audit.strip_comments(path.read_text(errors="replace"))
    lines = text.splitlines()
    kw = re.compile(r"^\s*(definition|abbreviation|lemma|theorem|corollary)\b(.*)")
    out, i, n = {}, 0, len(lines)
    while i < n:
        m = kw.match(lines[i])
        if not m:
            i += 1
            continue
        name = audit._first_name(m.group(2).lstrip())
        j = i + 1
        if not name:  # name may be on a following line (definition ... \n name ::)
            while j < n and not lines[j].strip():
                j += 1
            if j < n:
                name = audit._first_name(lines[j].strip())
        # gather the statement span up to the proof / next top-level command
        span, k = [m.group(2)], j
        while k < n and not PROOF_KW.match(lines[k]) and not (k > i and TOP_KW.match(lines[k])):
            span.append(lines[k])
            k += 1
        quoted = re.findall(r'"((?:[^"\\]|\\.)*)"', "\n".join(span), re.S)
        stmt = deglyph(" ⟶ ".join(quoted) if len(quoted) > 1 else (quoted[0] if quoted else ""))
        if name and name not in out:
            out[name] = stmt
        i = max(k, i + 1)
    return out


def lp_statements(path: Path):
    """{name: 'params : type'} — the head of each symbol up to ≔ / ; ."""
    text = path.read_text(errors="replace")
    out = {}
    # match `…symbol NAME …head… (≔|;)` allowing multiline heads
    sym = re.compile(
        r"^(?:private |protected |opaque |sequential |injective |constant |"
        r"associative |commutative )*symbol\s+(\S+)(.*?)(?:≔|;)",
        re.S | re.M)
    for m in sym.finditer(text):
        name, head = m.group(1), re.sub(r"\s+", " ", m.group(2)).strip()
        if name not in out:
            out[name] = head
    return out


def pair(module: str):
    thy = audit.ISA / f"{audit.LP_TO_THY.get(module, module)}.thy"
    lp = REPO / f"{module}.lp"
    tst = thy_statements(thy) if thy.exists() else {}
    lst = lp_statements(lp) if lp.exists() else {}
    rows = {}
    for name in sorted(set(tst) | set(lst)):
        rows[name] = {"isabelle": tst.get(name), "lp": lst.get(name)}
    return rows


def suspicious(name, r):
    """Heuristic flag: present one side only, or an Ord/premise asymmetry worth a look."""
    if r["isabelle"] is None or r["lp"] is None:
        return True
    i, l = r["isabelle"], r["lp"]
    # crude premise-count asymmetry: Isabelle ⟹/⟦⟧ vs lp → arrows
    ihyp = i.count("⟹") + (i.count("⟦") and i.count(";") + 1 or 0)
    lhyp = l.count("→")
    if "Ord" in l and "Ord" not in i:
        return True
    if ihyp and lhyp and abs(ihyp - lhyp) >= 2:
        return True
    return False


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print("usage: fidelity.py <Module> [--diff|--only NAME|--json]")
        return
    module = args[0]
    only = None
    if "--only" in sys.argv:
        only = sys.argv[sys.argv.index("--only") + 1]
    rows = pair(module)
    if only:
        rows = {only: rows.get(only, {"isabelle": None, "lp": None})}
    if "--diff" in sys.argv:
        rows = {n: r for n, r in rows.items() if suspicious(n, r)}
    if "--json" in sys.argv:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
        return
    print(f"=== {module}: {len(rows)} statement(s) "
          + ("(suspicious only)" if "--diff" in sys.argv else "") + " ===")
    for name, r in rows.items():
        flag = "  ⚠" if suspicious(name, r) else ""
        print(f"\n▸ {name}{flag}")
        print(f"  ISA: {r['isabelle'] if r['isabelle'] is not None else '(no source lemma)'}")
        print(f"  LP : {r['lp'] if r['lp'] is not None else '(NOT PORTED)'}")


if __name__ == "__main__":
    main()
