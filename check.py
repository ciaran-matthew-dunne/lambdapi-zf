#!/usr/bin/env python3
"""check.py — the single feedback tool for the lambdapi-zf port.

One script, one loop: build → worklist → gates → NEXT action.

  ./check.py                  dashboard: cold build of the whole port, admit
                              worklist, completeness gaps, repo hygiene,
                              anti-cheat gates, NEXT action
  ./check.py Foo.lp [...]     fast targeted type-check (warm, writes .lpo)
  ./check.py --gate           dashboard + exit non-zero iff build red or any
                              gate fails — run this BEFORE every commit
  ./check.py --next           just the next-action line
  ./check.py --json           dashboard, machine-readable
  ./check.py --admits [Mod]   the admit worklist as full statements
  ./check.py --missing [Mod]  completeness detail vs isabelle-src (missing,
                              possible renames, skipped simp-noise)
  ./check.py --fidelity Mod [--only NAME] [--diff]
                              Isabelle statement vs .lp statement side by side
                              (--diff: only suspicious pairs; --json works too)

Design notes
------------
* The dashboard build is ALWAYS COLD (every .lpo removed first): lambdapi only
  prints the `axiom _axNNN: <statement>` lines for `admit`s while actually
  type-checking a file, so a warm cache would hide both admits and breakage.
  A full cold build is ~4s — the loop can afford the truth every step.
* Anti-cheat gates compare the working tree against **git HEAD** — no state
  file to save, forget, or tamper with. A lemma proved in HEAD must not revert
  to `admit` or vanish; no new bare `π`-axiom may appear; no forbidden
  type-checker flags anywhere. Gate BEFORE committing and a regression can
  never be committed silently.
* Scratch/experimental .lp files listed in .check-exclude are not part of the
  port: they are neither built nor gated, so a broken experiment can never
  mask the port's state. (The gates read HEAD's .check-exclude, so *newly*
  excluding a file does not silently drop its protections.)
* The lambdapi binary here is a moving dev target; this script relies only on
  stable CLI surface (`check`, `-c`, `--too-long`, `--no-colors`).
"""
import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent
ISA = REPO / "isabelle-src"
ANSI = re.compile(r"\x1b\[[0-9;]*m")

# lp module -> Isabelle theory name (default: identical). A module with no
# matching .thy (local glue like OrdLeast) is simply skipped for completeness.
LP_TO_THY = {"Bool_ZF": "Bool", "Nat_ZF": "Nat"}

# Theories represented by Stdlib+ZF_Base: an un-ported theory importing only
# these (plus ported modules) is ready to port.
GIVEN_THYS = {"ZF", "FOL", "IFOL", "Main", "Pure"}

# Isabelle automation/plumbing names not worth porting as standalone results.
SKIP_RE = re.compile(r"(^atomize_)|(_simps?$)|(_simps[12]$)|(^setup)|(_cong_simp$)")

NAME = r"[A-Za-z][A-Za-z0-9_']*"
SYM_NAME = re.compile(
    r"^\s*(?:private |protected |opaque |sequential |injective |constant |"
    r"associative |commutative )*symbol\s+(\S+)")
LOC_RE = re.compile(r"^\[(?P<path>[^\]]*?\.lp):(?P<line>\d+):[\d:-]+\]\s*(?P<msg>.*)$")
AX_RE = re.compile(r"^axiom (_ax\d+):\s*(.*)$")
STRUCT_RE = re.compile(r"^(Start|End) checking ")


# ---------------------------------------------------------------------------
# repo plumbing
# ---------------------------------------------------------------------------

def git(*args):
    r = subprocess.run(["git", "-C", str(REPO), *args],
                       capture_output=True, text=True)
    return r.returncode, r.stdout


def parse_exclude(text):
    out = set()
    for ln in (text or "").splitlines():
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            out.add(ln)
    return out


def port_modules():
    """Root *.lp basenames constituting the port (scratch files excluded)."""
    f = REPO / ".check-exclude"
    excl = parse_exclude(f.read_text() if f.exists() else "")
    files = sorted(p.name for p in REPO.glob("*.lp") if p.name not in excl)
    return files, sorted(excl)


def head_text(name):
    """Contents of `name` at git HEAD, or None if absent/no HEAD."""
    rc, out = git("show", f"HEAD:{name}")
    return out if rc == 0 else None


def head_lp_files():
    rc, out = git("ls-tree", "--name-only", "HEAD")
    if rc != 0:
        return []
    return [n for n in out.splitlines() if n.endswith(".lp")]


# ---------------------------------------------------------------------------
# building
# ---------------------------------------------------------------------------

def run_cold_build():
    """Cold-build the port; return (ok, axioms, errors, warnings, seconds).

    Cold because lambdapi silently loads a cached .lpo — a warm build reports
    zero admits and can show a stale green."""
    files, _ = port_modules()
    for lpo in REPO.glob("*.lpo"):
        lpo.unlink()
    t0 = time.monotonic()
    r = subprocess.run(["lambdapi", "check", "-c", "--no-colors",
                        "--too-long=10", *files],
                       cwd=REPO, capture_output=True, text=True)
    dt = time.monotonic() - t0
    lines = [ANSI.sub("", ln).rstrip()
             for ln in (r.stdout + "\n" + r.stderr).splitlines()]
    axioms, errors, warnings, last_loc, cur = [], [], [], None, None

    def close(block):
        if block and block["msg"].strip():
            if block["msg"].lower().startswith("warning"):
                warnings.append(block)
            else:
                errors.append(block)

    for ln in lines:
        if STRUCT_RE.match(ln):
            close(cur)
            cur = None
            continue
        m = LOC_RE.match(ln)
        if m:
            close(cur)
            last_loc = (Path(m["path"]).name, int(m["line"]))
            cur = {"file": last_loc[0], "line": last_loc[1],
                   "msg": m["msg"].strip()}
            continue
        a = AX_RE.match(ln)
        if a:
            close(cur)
            cur = None
            if last_loc:
                axioms.append({"file": last_loc[0], "line": last_loc[1],
                               "name": a.group(1), "stmt": a.group(2)})
            continue
        if cur is not None and ln.strip():
            cur["msg"] = (cur["msg"] + " " + ln.strip()).strip()
    close(cur)
    return r.returncode == 0, axioms, errors, len(warnings), dt


def check_files(files):
    """Targeted `lambdapi check -c` on specific files, streaming output."""
    r = subprocess.run(["lambdapi", "check", "-c", "--too-long=10", *files],
                       cwd=REPO)
    if r.returncode == 0:
        print("OK: type-checked successfully.")
    return r.returncode


# ---------------------------------------------------------------------------
# .lp analysis (works on TEXT so the same code audits HEAD and working tree)
# ---------------------------------------------------------------------------

def lp_symbols(text):
    syms = set()
    for ln in text.splitlines():
        m = SYM_NAME.match(ln)
        if m:
            syms.add(m.group(1))
    return syms


def proved_symbols(text):
    """Names carrying a real (non-admitted) proof — work that must never
    silently revert. A symbol is proved iff it opens `begin … end` whose body
    has no `admit` tactic (skeleton stubs are thus excluded on purpose)."""
    lines = text.splitlines()
    out, i, n = set(), 0, len(lines)
    while i < n:
        sm = SYM_NAME.match(lines[i])
        if not sm:
            i += 1
            continue
        name, j, opened = sm.group(1), i, False
        while j < n:  # does `begin` open before the command ends (`;`)?
            b, s = lines[j].find("begin"), lines[j].find(";")
            if b != -1 and (s == -1 or b < s):
                opened = True
                break
            if s != -1:
                break
            j += 1
        if not opened:
            i = j + 1
            continue
        body, k = [], j
        while k < n:
            body.append(lines[k])
            if re.search(r"\bend\s*;", lines[k]):
                break
            k += 1
        # comments stripped first, so an `admit` anywhere in real proof text
        # counts (a line-anchored match would miss `begin admit end;`)
        text = re.sub(r"//[^\n]*", "", "\n".join(body))
        text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
        if not re.search(r"\badmit\b", text):
            out.add(name)
        i = k + 1
    return out


def _is_defining_axiom(name, decl):
    """True iff `decl` is a conservative definitional extension: an axiom
    named X_def whose statement is `π (X p₁ … pₙ = RHS)` where p₁…pₙ are
    exactly its Π-bound parameters, in order. Such an axiom only fixes the
    meaning of the fresh constant X — it cannot assert anything else."""
    base = name[: -len("_def")]
    rest = re.sub(r"^.*?symbol\s+\S+\s*", "", decl, count=1, flags=re.S)
    params = []
    while True:  # consume flat (p … : T) groups; implicit/nested → not ours
        pm = re.match(r"\(([^()]*)\)\s*", rest)
        if not pm:
            break
        grp = pm.group(1)
        if ":" not in grp:
            return False
        params.extend(grp.split(":", 1)[0].split())
        rest = rest[pm.end():]
    if not rest.startswith(":"):
        return False
    lhs = re.match(r"\s*π\s*\(\s*" + re.escape(base) + r"((?:\s+[\w']+)*)\s*=",
                   rest[1:])
    return bool(lhs) and lhs.group(1).split() == params


def _scan_axioms(text):
    """(genuine, defax): bare `symbol f : π …;` axiom names, split into
    genuine LOGICAL axioms (the cheat vector) and shape-checked `X_def`
    defining axioms (Isabelle `definition` twins — conservative extensions).
    `*_eq` definition equations count as neither."""
    genuine, defax = [], []
    lines = text.splitlines()
    i, n = 0, len(lines)
    while i < n:
        sm = SYM_NAME.match(lines[i])
        if not sm:
            i += 1
            continue
        name, j, verdict = sm.group(1), i, "axiom"
        while j < n:
            seg = lines[j]
            if "≔" in seg or "begin" in seg:
                verdict = "def"
                break
            if ";" in seg:
                break
            j += 1
        if verdict == "axiom":
            decl = " ".join(lines[i:j + 1])
            if "π" in decl:
                if name.endswith("_def") and _is_defining_axiom(name, decl):
                    defax.append(name)
                elif not name.endswith("_eq"):
                    genuine.append(name)
        i = j + 1
    return genuine, defax


def bare_axioms(text):
    return _scan_axioms(text)[0]


# ---------------------------------------------------------------------------
# Isabelle-side analysis (completeness + fidelity)
# ---------------------------------------------------------------------------

def strip_comments(text):
    """Remove Isabelle (* … *) comments. They NEST (IntDiv.thy wraps a whole
    legacy block, itself containing comments, in one (* … *)), so a regex
    would leak the tail of the outer comment back in as 'code'. Newlines
    inside comments are kept so line structure survives."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        else:
            if not depth or text[i] == "\n":
                out.append(text[i])
            i += 1
    return "".join(out)


def _first_name(rest):
    """Leading (possibly quoted) Isabelle identifier, else None."""
    rest = rest.lstrip()
    mq = re.match(r'"(' + NAME + r')"', rest)
    if mq:
        return mq.group(1)
    if rest.startswith('"'):
        return None  # anonymous statement
    mi = re.match(r"(" + NAME + r")", rest)
    return mi.group(1) if mi else None


def thy_names(path):
    """Declared definition/lemma/theorem names in a .thy."""
    lines = strip_comments(path.read_text(errors="replace")).splitlines()
    names = set()
    kw_re = re.compile(r"^\s*(definition|abbreviation|lemma|lemmas|theorem|"
                       r"corollary)\b(.*)")
    for i, line in enumerate(lines):
        m = kw_re.match(line)
        if not m:
            continue
        nm = _first_name(m.group(2))
        if not nm and m.group(1) in ("definition", "abbreviation"):
            for j in range(i + 1, min(i + 4, len(lines))):
                if lines[j].strip():
                    nm = _first_name(lines[j].strip())
                    break
        if nm:
            names.add(nm)
    return names


def _strip_brackets(s):
    """Drop Isabelle attribute brackets [ … ] (they nest: [THEN x [THEN y]])."""
    out, depth = [], 0
    for ch in s:
        if ch == "[":
            depth += 1
        elif ch == "]":
            if depth:
                depth -= 1
        elif not depth:
            out.append(ch)
    return "".join(out)


def thy_bundles(path):
    """Names of `lemmas` declarations whose RHS lists ≥2 facts — pure
    hint-list bundles (simp/intro bags like div_rls, int_typechecks) with no
    single statement to port; each member fact is audited on its own. A
    single-fact `lemmas foo = bar [THEN baz]` is NOT a bundle — it is a
    genuine derived statement and stays on the worklist."""
    lines = strip_comments(path.read_text(errors="replace")).splitlines()
    out, i, n = set(), 0, len(lines)
    kw = re.compile(r"^\s*lemmas\b(.*)")
    while i < n:
        m = kw.match(lines[i])
        if not m:
            i += 1
            continue
        span, j = [m.group(1)], i + 1
        while j < n and not TOP_KW.match(lines[j]) \
                and not PROOF_KW.match(lines[j]):
            span.append(lines[j])
            j += 1
        parts = _strip_brackets(" ".join(span)).split("=", 1)
        if len(parts) == 2:
            name = _first_name(parts[0])
            if name and len(re.findall(NAME, parts[1])) >= 2:
                out.add(name)
        i = max(j, i + 1)
    return out


def rename_hint(missing, targets):
    """Best candidate .lp symbol `missing` might have been renamed to.
    A target must contain (or be contained in) the missing name with ≥50%
    length overlap — and must not itself be a source statement name, else
    every `foo_*` lemma 'renames' to the `foo` definition."""
    best, best_ratio = None, 0.0
    for s in targets:
        if missing != s and (missing in s or s in missing):
            ratio = min(len(missing), len(s)) / max(len(missing), len(s))
            if ratio >= 0.5 and ratio > best_ratio:
                best, best_ratio = s, ratio
    return best


def ported_modules():
    """Port modules that have a matching Isabelle theory to audit against."""
    files, _ = port_modules()
    out = []
    for f in files:
        mod = f[:-3]
        if (ISA / f"{LP_TO_THY.get(mod, mod)}.thy").exists():
            out.append(mod)
    return out


def audit_module(mod):
    thy = ISA / f"{LP_TO_THY.get(mod, mod)}.thy"
    lp = REPO / f"{mod}.lp"
    if not thy.exists() or not lp.exists():
        return None
    src = thy_names(thy)
    bundles = thy_bundles(thy)
    syms = lp_symbols(lp.read_text(errors="replace"))
    targets = syms - src  # a symbol that IS a source name can't be a rename
    present, genuine, skip, renamed = [], [], [], []
    for n in sorted(src):
        if n in syms:
            present.append(n)
        elif SKIP_RE.search(n) or n in bundles:
            skip.append(n)
        else:
            hint = rename_hint(n, targets)
            (renamed if hint else genuine).append((n, hint))
    return {"module": mod, "thy": thy.stem, "total": len(src),
            "present": present, "genuine": genuine, "skip": skip,
            "renamed": renamed}


def completeness():
    return [r for r in (audit_module(m) for m in ported_modules()) if r]


def ready_to_port():
    """Un-ported theories whose imports are all ported or foundational."""
    ported_thys = {LP_TO_THY.get(m, m) for m in ported_modules()}
    available = ported_thys | GIVEN_THYS
    out = []
    for thy in sorted(ISA.glob("*.thy")):
        if thy.stem in ported_thys:
            continue
        m = re.search(r"\bimports\b(.+?)\bbegin\b",
                      strip_comments(thy.read_text(errors="replace")), re.S)
        if not m:
            continue
        imps = re.findall(NAME, m.group(1))
        if all(x in available for x in imps):
            out.append(thy.stem)
    return out


# --- fidelity ---------------------------------------------------------------

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
TOP_KW = re.compile(r"^\s*(lemma|lemmas|theorem|corollary|definition|"
                    r"abbreviation|section|subsection|subsubsection|text|"
                    r"context|instance|end|begin)\b")


def deglyph(s):
    for k, v in GLYPH.items():
        s = s.replace(k, v)
    return re.sub(r"\s+", " ", s).strip()


def thy_statements(path):
    """{name: isabelle-statement-text} for definitions/lemmas/theorems."""
    lines = strip_comments(path.read_text(errors="replace")).splitlines()
    kw = re.compile(r"^\s*(definition|abbreviation|lemma|theorem|corollary)"
                    r"\b(.*)")
    out, i, n = {}, 0, len(lines)
    while i < n:
        m = kw.match(lines[i])
        if not m:
            i += 1
            continue
        name = _first_name(m.group(2).lstrip())
        j = i + 1
        if not name:  # name may sit on a following line
            while j < n and not lines[j].strip():
                j += 1
            if j < n:
                name = _first_name(lines[j].strip())
        span, k = [m.group(2)], j
        while k < n and not PROOF_KW.match(lines[k]) \
                and not (k > i and TOP_KW.match(lines[k])):
            span.append(lines[k])
            k += 1
        quoted = re.findall(r'"((?:[^"\\]|\\.)*)"', "\n".join(span), re.S)
        stmt = deglyph(" ⟶ ".join(quoted) if len(quoted) > 1
                       else (quoted[0] if quoted else ""))
        if name and name not in out:
            out[name] = stmt
        i = max(k, i + 1)
    return out


def lp_statements(text):
    """{name: 'params : type'} — the head of each symbol up to ≔ / ; ."""
    out = {}
    sym = re.compile(
        r"^(?:private |protected |opaque |sequential |injective |constant |"
        r"associative |commutative )*symbol\s+(\S+)(.*?)(?:≔|;)",
        re.S | re.M)
    for m in sym.finditer(text):
        name, head = m.group(1), re.sub(r"\s+", " ", m.group(2)).strip()
        if name not in out:
            out[name] = head
    return out


def fidelity_pairs(module):
    thy = ISA / f"{LP_TO_THY.get(module, module)}.thy"
    lp = REPO / f"{module}.lp"
    tst = thy_statements(thy) if thy.exists() else {}
    lst = lp_statements(lp.read_text(errors="replace")) if lp.exists() else {}
    return {name: {"isabelle": tst.get(name), "lp": lst.get(name)}
            for name in sorted(set(tst) | set(lst))}


def suspicious(r):
    """Heuristic: one side missing, or an Ord/premise asymmetry worth a look."""
    if r["isabelle"] is None or r["lp"] is None:
        return True
    i, l = r["isabelle"], r["lp"]
    if "Ord" in l and "Ord" not in i:
        return True
    ihyp = i.count("⟹") + ((i.count(";") + 1) if i.count("⟦") else 0)
    lhyp = l.count("→")
    return bool(ihyp and lhyp and abs(ihyp - lhyp) >= 2)


# ---------------------------------------------------------------------------
# gates & hygiene
# ---------------------------------------------------------------------------

FORBIDDEN = re.compile(r"no-sr-check")


def gate_checks():
    """Anti-cheat gates, each (name, ok, detail). Floor = git HEAD."""
    res = []
    # 1. forbidden type-checker flags in sources or hooks
    hits = []
    scan = list(REPO.glob("*.lp")) + list((REPO / ".claude" / "hooks").glob("*"))
    for p in scan:
        for k, ln in enumerate(p.read_text(errors="replace").splitlines(), 1):
            if FORBIDDEN.search(ln):
                hits.append(f"{p.name}:{k}")
    res.append(("no-forbidden-flags", not hits, ", ".join(hits) or "clean"))
    # 2/3. vs HEAD: no proved lemma reverts/vanishes; no new bare π-axiom.
    head_files = head_lp_files()
    if not head_files:
        res.append(("vs-HEAD", False, "no git HEAD to compare against"))
        return res
    head_excl = parse_exclude(head_text(".check-exclude") or "")
    wt_files, _ = port_modules()
    gated = sorted((set(head_files) | set(wt_files)) - head_excl)
    reverted, new_ax = [], []
    for f in gated:
        head = head_text(f)
        wt_path = REPO / f
        wt = wt_path.read_text(errors="replace") if wt_path.exists() else ""
        mod = f[:-3]
        if head is not None:
            # A proved `X_def` may become the shape-checked defining AXIOM of
            # its twin constant (definition-encoding migration): the statement
            # stays, only its status changes — not a reverted proof.
            lost = (proved_symbols(head) - proved_symbols(wt)
                    - set(_scan_axioms(wt)[1]))
            reverted += [f"{mod}:{x}" for x in sorted(lost)]
        extra = set(bare_axioms(wt)) - set(bare_axioms(head or ""))
        new_ax += [f"{mod}:{x}" for x in sorted(extra)]
    res.append(("no-proof-reverted", not reverted, ", ".join(reverted) or "ok"))
    res.append(("no-new-axioms", not new_ax, ", ".join(new_ax) or "ok"))
    return res


def repo_state():
    """Branch, unpushed count, and working-tree drift — so the loop can see
    accidental deletions / leftover scratch edits without running git."""
    rc, branch = git("rev-parse", "--abbrev-ref", "HEAD")
    branch = branch.strip() if rc == 0 else "?"
    rc, ahead = git("rev-list", "--count", "@{u}..HEAD")
    unpushed = int(ahead.strip()) if rc == 0 else None
    _, out = git("status", "--porcelain")
    _, excl = port_modules()
    dirty, deleted, untracked = [], [], []
    for ln in out.splitlines():
        st, name = ln[:2], ln[3:]
        if st == "??":
            if name not in excl:
                untracked.append(name)
        elif "D" in st:
            deleted.append(name)
        else:
            dirty.append(name)
    return {"branch": branch, "unpushed": unpushed, "dirty": dirty,
            "deleted": deleted, "untracked": untracked}


# ---------------------------------------------------------------------------
# next action & dashboard
# ---------------------------------------------------------------------------

def next_action(ok, errors, axioms, admits_by_mod, comp):
    if not ok:
        e = errors[0] if errors else {"file": "?", "line": "?",
                                      "msg": "build failed"}
        return f"FIX BUILD — {e['file']}:{e['line']}  {e['msg']}"
    # STAGE 1 — completeness: every statement PRESENT (proofs may be admits).
    rdy = ready_to_port()
    if rdy:
        return (f"SKELETON NEW MODULE — {rdy[0]}  (create {rdy[0]}.lp: each def "
                f"with a faithful body, each lemma as `… ≔ begin admit end`, "
                f"build green).\n    ready now: {', '.join(rdy)}")
    gaps = [c for c in comp
            if c["genuine"] and admits_by_mod.get(c["module"])]
    if gaps:
        g = min(gaps, key=lambda c: len(c["genuine"]))
        return (f"PORT MISSING STATEMENT into {g['module']}.lp — "
                f"{g['genuine'][0][0]} ({len(g['genuine'])} missing; add as "
                f"`begin admit end`)")
    # STAGE 2 — prove the admits, finishing the closest-to-done module first.
    if admits_by_mod:
        mod = min(admits_by_mod, key=admits_by_mod.get)
        first = min((a for a in axioms if a["file"] == mod + ".lp"),
                    key=lambda a: a["line"])
        return (f"PROVE ADMIT — {mod}.lp:{first['line']}  "
                f"({admits_by_mod[mod]} left in {mod})\n    {first['stmt']}")
    return "DONE — no admits, no gaps, build green."


def gather():
    ok, axioms, errors, warnings, dt = run_cold_build()
    files, scratch = port_modules()
    admits_by_mod = {}
    for a in axioms:
        m = a["file"][:-3]
        admits_by_mod[m] = admits_by_mod.get(m, 0) + 1
    comp = completeness()
    gates = gate_checks()
    return {"build_ok": ok, "seconds": round(dt, 2), "n_modules": len(files),
            "warnings": warnings, "errors": errors, "axioms": axioms,
            "admits_by_mod": admits_by_mod, "total_admits": len(axioms),
            "completeness": [
                {"module": c["module"], "present": len(c["present"]),
                 "total": c["total"], "missing": len(c["genuine"]),
                 "missing_names": [n for n, _ in c["genuine"]]}
                for c in comp],
            "scratch": scratch, "repo": repo_state(),
            "ready_to_port": ready_to_port(),
            "gates": [{"name": n, "ok": o, "detail": d} for n, o, d in gates],
            "next": next_action(ok, errors, axioms, admits_by_mod, comp)}


def fmt_dashboard(s):
    out = []
    build = "✓ GREEN" if s["build_ok"] else "✗ RED"
    warn = f"  ⚠ {s['warnings']} warnings" if s["warnings"] else ""
    out.append(f"BUILD  {build}   {s['n_modules']} port modules, "
               f"{s['seconds']}s cold{warn}")
    if not s["build_ok"]:
        for e in s["errors"][:5]:
            out.append(f"   ✗ {e['file']}:{e['line']}  {e['msg']}")
    if s["scratch"]:
        out.append(f"       (scratch excluded: {', '.join(s['scratch'])})")
    r = s["repo"]
    bits = [r["branch"] + (f" +{r['unpushed']} unpushed"
                           if r["unpushed"] else "")]
    if r["dirty"]:
        bits.append("dirty: " + " ".join(r["dirty"]))
    if r["deleted"]:
        bits.append("⚠ deleted: " + " ".join(r["deleted"]))
    if r["untracked"]:
        bits.append("untracked: " + " ".join(r["untracked"]))
    out.append("REPO   " + "  |  ".join(bits))
    out.append("")
    by = "  ".join(f"{m} {n}" for m, n in
                   sorted(s["admits_by_mod"].items(), key=lambda kv: -kv[1]))
    out.append(f"ADMITS {s['total_admits']} to prove   {by}")
    # Frontier gaps only (modules with admits) — base-file "missing" counts are
    # Isabelle simp-noise the port deliberately skips (CLAUDE.md §4).
    gaps = [c for c in s["completeness"]
            if c["missing"] > 0 and s["admits_by_mod"].get(c["module"])]
    if gaps:
        gs = "  ".join(f"{c['module']} {c['present']}/{c['total']}"
                       f"(-{c['missing']})"
                       for c in sorted(gaps, key=lambda c: -c["missing"]))
        out.append(f"GAPS   frontier: {gs}")
    if s["ready_to_port"]:
        out.append(f"READY  un-ported, deps met: {', '.join(s['ready_to_port'])}")
    out.append("")
    for g in s["gates"]:
        out.append(f"GATE   {'✓' if g['ok'] else '✗'} {g['name']}: {g['detail']}")
    out.append("")
    out.append("NEXT   " + s["next"])
    return "\n".join(out)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def cmd_admits(mod, as_json):
    _, axioms, *_ = run_cold_build()
    if mod:
        axioms = [a for a in axioms if a["file"][:-3] == mod]
    if as_json:
        print(json.dumps(axioms, indent=2, ensure_ascii=False))
        return
    for a in axioms:
        print(f"{a['file']}:{a['line']}  {a['name']}\n    {a['stmt']}")


def cmd_missing(mod, as_json):
    mods = [mod] if mod else ported_modules()
    rows = [r for r in (audit_module(m) for m in mods) if r]
    if as_json:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
        return
    for r in rows:
        print(f"\n=== {r['module']} (vs {r['thy']}.thy) — "
              f"{len(r['present'])}/{r['total']} present, "
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
            print("  automation/skip (simp plumbing, lemmas bundles): "
                  + ", ".join(r["skip"]))


def cmd_fidelity(module, only, diff, as_json):
    rows = fidelity_pairs(module)
    if only:
        rows = {only: rows.get(only, {"isabelle": None, "lp": None})}
    if diff:
        rows = {n: r for n, r in rows.items() if suspicious(r)}
    if as_json:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
        return
    print(f"=== {module}: {len(rows)} statement(s)"
          + (" (suspicious only)" if diff else "") + " ===")
    for name, r in rows.items():
        flag = "  ⚠" if suspicious(r) else ""
        print(f"\n▸ {name}{flag}")
        print(f"  ISA: {r['isabelle'] if r['isabelle'] is not None else '(no source lemma)'}")
        print(f"  LP : {r['lp'] if r['lp'] is not None else '(NOT PORTED)'}")


def main():
    p = argparse.ArgumentParser(
        description="lambdapi-zf: build, worklist, anti-cheat gates, next action.")
    p.add_argument("files", nargs="*", metavar="FILE.lp",
                   help="targeted type-check of specific files (warm, writes .lpo)")
    p.add_argument("--gate", action="store_true",
                   help="exit non-zero iff build red or any gate fails")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    p.add_argument("--next", dest="next_only", action="store_true",
                   help="print just the next-action line")
    p.add_argument("--admits", nargs="?", const="", metavar="MOD",
                   help="dump the admit worklist (all modules, or one)")
    p.add_argument("--missing", nargs="?", const="", metavar="MOD",
                   help="completeness detail vs isabelle-src")
    p.add_argument("--fidelity", metavar="MOD",
                   help="Isabelle vs .lp statements, side by side")
    p.add_argument("--only", metavar="NAME", help="with --fidelity: one lemma")
    p.add_argument("--diff", action="store_true",
                   help="with --fidelity: only suspicious pairs")
    args = p.parse_args()

    if args.files:
        sys.exit(check_files(args.files))
    if args.admits is not None:
        cmd_admits(args.admits, args.json)
        return
    if args.missing is not None:
        cmd_missing(args.missing, args.json)
        return
    if args.fidelity:
        cmd_fidelity(args.fidelity, args.only, args.diff, args.json)
        return

    s = gather()
    if args.json:
        print(json.dumps(s, indent=2, ensure_ascii=False))
    elif args.next_only:
        print(s["next"])
    else:
        print(fmt_dashboard(s))
    if args.gate:
        sys.exit(0 if s["build_ok"] and all(g["ok"] for g in s["gates"]) else 1)


if __name__ == "__main__":
    main()
