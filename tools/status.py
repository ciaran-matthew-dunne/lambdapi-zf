#!/usr/bin/env python3
"""status.py — the porting loop's single source of truth.

`audit.py` answers "is every statement PRESENT?" (static, name-based). This tool
answers the three questions an autonomous porting loop must re-ask every
iteration:

  1. IS THE PORT ACTUALLY GREEN?   — a real clean build of the port modules
     (scratch/experimental files in .check-exclude are excluded so a broken
     experiment can never mask the port's state).
  2. WHAT REMAINS TO PROVE?        — every `admit` shows up in the plain-text
     build as `axiom _axNNN: <full statement> [file:line:col]`. We harvest that:
     it is a precise, statement-level worklist, for free, straight from lambdapi.
  3. DID I CHEAT OR REGRESS?       — gates: build red, forbidden flags
     (--no-sr-check et al.), a previously-PROVED lemma reverting to `admit`, or a
     new bare-axiom `symbol` declaration sneaking in. (Adding fresh admits is NOT
     a regression — that is Stage-1 skeletoning; only losing a proof is.)

It then prints the NEXT ACTION (fix the build / prove a specific admit / port a
ready module) so the loop always has an unambiguous move.

Usage:
  tools/status.py                 # dashboard (runs a clean build; ~3s)
  tools/status.py --json          # machine-readable, for the loop driver
  tools/status.py --next          # just the single next-action line
  tools/status.py --axioms [Mod]  # dump the admit worklist (all, or one module)
  tools/status.py --gate          # exit non-zero if any anti-cheat gate fails
  tools/status.py --save-baseline # record current admits + bare-axioms as the
                                   # regression baseline (do this after a commit)

Exit status: 0 normally; with --gate, non-zero iff a gate failed.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit  # noqa: E402  (sibling module: completeness/name logic)

REPO = Path(__file__).resolve().parent.parent
BASELINE = REPO / "tools" / "port_baseline.json"
ANSI = re.compile(r"\x1b\[[0-9;]*m")

# Isabelle theories that are foundational / represented by Stdlib+ZF_Base, so an
# un-ported theory importing only these (plus ported modules) is ready to port.
GIVEN_THYS = {"ZF", "FOL", "IFOL", "Main", "Pure"}

LOC_RE = re.compile(r"^\[(?P<path>[^\]:]+\.lp):(?P<line>\d+):[\d-]+\]\s*(?P<msg>.*)$")
AX_RE = re.compile(r"^axiom (_ax\d+):\s*(.*)$")
CMD_START = re.compile(
    r"^\s*(?:private |protected |opaque |sequential |injective |constant |"
    r"associative |commutative )*"
    r"(symbol|inductive|rule|notation|builtin|require|open|unif_rule|"
    r"coercion|debug|flag|prover)\b")
SYM_NAME = re.compile(
    r"^\s*(?:private |protected |opaque |sequential |injective |constant |"
    r"associative |commutative )*symbol\s+(\S+)")


def port_modules():
    """Root *.lp basenames that constitute the port (scratch files excluded)."""
    excl = set()
    f = REPO / ".check-exclude"
    if f.exists():
        for ln in f.read_text().splitlines():
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                excl.add(ln)
    files = sorted(p.name for p in REPO.glob("*.lp") if p.name not in excl)
    return files, sorted(excl)


def run_build():
    """Clean-build the port; return (ok, axioms, errors, warnings, seconds).

    ALWAYS cold (removes .lpo first): lambdapi only emits the `axiom _axNNN`
    lines while actually type-checking a file — a cached .lpo is loaded silently,
    so a warm build would report zero admits and fool the anti-cheat gates. Cold
    is ~3s, which is the whole premise (the loop can afford truth every step)."""
    files, _ = port_modules()
    for lpo in REPO.glob("*.lpo"):
        lpo.unlink()
    cmd = ["lambdapi", "check", "-c", "--too-long=10", *files]
    import time
    t0 = time.monotonic()
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    dt = time.monotonic() - t0
    lines = ANSI.sub("", r.stdout + "\n" + r.stderr).splitlines()
    axioms, errors, warnings, last_loc = [], [], 0, None
    for ln in lines:
        ln = ln.rstrip()
        m = LOC_RE.match(ln)
        if m:
            last_loc = (Path(m.group("path")).name, int(m.group("line")))
            if m.group("msg"):  # a diagnostic with a message on the loc line
                errors.append({"file": last_loc[0], "line": last_loc[1],
                               "msg": m.group("msg")})
            continue
        a = AX_RE.match(ln)
        if a and last_loc:
            axioms.append({"file": last_loc[0], "line": last_loc[1],
                           "name": a.group(1), "stmt": a.group(2)})
            continue
        if "critical pair" in ln or "not confluent" in ln or "cannot be" in ln:
            warnings += 1
    return (r.returncode == 0, axioms, errors, warnings, dt)


def bare_axioms(path: Path):
    """Names of `symbol f : T;` declarations with no `≔` and no proof (`begin`).

    These are logical axioms (undefined constants). The ZF primitives are the
    only legitimate ones; a NEW one is how a cheating proof would smuggle in an
    assumption. Command-block scan: from a `symbol` line, whichever of `≔` /
    `begin` / `;` appears first decides def / proof / axiom."""
    out = []
    lines = path.read_text(errors="replace").splitlines()
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
                verdict = "axiom"
                break
            j += 1
        if verdict == "axiom":
            out.append(name)
        i = j + 1
    return out


def all_bare_axioms():
    files, _ = port_modules()
    return {f: bare_axioms(REPO / f) for f in files}


def proved_symbols(path: Path):
    """Names of lemmas carrying a real (non-admitted) proof — the work that must
    never silently revert to `admit`. A symbol is 'proved' iff it opens a
    `begin … end` whose body contains no `admit` tactic. (Skeleton stubs, which
    ARE `begin admit end`, are deliberately excluded, so adding them never trips
    the regression gate — Stage 1 grows admits on purpose.)"""
    lines = path.read_text(errors="replace").splitlines()
    out, i, n = set(), 0, len(lines)
    while i < n:
        sm = SYM_NAME.match(lines[i])
        if not sm:
            i += 1
            continue
        name, j, opened = sm.group(1), i, False
        while j < n:  # does a proof open (`begin`) before the command ends (`;`)?
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
        if not re.search(r"(?m)^\s*admit\b", "\n".join(body)):
            out.add(name)
        i = k + 1
    return out


def all_proved():
    files, _ = port_modules()
    return {f[:-3]: sorted(proved_symbols(REPO / f)) for f in files}


def ready_to_port():
    """Un-ported theories whose imports are all ported or foundational."""
    ported_thys = {audit.LP_TO_THY.get(m, m) for m in audit.ported_modules()}
    available = ported_thys | GIVEN_THYS
    out = []
    for thy in sorted(audit.ISA.glob("*.thy")):
        if thy.stem in ported_thys:
            continue
        text = audit.strip_comments(thy.read_text(errors="replace"))
        m = re.search(r"\bimports\b(.+?)\bbegin\b", text, re.S)
        if not m:
            continue
        imps = re.findall(r"[A-Za-z][A-Za-z0-9_']*", m.group(1))
        missing = [x for x in imps if x not in available]
        if not missing:
            out.append(thy.stem)
    return out


def completeness():
    rows = []
    for m in audit.ported_modules():
        r = audit.audit_module(m)
        if r:
            rows.append({"module": m, "present": len(r["present"]),
                         "total": r["total"], "missing": len(r["genuine"]),
                         "missing_names": [n for n, _ in r["genuine"]]})
    return rows


def gate_checks(admits_by_mod, bare):
    """Return (list of gate results). Each: (name, ok, detail)."""
    res = []
    # 1. forbidden flags anywhere in sources / build script / hooks
    hits = []
    for p in list(REPO.glob("*.lp")) + [REPO / "check.sh"]:
        if not p.exists():
            continue
        for k, ln in enumerate(p.read_text(errors="replace").splitlines(), 1):
            if re.search(r"no-sr-check|--no-[a-z]", ln):
                hits.append(f"{p.name}:{k}")
    res.append(("no-forbidden-flags", not hits, ", ".join(hits) or "clean"))
    # 2/3. regression vs baseline: a PROVED lemma must not revert to admit/vanish
    # (adding new admits is fine — that is Stage-1 skeletoning), and no new bare
    # axioms may appear.
    if BASELINE.exists():
        base = json.loads(BASELINE.read_text())
        now_proved = all_proved()
        reverted = []
        for m, names in base.get("proved", {}).items():
            lost = set(names) - set(now_proved.get(m, []))
            reverted += [f"{m}:{x}" for x in sorted(lost)]
        res.append(("no-proof-reverted", not reverted, ", ".join(reverted) or "ok"))
        base_bare = {m: set(v) for m, v in base.get("bare_axioms", {}).items()}
        new_ax = []
        for m, names in bare.items():
            extra = set(names) - base_bare.get(m, set())
            new_ax += [f"{m}:{x}" for x in sorted(extra)]
        res.append(("no-new-axioms", not new_ax, ", ".join(new_ax) or "ok"))
    else:
        res.append(("baseline", False, "no baseline saved (run --save-baseline)"))
    return res


def gather():
    ok, axioms, errors, warnings, dt = run_build()
    files, scratch = port_modules()
    admits_by_mod = {}
    for a in axioms:
        admits_by_mod[a["file"].replace(".lp", "")] = \
            admits_by_mod.get(a["file"].replace(".lp", ""), 0) + 1
    bare = all_bare_axioms()
    comp = completeness()
    gates = gate_checks(admits_by_mod, bare)
    nxt = next_action(ok, errors, axioms, admits_by_mod, comp)
    return {"build_ok": ok, "seconds": round(dt, 2), "n_modules": len(files),
            "warnings": warnings, "errors": errors, "axioms": axioms,
            "admits_by_mod": admits_by_mod, "total_admits": len(axioms),
            "completeness": comp, "scratch": scratch,
            "ready_to_port": ready_to_port(),
            "gates": [{"name": n, "ok": o, "detail": d} for n, o, d in gates],
            "next": nxt}


def next_action(ok, errors, axioms, admits_by_mod, comp):
    if not ok:
        e = errors[0] if errors else {"file": "?", "line": "?", "msg": "build failed"}
        return f"FIX BUILD — {e['file']}:{e['line']}  {e['msg']}"
    # STAGE 1 — completeness (every statement PRESENT; proofs deferred to admit).
    # 1a: skeleton the next ready un-ported module (the loop's first stage).
    rdy = ready_to_port()
    if rdy:
        return (f"SKELETON NEW MODULE — {rdy[0]}  (create {rdy[0]}.lp: each def with "
                f"a faithful body, each lemma as `… ≔ begin admit end`, build green).\n"
                f"    ready now: {', '.join(rdy)}")
    # 1b: fill remaining missing statements in existing frontier modules.
    gaps = [c for c in comp if c["missing"] > 0 and admits_by_mod.get(c["module"])]
    if gaps:
        g = min(gaps, key=lambda c: c["missing"])
        return (f"PORT MISSING STATEMENT into {g['module']}.lp — {g['missing_names'][0]} "
                f"({g['missing']} missing; add as `begin admit end`)")
    # STAGE 2 — prove the admits, finishing the module closest to done first.
    if admits_by_mod:
        mod = min(admits_by_mod, key=admits_by_mod.get)
        first = min((a for a in axioms if a["file"] == mod + ".lp"),
                    key=lambda a: a["line"])
        return (f"PROVE ADMIT — {mod}.lp:{first['line']}  "
                f"({admits_by_mod[mod]} left in {mod})\n    {first['stmt']}")
    return "DONE — no admits, no gaps, build green."


def save_baseline():
    ok, axioms, *_ = run_build()
    admits = {}
    for a in axioms:
        k = a["file"].replace(".lp", "")
        admits[k] = admits.get(k, 0) + 1
    proved = all_proved()
    BASELINE.write_text(json.dumps(
        {"admits": admits, "proved": proved,
         "bare_axioms": all_bare_axioms()}, indent=2))
    n_proved = sum(len(v) for v in proved.values())
    print(f"baseline saved: {sum(admits.values())} admits, {n_proved} proved "
          f"lemmas protected → {BASELINE.relative_to(REPO)}")


def fmt_dashboard(s):
    out = []
    build = "✓ GREEN" if s["build_ok"] else "✗ RED"
    warn = f"  ⚠ {s['warnings']} warnings" if s["warnings"] else ""
    out.append(f"BUILD  {build}   {s['n_modules']} port modules, "
               f"{s['seconds']}s clean{warn}")
    if not s["build_ok"]:
        for e in s["errors"][:5]:
            out.append(f"   ✗ {e['file']}:{e['line']}  {e['msg']}")
    if s["scratch"]:
        out.append(f"       (scratch excluded: {', '.join(s['scratch'])})")
    out.append("")
    tot = s["total_admits"]
    by = "  ".join(f"{m} {n}" for m, n in
                   sorted(s["admits_by_mod"].items(), key=lambda kv: -kv[1]))
    out.append(f"ADMITS {tot} to prove   {by}")
    # Only frontier modules (those with admits) — base-file "missing" counts are
    # Isabelle simp-noise the port deliberately skips (see CLAUDE.md §4).
    gaps = [c for c in s["completeness"]
            if c["missing"] > 0 and s["admits_by_mod"].get(c["module"])]
    if gaps:
        gs = "  ".join(f"{c['module']} {c['present']}/{c['total']}(-{c['missing']})"
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


def main():
    argv = sys.argv[1:]
    if "--save-baseline" in argv:
        save_baseline()
        return
    if "--axioms" in argv:
        i = argv.index("--axioms")
        mod = argv[i + 1] if i + 1 < len(argv) and not argv[i+1].startswith("-") else None
        _, ax, *_ = run_build()
        for a in ax:
            if mod and a["file"].replace(".lp", "") != mod:
                continue
            print(f"{a['file']}:{a['line']}  {a['name']}\n    {a['stmt']}")
        return
    s = gather()
    if "--json" in argv:
        print(json.dumps(s, indent=2))
    elif "--next" in argv:
        print(s["next"])
    else:
        print(fmt_dashboard(s))
    if "--gate" in argv:
        failed = [g for g in s["gates"] if not g["ok"]] + \
                 ([{"name": "build"}] if not s["build_ok"] else [])
        sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
