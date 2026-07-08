#!/usr/bin/env python3
"""PostToolUse hook: type-check an edited Lambdapi (.lp) file and surface its
diagnostics back to the agent.

The lambdapi binary here is a locally-built moving target (we develop lambdapi
itself), so the hook ADAPTS to the CLI it finds: it first tries the rich
interface (`--json --proof-state-on-error`, which renders the goal state a
failing tactic faced); if the binary rejects those options it silently falls
back to a plain-text run and parses `[file:line:col]` diagnostics instead.
When a lambdapi with the rich flags is installed again, the goal-state display
comes back with no hook change.

It runs WITHOUT `-c` (an edit-time check must never write a `.lpo`, which
could go stale or race a manual ./check.py run). On success it reports a
one-line confirmation with elapsed time; on failure it renders every error.
Silent only for non-.lp files. Never fails the turn (exit 0 always).
"""
import json
import re
import subprocess
import sys
import time
from pathlib import Path

TIMEOUT = 120       # wall-clock s; a hand-edited source compiles slower than a goal
_MAX_TYPE = 500     # characters, per hypothesis type / conclusion
_MAX_HYPS = 20      # hypotheses rendered per goal
_MAX_GOALS = 8      # goals rendered per before/after block
_MAX_RAW = 1500     # characters of raw output to surface when nothing parses

ANSI = re.compile(r"\x1b\[[0-9;]*m")
LOC_RE = re.compile(r"^\[(?P<path>[^\]]*?\.lp):(?P<line>\d+):(?P<col>[\d:-]+)\]"
                    r"\s*(?P<msg>.*)$")
STRUCT_RE = re.compile(r"^(Start|End) checking |^axiom _ax\d+:")


def _emit(context):
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": context,
        }
    }))


def _clip(s, n=_MAX_TYPE):
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[:n - 1] + "…"


def _fmt_goal(g):
    hyps = g.get("hyps") or []
    lines = [f"      {h.get('name', '?')} : {_clip(h.get('type', ''))}"
             for h in hyps[:_MAX_HYPS]]
    if len(hyps) > _MAX_HYPS:
        lines.append(f"      … (+{len(hyps) - _MAX_HYPS} more hypotheses)")
    lines.append(f"      ⊢ {_clip(g.get('concl') or g.get('constr') or '')}")
    return "\n".join(lines)


def _fmt_state(label, goals):
    block = "\n".join(_fmt_goal(g) for g in goals[:_MAX_GOALS])
    if len(goals) > _MAX_GOALS:
        block += f"\n      … (+{len(goals) - _MAX_GOALS} more goals)"
    return f"  {label}:\n{block}"


def _errors_from_json(out):
    """Errors from `--json` diagnostics, with goal states when attached."""
    errors = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            ev = json.loads(line)
        except json.JSONDecodeError:
            continue
        if ev.get("kind") != "diagnostic" or ev.get("severity") != "error":
            continue
        start = (ev.get("range") or {}).get("start") or {}
        entry = [f"[{start.get('line', '?')}:{start.get('col', '?')}] "
                 f"{ev.get('message', '')}"]
        if ev.get("goals_before"):
            entry.append(_fmt_state("goal state before", ev["goals_before"]))
        if ev.get("goals_after"):
            entry.append(_fmt_state("subgoals left open", ev["goals_after"]))
        errors.append("\n".join(entry))
    return errors


def _errors_from_text(out):
    """Errors from plain output: a `[file:line:col]` line opens a block whose
    message may continue on the following lines."""
    errors, cur = [], None

    def close():
        nonlocal cur
        if cur and cur[1].strip() and not cur[1].lower().startswith("warning"):
            errors.append(f"[{cur[0]}] {_clip(cur[1], _MAX_RAW)}")
        cur = None

    for ln in ANSI.sub("", out).splitlines():
        ln = ln.rstrip()
        if STRUCT_RE.match(ln):
            close()
            continue
        m = LOC_RE.match(ln)
        if m:
            close()
            cur = [f"{m['line']}:{m['col']}", m["msg"].strip()]
            continue
        if cur is not None and ln.strip():
            cur[1] = (cur[1] + " " + ln.strip()).strip()
    close()
    return errors


def main():
    try:
        event = json.load(sys.stdin)
    except Exception:
        return
    path_s = (event.get("tool_input") or {}).get("file_path") or ""
    if not path_s.endswith(".lp"):
        return
    path = Path(path_s)
    try:
        if not path.is_file():
            return
        path = path.resolve()
    except OSError:
        return
    # No `-c`: read-only, never writes a `.lpo` (the cache writer is
    # ./check.py). --too-long=5 surfaces any single command taking >5s.
    base = ["lambdapi", "check", "--too-long=5", str(path)]
    rich = base[:2] + ["--json", "--proof-state-on-error"] + base[2:]
    t0 = time.monotonic()
    try:
        r = subprocess.run(rich, capture_output=True, text=True, timeout=TIMEOUT)
        used_json = "unknown option" not in (r.stderr or "")
        if not used_json:
            r = subprocess.run(base, capture_output=True, text=True,
                               timeout=TIMEOUT)
    except FileNotFoundError:
        return
    except subprocess.TimeoutExpired:
        _emit(f"⏱ lambdapi check timed out after {TIMEOUT}s on {path.name} "
              f"— too slow to verify this edit automatically; run "
              f"./check.py {path.name} manually.")
        return
    dt = time.monotonic() - t0
    if r.returncode == 0:
        _emit(f"✓ lambdapi check passed: {path.name} ({dt:.1f}s, read-only — "
              f"run ./check.py {path.name} to refresh its .lpo).")
        return
    out = r.stdout + "\n" + r.stderr
    errors = (_errors_from_json(out) if used_json else []) \
        or _errors_from_text(out)
    if not errors:
        raw = (r.stderr or r.stdout).strip()
        if not raw:
            return
        errors.append(_clip(ANSI.sub("", raw), _MAX_RAW))
    _emit("`lambdapi check` failed on the file you just edited:\n\n"
          + "\n\n".join(errors))


if __name__ == "__main__":
    main()
