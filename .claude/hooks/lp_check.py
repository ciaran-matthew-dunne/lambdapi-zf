#!/usr/bin/env python3
"""PostToolUse hook: type-check an edited Lambdapi (.lp) file and surface its
diagnostics — including the proof state at the failure point — back to the agent.

Adapted from hyperset's .claude/hooks/lp_check.py for this repo's SINGLE-package
layout: every .lp file lives at the root of the `zf` package (root_path = ZF, see
lambdapi.pkg), so module lookup is handled entirely by the local lambdapi.pkg and
NO `--map-dir` is ever needed (cf. ./check.sh). It runs `lambdapi check --json
--proof-state-on-error` WITHOUT `-c` (an edit-time check must never write a
`.lpo`, which could leave a stale/partial object behind or race a manual
./check.sh) and renders, on failure, the goal state a failing tactic faced
(`goals_before`) and any subgoals left open (`goals_after`).

On success it reports a one-line confirmation (with elapsed time) so a green edit
is positively acknowledged rather than ambiguously silent; on failure it renders
the message + goal state. Silent only for non-.lp files. Never fails the turn
(exit 0 always): any error here just means no extra context.
"""
import json
import subprocess
import sys
import time
from pathlib import Path


def _emit(context):
    """Send one line of additionalContext back to the agent (success or
    failure). PostToolUse surfaces this in the transcript."""
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": context,
        }
    }))

TIMEOUT = 120       # wall-clock s; a hand-edited source compiles slower than a goal
_MAX_TYPE = 500     # characters, per hypothesis type / conclusion
_MAX_HYPS = 20      # hypotheses rendered per goal
_MAX_GOALS = 8      # goals rendered per before/after block
_MAX_RAW = 1500     # characters of raw output to surface when no JSON diagnostic


def _clip(s, n=_MAX_TYPE):
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[:n - 1] + "…"


def _fmt_goal(g):
    """Render one goal: its hypotheses as `name : type` lines, then the
    conclusion (typing goal) or constraint (unification goal) after a `⊢`."""
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
    # No `-c`: this read-only check never writes a `.lpo`. The authoritative
    # cache writer is ./check.sh (which DOES pass -c); keeping the edit-time hook
    # read-only means it can never race that writer over the shared dependency
    # objects, nor leave a partial `.lpo` if it times out mid-edit. After a file
    # goes green, run ./check.sh on it to warm the cache for downstream files.
    # --too-long=5: surface any single command that takes >5s as a warning.
    cmd = ["lambdapi", "check", "--json", "--proof-state-on-error", "--too-long=5",
           str(path)]
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except FileNotFoundError:
        return
    except subprocess.TimeoutExpired:
        _emit(f"⏱ lambdapi check timed out after {TIMEOUT}s on {path.name} "
              f"— too slow to verify this edit automatically; run ./check.sh "
              f"{path.name} manually.")
        return
    dt = time.monotonic() - t0
    if r.returncode == 0:
        _emit(f"✓ lambdapi check passed: {path.name} ({dt:.1f}s, read-only — "
              f"run ./check.sh {path.name} to refresh its .lpo).")
        return
    diagnostics = []
    for line in (r.stdout + "\n" + r.stderr).splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            ev = json.loads(line)
        except json.JSONDecodeError:
            continue
        if ev.get("kind") == "diagnostic":
            diagnostics.append(ev)
    errors = []
    for ev in diagnostics:
        if ev.get("severity") != "error":
            continue
        start = (ev.get("range") or {}).get("start") or {}
        loc = f"{start.get('line', '?')}:{start.get('col', '?')}"
        entry = [f"[{loc}] {ev.get('message', '')}"]
        # The proof state, when --proof-state-on-error attached it: goals_before
        # for a tactic failure, goals_after for a subproof-count mismatch.
        if ev.get("goals_before"):
            entry.append(_fmt_state("goal state before", ev["goals_before"]))
        if ev.get("goals_after"):
            entry.append(_fmt_state("subgoals left open", ev["goals_after"]))
        errors.append("\n".join(entry))
    if not errors:
        # Non-zero exit but no structured error (e.g. a CLI/parse failure on
        # stderr) — surface the raw tail so the agent still sees something.
        raw = (r.stderr or r.stdout).strip()
        if not raw:
            return
        errors.append(_clip(raw, _MAX_RAW))
    _emit("`lambdapi check` failed on the file you just edited:\n\n"
          + "\n\n".join(errors))


if __name__ == "__main__":
    main()
