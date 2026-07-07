# PORTING_LOOP.md — the autonomous porting iteration

This is the operational loop for unsupervised porting of Isabelle/ZF → Lambdapi.
It assumes CLAUDE.md (encodings, faithfulness, workflow) and the `lambdapi`
skill. The feedback loop is three tools; the discipline is the gates.

## Two stages

Completeness before proofs (CLAUDE.md §4: "the goal is no missing *statements*,
not no *holes*"). So the loop runs in two stages, and `status.py`'s `NEXT`
enforces the order:

- **Stage 1 — SKELETON.** Get every statement PRESENT. Breadth-first across the
  dependency tree: for each un-ported module whose deps are met, create its `.lp`
  with every definition (real body) and every lemma as an admitted stub. A
  module's *statements* are all its dependents need to type-check, so skeletoning
  unblocks the whole tree fast. This is the loop's **first** job.
- **Stage 2 — PROVE.** Discharge the `admit`s, finishing the module closest to
  done first.

Stage 1 deliberately RAISES the admit count — that is not a regression. The gate
protects *proved* lemmas from reverting, not the raw admit total.

## The sensor: one command, one truth

```bash
python3 tools/status.py         # clean build (~3s) + worklist + gates + NEXT
python3 tools/status.py --next  # just the next action
python3 tools/status.py --json  # machine-readable (for the driver)
python3 tools/status.py --axioms [Mod]   # the admit worklist, with statements
python3 tools/fidelity.py <Mod> [--only NAME|--diff|--json]  # ISA vs LP stmts
```

`status.py` always builds **cold** (removes `.lpo`) because lambdapi only prints
the `admit`→`axiom _axN: <statement>` lines while actually checking. That build
is the ground truth for: green/red, the 222 admits (as statements, by
`file:line`), completeness, the anti-cheat gates, and the ready-to-port frontier.

**Bootstrap (once, at session start):** run `python3 tools/status.py
--save-baseline` to sync the regression floor (`tools/port_baseline.json`, a
local uncommitted cache) to the tree you are starting from. Confirm the build is
green before the first edit.

## One iteration

1. **Sense** — `python3 tools/status.py`. Read `NEXT` and the gates.
2. **Pick** — take `NEXT` unless you have a better-justified move. Priority:
   `FIX BUILD` ≫ **`SKELETON NEW MODULE`** ≫ `PORT MISSING STATEMENT` ≫
   `PROVE ADMIT` (Stage 1 before Stage 2; "finish the closest module" = fewest
   admits first).
3. **Act**
   - *Skeleton a new module (Stage 1):* create `<Module>.lp`. `require open` its
     ported deps. Translate **every** `definition`/`abbreviation` with a faithful
     body, and **every** `lemma`/`theorem`/`corollary` as
     `opaque symbol NAME (params) : π (STATEMENT) ≔ begin admit end;` —
     statement faithful (§4.1), proof deferred. Work easy→hard so the file
     type-checks; the module is "done for Stage 1" when it builds green with all
     statements present (audit.py shows 0 genuine-missing). Follow CLAUDE.md §5
     for symbol-name lookup in deps.
   - *Prove an admit (Stage 2):* edit at the admit's `file:line`; replace `admit`
     with the proof. The edit hook shows the goal state on each save.
   - *Port a missing statement:* translate the Isabelle statement **faithfully**
     (§4.1), then prove it or leave `admit` + `// TODO`.
4. **Verify — ALL must hold before you commit:**
   - `python3 tools/status.py --gate` exits **0** (green build; no forbidden
     flags; no proved lemma reverted to `admit`; no new bare-axiom `symbol`).
   - **Fidelity of everything you added/changed**: `python3 tools/fidelity.py
     <Mod> --only <name>` — the LP statement must match the ISA statement with no
     added hypothesis (esp. a stray `Ord`), no dropped premise, no specialised
     conclusion. For a batch, judge `fidelity.py <Mod> --json` per name.
   - **Progress**: completeness ↑ (Stage 1) **or** admits ↓ (Stage 2). If
     neither, you got stuck (go to the skip rule) or you are refactoring (say so
     in the commit).
5. **Commit + rebaseline** — `git commit -m "<Mod>: <what> (N→M admits)"`, then
   `python3 tools/status.py --save-baseline` so the regression floor tracks the
   new state. Push + submodule bump per CLAUDE.md §5.7 is a **batch** action
   (module complete, or on request) — not every iteration.
6. **Loop.**

## The cardinal rules (never, even to make the build green)

- **Never weaken a statement** to close a proof. If a proof seems to need a
  hypothesis Isabelle lacks, *derive* it; if you cannot, leave the `admit`. A
  weakened lemma that type-checks is worse than an honest hole — it is a lie the
  gates below are designed to catch.
- **Never fake a proof, never `--no-sr-check`, never `admit` an easy goal.**
- **Hard proof → `admit` + `// TODO: <precisely what is needed>`**, then move to
  the next item. Do not spin more than ~3 serious attempts on one admit in a
  single iteration; a clear TODO is worth more than a fourth failed attempt.
- **Build won't recover in ≤2 edits → `git checkout -- <file>`** to the last
  green commit and pick a different item. Never leave the tree red across a
  commit.
- **Scratch files** (`.check-exclude`: GST.lp, AC_Test.lp) are experiments, not
  port work — never edit them to satisfy the loop.

## What the gates actually catch

| Gate | Catches |
|---|---|
| build green (cold) | any type error; stale-cache false-green (always cold) |
| `no-forbidden-flags` | `--no-sr-check` and friends smuggled into a source/script |
| `no-proof-reverted` | a once-proved lemma quietly reverting to `admit` or vanishing (adding fresh admits is fine — that's Stage 1) |
| `no-new-axioms` | a bare `symbol f : T;` used to assume away a subgoal |
| fidelity (manual/agent) | a statement weakened to fit the proof |

The one gate a machine can't fully close is fidelity — so it is the one the loop
must run **by judgment** on every changed statement. Everything else is `--gate`.
