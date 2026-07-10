# CLAUDE.md — porting Isabelle/ZF to Lambdapi

This repository (`lambdapi-zf`) is the **authoritative** Lambdapi port of
Isabelle/ZF. It is vendored into `~/prog/hyperset` as the `lp/ZF` submodule.

> Older attempts in `~/prog/lp-slop/zf` and the previous `hyperset` history are
> **superseded** — do not treat their `.lp` files as correct. The only thing
> worth reusing from `lp-slop` is occasionally a *draft proof* as a starting
> hint, and even then verify it against this repo's conventions. The Isabelle
> sources are vendored **here**, in `isabelle-src/` — use those, not lp-slop's.

Activate the **`lambdapi` skill** (`Skill` tool, `skill="lambdapi"`) before
editing `.lp` files — it documents the CLI, tactics, and stdlib.

---

## 1. Quick start

**`./check.py` is the single feedback tool** — build, worklist, anti-cheat
gates, and the next action, in one place:

```bash
./check.py                 # THE loop sensor: cold build of the whole port +
                           #   admit worklist + gaps + repo hygiene +
                           #   anti-cheat gates + NEXT action  (~4s)
./check.py Order.lp        # fast targeted type-check (+ deps; writes .lpo)
lambdapi check Foo.lp      # read-only check (no .lpo written)
./check.py --gate          # exit nonzero iff build red / cheated / regressed
                           #   — run BEFORE every commit
./check.py --admits Cardinal   # the admit worklist, as full statements
./check.py --missing Order     # completeness detail vs isabelle-src
./check.py --fidelity Order    # pair each Isabelle statement with its .lp port
```

The anti-cheat gates compare the working tree against **git HEAD** (no state
file): a lemma proved in HEAD must not revert to `admit` or vanish, no new bare
`π`-axiom may appear, no forbidden flags (`--no-sr-check`) anywhere. Gating
before each commit means a regression can never be committed silently. For
autonomous work, one iteration = `./check.py` (sense) → do the NEXT action →
`./check.py --gate` must pass → commit. `.check-exclude` lists
scratch/experimental `.lp` (GST, AC_Test) that are NOT part of the port, so a
broken experiment can never turn the build red or mask the port's state.

A **PostToolUse hook** (`.claude/hooks/lp_check.py`, wired up in
`.claude/settings.json`) automatically runs a read-only `lambdapi check` on
every `.lp` you Write/Edit and surfaces the diagnostics at the failure point.
The local `lambdapi` is a moving dev target (we work on lambdapi PRs); the hook
probes for the rich CLI (`--json --proof-state-on-error`, which renders the
goal state a failing tactic faced) and falls back to plain-text parsing when
the installed binary lacks it.

---

## 2. Layout

```
lambdapi.pkg          package zf, root_path = ZF  → file Foo.lp is module ZF.Foo
check.py              THE tool: build/dashboard/gates/completeness/fidelity (§1)
*.lp                  the port (ZF.* modules)
isabelle-src/*.thy    the Isabelle/ZF sources being ported (the source of truth)
.claude/hooks/        lp_check.py — edit-time type-check hook
.claude/settings.json shared: enables the hook + common permissions
```

`Stdlib.*` (Set, Prop, FOL, Eq, Classic, Impred, HOL, PropExt, Epsilon) ships
with Lambdapi's library root; `ZF.*` resolves locally via `lambdapi.pkg`.

---

## 3. Authoritative encodings — DO NOT silently change these

These were deliberate decisions (faithful to Isabelle/ZF). Match them; never
"simplify" a definition to make a proof easier.

### Isabelle `definition` = declared constant + `_def` axiom (2026-07-10)
Every symbol that corresponds to an Isabelle keyword-`definition` is encoded
as a **declared constant** plus a **defining axiom** named `<name>_def`:
```
constant symbol pred (A x r : τ ι) : τ ι;
constant symbol pred_def (A x r : τ ι) :
  π (pred A x r = Collect A (λ y, Pair y x ∈ r));
```
Prop-valued definitions state `=` at code `o` (a `unif_rule` in upair.lp makes
plain `=` elaborate); the axiom RHS is the old `≔` body verbatim. check.py's
no-new-axioms gate shape-checks `_def` axioms (LHS must be the twin constant
applied to exactly its Π-params) so they are conservative extensions.
**Exceptions that stay transparent `≔`:** Isabelle `abbreviation`s (`∉`, `le`,
`Preorder`, …), the π-computing plumbing `Ball`/`Bex`/`⊆`, port-internal
helpers (`singleton`, `vimage_singleton`, `rel_image_sing`, `id_rel`,
`inductive_set`, …), and inductive-package sets (`Fin`, `list`, `TFin`).
**Proof idioms:** unfold in the GOAL with `rewrite X_def;` (before `assume x hx`
when the membership lands in a hypothesis); unfold a HYPOTHESIS `h` with
`ind_eq (eq_sym (X_def …)) (λ p, p) h` (Prop) or
`ind_eq (eq_sym (X_def …)) (λ w, t ∈ w) h` (membership).
Converted so far: upair.lp (Collect, RepFun, Upair, Un, Inter, Int, Diff,
cons, succ, The, If), Fixedpt.lp (bnd_mono, lfp, gfp), Nat_ZF.lp (omega).
The remaining ~185 definitions convert module-by-module (bottom-up:
pair → func → Sum/QPair/Trancl/WF → Perm/Order → …), each wave ending in a
green `./check.py --gate` commit.

### Ordered pairs are CONCRETE Kuratowski (`pair.lp`)
```
Pair a b ≔ Upair (singleton a) (Upair a b)      -- {{a},{a,b}}
fst p    ≔ The (λ a, ∃ b, p = Pair a b)
snd p    ≔ The (λ b, ∃ a, p = Pair a b)
```
`Pair_inject1/2`, `Pair_neq_0`, `fst_conv`, `snd_conv` are **proved** (not
axioms). **Consequence:** `fst (Pair a b)` does **NOT** reduce to `a`
definitionally — you must rewrite with `fst_conv a b : fst (Pair a b) = a`
(and `snd_conv`). Same for `snd`. (There is NO abstract Pair / reduction rule;
a previous experiment with that is abandoned.)

### `lt` / `le` CARRY `Ord` (`Ordinal.lp`), exactly as Isabelle
```
lt i j ≔ i ∈ j ∧ Ord j
le i j ≔ lt i (succ j)        -- i.e. (i ∈ succ j) ∧ Ord (succ j)
```
So `lt`/`le` are **not** bare membership. From `h : lt i j` use `ltD i j h : i∈j`
and `∧ₑ₂ h : Ord j`. From `h : le i j` use `leE i j h : i∈j ∨ i=j` and
`le_Ord2 i j h : Ord j`. To **build** them: `ltI i j (i∈j) (Ord j)`,
`leI i j (i∈j) (Ord j)`, `le_eqI i j (i=j) (Ord j)`, `le_refl i (Ord i)`.
This is why ordinal lemmas need no extra `Ord` hypotheses beyond Isabelle's — the
`Ord` travels inside `lt`/`le`.

See memory `concrete-kuratowski-pairs-and-isabelle-lt` for the rationale.

---

## 4. Faithfulness — the prime directive

A port is faithful iff **both** hold:

1. **Statement fidelity.** Every ported `definition`/`lemma`/`theorem` matches the
   Isabelle statement (same quantifier structure, hypotheses, conclusion). Do not
   weaken a statement (e.g. add an `Ord` hypothesis Isabelle lacks, or special-case
   it) to make a proof go through. If a proof needs something extra, derive it.
2. **Completeness.** The `.lp` must contain **every** genuine def/lemma/theorem in
   the source `.thy`. The lp-slop drafts silently dropped many lemmas — do not
   inherit that. Run `./check.py --missing <Module>` and add what's missing.
   `--fidelity <Module>` puts each Isabelle statement next to its port so a
   weakened statement is visible.

**Difficult proofs may be left as `admit`** (with a clear `// TODO` explaining
what's needed) — the goal is no *missing statements*, not no *holes*. But never
fake a proof, never use `--no-sr-check`, and never `admit` something easy.

`--missing` notes: for the *base* files (`equalities`, `upair`, `func`,
`ZF_Base`, `Univ`, `Bool_ZF` …) the huge "missing" counts are mostly Isabelle
**simp-lemma noise** that the development doesn't use — focus completeness effort
on the **frontier modules you are actively porting** (the dashboard's GAPS line
already filters to those).

---

## 5. Porting workflow for a module `Foo`

1. **Check it's ready:** all theories `Foo.thy` *imports* must already be `.lp`
   here. The dashboard's READY line (`./check.py`) lists un-ported `.thy` whose
   deps are met.
2. **Read** `isabelle-src/Foo.thy` and **all** dependency `.lp` files (to know the
   available symbol names — they differ from Isabelle's; e.g. `id_fun` not `id_bij`,
   `case_sum` not `case`).
3. **Translate** definitions first, then notations, then lemmas easy→hard. Use the
   type table below. Keep statements faithful (§4.1).
4. **Iterate** with `lambdapi check Foo.lp` (the hook also reports on each edit).
   Fix the first error; repeat.
5. **Audit completeness:** `./check.py --missing Foo` — add every genuine
   missing item (prove, or `admit` + TODO if hard).
6. **Finalize:** `./check.py --gate` must pass (green cold build + no gate
   failures); its ADMITS line is the authoritative admit count.
7. **Commit + push**, then **bump the submodule** in `~/prog/hyperset`:
   ```bash
   (cd ~/prog/hyperset/lp/ZF && git fetch -q origin && git checkout -q main && git merge --ff-only origin/main)
   (cd ~/prog/hyperset && git add lp/ZF && git commit -m "Bump lp/ZF: <what>" && git push)
   ```

### Type translation (Isabelle → Lambdapi)
| Isabelle | Lambdapi | from |
|---|---|---|
| `i` (set) | `τ ι` | Stdlib.Set |
| `o` (prop) | `Prop` / `π (…)` | Stdlib |
| `∈ 0 ⟨a,b⟩ A∪B A∩B A-B ⋃A Pow` | `∈ empty (Pair a b) (Un A B) (Int A B) (Diff A B) (Union A) (Pow A)` | ZF_Base/upair |
| `succ cons {a} {a,b}` | `succ`, `cons a A`, `singleton a`, `Upair a b` | upair |
| `Sigma fst snd split` | `Sigma A B`, `fst`, `snd`, `split` | pair |
| `f`a Lambda(A,b) Pi` | `fapply f a`, `Lambda A b`, `Pi A B` | pair/func |
| `∀x∈A.P / ∃x∈A.P` | `Ball A (λ x, P)` / `Bex A (λ x, P)` | ZF_Base |
| `THE x. P` | `The (λ x, P)` (`≔ ε`) | upair |
| `True False ∧ ∨ ⟶ ⟷ ¬` | `⊤ ⊥ ∧ ∨ ⇒ ⇔ ¬` | Stdlib.Prop |
| `0 succ` ordinals; `i<j i≤j Ord` | `empty succ`; `lt i j`, `le i j`, `Ord i` | Ordinal |

---

## 6. Lambdapi proof cheatsheet (this codebase's idioms)

**Structure:** `opaque symbol name (args) : π (STATEMENT) ≔ begin … end;`
Parameters declared before `:` are Π-bound — the proof must `assume` them first.

**Stdlib intro/elim** (note the subscript-i/e naming):
`∧ᵢ`, `∧ₑ₁`, `∧ₑ₂`; `∨ᵢ₁`, `∨ᵢ₂`, `∨ₑ h fL fR`; `∃ᵢ witness pf`, `∃ₑ h (λ x hx, …)`
(here used as `refine ∃ₑ h _; assume x hx; …`); `⊥ₑ`; `⊤ᵢ`; `em P : P ∨ ¬P`
(classical); `eq_refl`, `eq_sym`.

**Rewriting with equalities** — `ind_eq` direction matters:
```
ind_eq (h : a = b) (P : τ ι → Prop) (pf : π (P b)) : π (P a)    -- rewrites b → a
```
So to turn a proof of `P a` into `P b`, use `ind_eq (eq_sym h) …`. The `rewrite`
tactic also works (left-to-right on the goal); `reflexivity` closes `x = x`.

**Sets:** `equality_iffI A B (λ x, ⟨pf x∈A ⇔ x∈B⟩) : A = B`; `subset_antisym`;
`extension`; membership in goal `A ⊆ B` is proved by `assume x hx; …`.
`CollectI/CollectD1/CollectD2`, `RepFunI/RepFun_iff`, `UnionI/UnionE`,
`Upair_iff/UpairI1/UpairI2/UpairE`, `singleton_iff/singletonI`,
`cons_iff/consI1/consI2`, `emptyE`, `equals0I`.

**Pairs (concrete!):** project with `fst_conv`/`snd_conv` (do NOT expect
reduction). `SigmaI x y A B (x∈A) (y∈B x)`, `SigmaE`, `Pair_inject1/2`.

**Ordinals:** `Ord_0`, `Ord_succ`, `Ord_in_Ord`, `Ord_trans`, `Ord_linear`,
`OrdmemD`, `trans_induct`; `succ_iff c i : c∈succ i ⇔ (c=i ∨ c∈i)`,
`succI1 i : i∈succ i`, `succI2 c i : c∈i → c∈succ i`. For `lt`/`le` see §3.

**Tactic power-ups** (verified on lambdapi 3.0.0-87 — use these, they cut
proof length substantially):

- `simplify rule off;` β-normalizes the goal **without** unfolding
  `≔`-definitions (`fst` stays `fst`, no `The`-explosion). Use it right after a
  `rewrite` whose RHS is a meta-application (`case_Inl`, `beta`, …) and leaves
  `(λ …) x` redexes blocking the next rewrite — replaces the old
  `have hstep : π (reduced form) {…}; refine hstep` workaround.
- `rewrite` takes **Π-quantified** equations: `rewrite fst_conv;` finds the
  instance itself — don't spell out `rewrite (fst_conv (Pair a b) c)`.
- `rewrite left h;` rewrites **right-to-left** — use instead of
  `eq_sym`/`ind_eq` transport gymnastics.
- Tacticals are script-level, prefix, **no parentheses**:
  `repeat orelse rewrite fst_conv rewrite snd_conv;` is a one-line simp-lite;
  `repeat refine SigmaI _ _ _ _ _ _` stacks intro rules greedily. Two quirks:
  `repeat` **stops as soon as the goal count decreases** (a leaf closes), so
  put closing steps after the loop, and a step leaving N goals must be
  followed by N `{ … }` subproof blocks.

**Worked micro-example** (extract `Ord` from `lt`, build a new `lt`):
```
assume i k P hik hstep;          // hik : lt i k
have hOk : π (Ord k) { refine ∧ₑ₂ hik };
have hik_mem : π (i ∈ k) { refine ltD i k hik };
… refine hstep x (ltI x k hxk hOk) …   // rebuild lt x k from x∈k and Ord k
```

---

## 7. Gotchas

- **Stale `.lpo` caches.** `lambdapi check` reuses a `.lpo` if it is newer than its
  *source*, but it does **not** always invalidate on a *dependency* change. The
  `./check.py` dashboard is immune (it always builds cold), but after editing a
  base file (e.g. `pair.lp`, `Ordinal.lp`) don't trust *targeted* checks until
  you've re-run `./check.py` — a stale cache can show a false "OK". The
  edit-time hook is `-c`-free precisely to avoid writing stale caches.
- **Counting admits.** `grep -cw admit` counts *comment* lines containing the
  word too. The authoritative count is the dashboard's ADMITS line (harvested
  from the type-checker itself); `./check.py --admits Foo` lists them as
  statements. `admit` (tactic, leaves a hole + axiom) ≠ `admitted` (ends a proof).
- **The `lambdapi` binary changes under us** (it's a locally-built dev version;
  we work on lambdapi PRs). If tooling output suddenly looks wrong, suspect a
  rebuilt binary before suspecting the port. `check.py` uses only stable CLI
  surface; the hook probes for rich flags and falls back automatically.
- **Pre-existing debt** (flag, don't be alarmed): `Perm.lp` and `EquivClass.lp`
  carry admits from before; `Order.lp` has one documented capstone admit
  (`well_ord_trichotomy`).
- **Don't reintroduce an abstract `Pair`** or **bare `lt`/`le`** (see §3).
- `private`/`opaque` symbols can't be unfolded by callers — match the existing
  visibility of the lemma you're porting.

---

## 8. Status & direction

The whole import chain to **Cardinal** (the north star) is skeletoned and
green; the work now is proving down the admits (Cardinal, OrderType) and
skeletoning the next READY modules. Run `./check.py` for the live picture —
its NEXT line is the current move.

When a module's source differs subtly from what's here (`Ordinal`/`Perm`/
`Nat_ZF` were hand-ported), verify the symbol names you call still exist
(`grep` the dep `.lp`).
