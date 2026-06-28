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

```bash
./check.sh                 # type-check the whole package (writes .lpo caches)
./check.sh Order.lp        # type-check one file (+ its deps)
lambdapi check Foo.lp      # read-only check (no .lpo written) — fastest feedback loop
python3 tools/audit.py --status   # dashboard: admits + completeness vs Isabelle source
python3 tools/audit.py Order      # detailed completeness audit of one module
```

A **PostToolUse hook** (`.claude/hooks/lp_check.py`, wired up in
`.claude/settings.json`) automatically runs a read-only `lambdapi check` on every
`.lp` you Write/Edit and surfaces the **proof state at the failure point**. So
after an edit you immediately see whether it type-checks and, if not, the goal
the failing tactic faced — no need to re-run anything to see the goal.

---

## 2. Layout

```
lambdapi.pkg          package zf, root_path = ZF  → file Foo.lp is module ZF.Foo
check.sh              build script (lambdapi check -c)
*.lp                  the port (ZF.* modules)
isabelle-src/*.thy    the Isabelle/ZF sources being ported (the source of truth)
tools/audit.py        completeness/status auditor (Isabelle .thy vs .lp)
.claude/hooks/        lp_check.py — edit-time type-check hook
.claude/settings.json shared: enables the hook + common permissions
```

`Stdlib.*` (Set, Prop, FOL, Eq, Classic, Impred, HOL, PropExt, Epsilon) ships
with Lambdapi's library root; `ZF.*` resolves locally via `lambdapi.pkg`.

---

## 3. Authoritative encodings — DO NOT silently change these

These were deliberate decisions (faithful to Isabelle/ZF). Match them; never
"simplify" a definition to make a proof easier.

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
   inherit that. Run `tools/audit.py <Module>` and add what's missing.

**Difficult proofs may be left as `admit`** (with a clear `// TODO` explaining
what's needed) — the goal is no *missing statements*, not no *holes*. But never
fake a proof, never use `--no-sr-check`, and never `admit` something easy.

`tools/audit.py` notes: for the *base* files (`equalities`, `upair`, `func`,
`ZF_Base`, `Univ`, `Bool_ZF` …) the huge "missing" counts are mostly Isabelle
**simp-lemma noise** that the development doesn't use — focus completeness effort
on the **frontier modules you are actively porting**.

---

## 5. Porting workflow for a module `Foo`

1. **Check it's ready:** all theories `Foo.thy` *imports* must already be `.lp`
   here. `python3 tools/audit.py --status` lists un-ported `.thy`.
2. **Read** `isabelle-src/Foo.thy` and **all** dependency `.lp` files (to know the
   available symbol names — they differ from Isabelle's; e.g. `id_fun` not `id_bij`,
   `case_sum` not `case`).
3. **Translate** definitions first, then notations, then lemmas easy→hard. Use the
   type table below. Keep statements faithful (§4.1).
4. **Iterate** with `lambdapi check Foo.lp` (the hook also reports on each edit).
   Fix the first error; repeat. The error shows the goal state.
5. **Audit completeness:** `python3 tools/audit.py Foo` — add every genuine
   missing item (prove, or `admit` + TODO if hard).
6. **Finalize:** `./check.sh Foo.lp` → "OK", then check admits with
   `grep -cnE '^\s*admit\b' Foo.lp`. Then a clean full build:
   `rm -f *.lpo && ./check.sh` must end "OK: type-checked successfully".
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
  *source*, but it does **not** always invalidate on a *dependency* change. After
  editing a base file (e.g. `pair.lp`, `Ordinal.lp`) ALWAYS do
  `rm -f *.lpo && ./check.sh` to get the true state — a stale cache can show a
  false "OK". The edit-time hook is `-c`-free precisely to avoid writing stale caches.
- **Counting admits.** `grep -cw admit` counts *comment* lines containing the word
  too. For the real tactic count use `grep -cnE '^\s*admit\b'` (or `tools/audit.py
  --status`). `admit` (tactic, leaves a hole + axiom) ≠ `admitted` (ends a proof).
- **Pre-existing debt** (flag, don't be alarmed): `Perm.lp` and `EquivClass.lp`
  carry admits from before; `Order.lp` has one documented capstone admit
  (`well_ord_trichotomy`).
- **Don't reintroduce an abstract `Pair`** or **bare `lt`/`le`** (see §3).
- `private`/`opaque` symbols can't be unfolded by callers — match the existing
  visibility of the lemma you're porting.

---

## 8. Status & dependency order toward Cardinal

Done & committed: `Sum`, `pair` (concrete), `Ordinal` (Ord-carrying lt/le),
`OrdQuant`, `Order` (14/15). Run `tools/audit.py --status` for the live picture.

Isabelle import chain toward **Cardinal** (north star):
```
QPair      ← Sum, func                    (ready)
Nat        ← OrdQuant, Bool               (ready)        → Arith ← Univ
Inductive  ← Fixedpt, QPair
OrderArith ← Order, Sum                   (ready once Order capstone irrelevant)
Finite     ← Inductive, Epsilon, Nat
OrderType  ← OrderArith, OrdQuant, Nat
Cardinal   ← OrderType, Finite, Nat, Sum
```
`ZFC` (deps all present) is a small off-path module. When a module's source
differs subtly from what's here (`Ordinal`/`Perm`/`Nat_ZF` were hand-ported),
verify the symbol names you call still exist (`grep` the dep `.lp`).
