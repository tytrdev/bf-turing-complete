# Status

`BF.simulates_TM0` / `BF.Reference.claim : BF.Claim` is proven (no sorry; axioms: propext, Classical.choice, Quot.sound).

## Layout
- `Core/` (frozen, shared, not counted): BF syntax + small-step semantics (`Basic.lean`); `BlockCode`, `encTape`, `Claim` (`Statement.lean`).
- `Reference/`: the original proof, plus tests (`Test.lean`, `CompileTest.lean`).
- `scripts/count.py`: non-whitespace characters (Unicode code points) and Lean tokens per version (tests excluded).

## Compression exercises
Each lives in its own folder and namespace and must end with `theorem ... : BF.Claim`.
Everything except `Core/` is free, including the compiler and the encoding.
Score = Lean tokens (identifiers, numbers, keywords, operators each count 1; comments included). Names are free, so use readable ones. Characters are still printed for reference only.

1. `Golf/`: shortest possible, readability irrelevant.
2. `Exposition/`: most readable for humans, length irrelevant.
3. `Elegant/`: as short as possible while staying elegant and readable.

Current (chars / tokens): Reference = 38076 / 15793. Golf = 17572 / 9629 (v1 was 10472). Elegant = 21374 / 9712.

## Reference proof architecture
Compiler (`Compile.lean`): one-hot blocks of width 2n+2m+6 per TM cell (sym, xsym, st, pend, T, ML, MR, R).
Step = dispatch (state, then symbol) → flush pending symbol → move (carry pend+R to neighbour block) → commit pending state; main loop `ifAt R`.
Proof: `Runs` (big-step from small-step) → `Holds` block view → `Spec` over flag predicates `ℤ → ℕ → Prop` → per-gadget specs with `bf_omega`/`bf_iff` → `Respects` + `tr_eval`/`tr_eval_rev` → relabel finite Γ/Λ to `Fin`.

## Lessons
- Keep every state in arithmetic form (`symAt`, offsets, transition numbers `newSym/nst/cont/mvL/mvR`) so `omega` closes side goals.
- `omega` chokes on `False → _`, `¬True`: simp them away first (see `bf_omega`).
- Give intermediate states explicitly when `by` blocks would otherwise see metavariables.
- `toBlk` is classical `if`; bridge to computable `if` with `classical; exact if_congr Iff.rfl rfl rfl`.
- `tr_eval'` forces one universe; use `tr_eval` + `tr_eval_rev` with `Part.ext`.
- `simp` rewrites `T.nth 0` to `T.head`; use `simp only` when hypotheses mention `nth 0`.

## Golf v1 design (`Golf/G.lean`)
- `H w b P t`: flags `P` in blocks of width `w`, viewed from base offset `b`; moving only changes `b`, so no tape equalities are ever needed.
- Four primitives (`S.tg` toggle, `S.l0`/`S.l1` loops, `S.mo` move) give every gadget.
- Compiles over Γ/Λ directly via `E : α ≃ Fin (card α - 1 + 1)` with `default ↦ 0` (no relabelling layer).
- A transition is one tuple `D q a`; `act` is five `if c then incAt x`, one lemma `S.oi`.
- Use `card Γ - 1` inline, never a `def`/`abbrev` alias: omega reads `Fin` bounds off binder types, so aliases create unrelated atoms.

## Token golf log (Golf/G.lean)
Done: auto-param side goals on `S.i0`/`S.i1` (-230), one-sided `S.cr`/`S.cl` (-28),
named offsets `O M k`, `Pd M i`, `St M i` (-586). Tried and reverted: a finRange `S.fr`
(explicit or auto-param no-op proofs both came out +20 tokens).

Original plan (items 1 and 4 done):
Biggest declarations: dsS 496, caS 491, ev 484, mvS 430, cmS 397, it 377, tmS 355, flS 317, r0 279.
Planned structural cuts (names are free now):
1. Name the repeated offsets (`Tf`, `ML`, `MR`, `Rf`, `pd k`, `st k`) and the transition projections
   (`cont M q T := (D M q (T.nth 0)).2.2.1`, etc.) as defs unfolded by `om`. Never alias inside `Fin` types.
2. Name the phase states (`afterDispatch`, `afterFlush`, `afterMove`, `afterCommit`) so each phase
   statement is a single line and `bdS` is pure composition.
3. A finRange-specialised `S.f1` whose no-op side conditions are arithmetic (`i.val ≠ a.val → ¬P 0 (g i)`),
   discharged by `om` directly; drop the repeated `intro i _ h; have := Fin.val_ne_of_ne h; exact S.i0 ..`.
4. A tactic for the repeated `exact S.i0 (by om) (by om)` / `S.i1 (by om) (by om) .. (by om)` shapes.
5. Look for a shorter `ev` (Part.ext with tr_eval/tr_eval_rev is ~480 tokens).
Build note: Golf/G.lean takes ~35 s and sets maxHeartbeats 1000000.

## Golf/Elegant lessons (session 2)
- Tactic macros used as auto-params must be declared before the lemma, with
  `set_option hygiene false in macro ...`, or the names in `simp only [...]` won't resolve.
- Auto-params run *before* the surrounding term's metavariables are solved. They are fine on
  `S.i0`/`S.i1` (o, P fixed by the program and context) but fail on `S.cq` (P'/Q' unknown); explicit
  `(by oi)` is postponed to the end and works.
- Build takes ~65 s since auto-params (was 31 s). Run builds in the background with a time cap.

## Elegant: redesign (agreed with Ty 2026-11-24)
`Elegant/Elegant.lean` is currently just Golf with readable names (v0). Ty's verdict: renaming is not
elegance. Replace it with a two-layer proof in which no offset arithmetic and no `omega` appear in
the TM part.

**Layer A: BF implements flag machines (generic, proved once).**
- A flag type `F` with `[Fintype F] [DecidableEq F]` and a fixed layout `ι : F ↪ Fin w`; tape view
  `Holds b P t`, where `P : ℤ → F → Prop` gives the flags of each block. The layout arithmetic lives
  in one block lemma here and nowhere else.
- Flag programs: `inductive FProg | set (f) | clr (f) | when (f) (body : List FProg) | shift (d : ℤ)`.
  Compile with `set f = [-]+` and `clr f = [-]` at offset `ι f`. Both are idempotent and work on any
  cell value, so they need **no side conditions**. `when f body = [ [-] body ]` at `ι f` runs the
  body once if `f` was set; its only side condition is that the body leaves `f` clear.
- Denotation `⟦p⟧ : (ℤ → F → Prop) → (ℤ → F → Prop)` (with `shift` re-basing), and a single
  theorem: compiled code takes `Holds 0 P` to `Holds 0 ⟦p⟧ P`.

**Layer B: flag machines implement TM0.**
- `inductive Flag Γ Λ | sym (a : Γ) | state (q : Λ) | pendSym (a) | pendState (q) | left | right | run`
  (blank has no `sym` flag, so blank cells are all zero). Disjointness of flags comes from
  constructors being distinct, which `simp` handles: no `card Γ - 1`, `Fin.succ`, `E` equivs or 0/1 `Act`.
- One step = for each state and symbol `when (state q) ...`; act writes pending flags; flush
  pending symbol; carry pending state and `run` to the neighbour; commit. Lists come from
  `Finset.univ.toList`. Correctness should be close to a case split on `M q a`.
- Main loop `when`-style on `run`; then the `Respects` / `tr_eval` ending as before.
Goal: each layer readable in one sitting. Size is secondary; compare against Golf (9629) afterwards.

Then Exposition = Elegant plus prose, worked example, and a discussion of the statement's scope
(TM0 vs partrec, two-sided tape, per-machine block code, right₀-only output, noncomputable compiler).
