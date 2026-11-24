# Status

`BF.simulates_TM0` / `BF.Reference.claim : BF.Claim` is proven (no sorry; axioms: propext, Classical.choice, Quot.sound).

## Layout
- `Core/` (frozen, shared, not counted): BF syntax + small-step semantics (`Basic.lean`); `BlockCode`, `encTape`, `Claim` (`Statement.lean`).
- `Reference/`: the original proof, plus tests (`Test.lean`, `CompileTest.lean`).
- `scripts/count.py`: non-whitespace characters (Unicode code points) and Lean tokens per version (tests excluded).

## Compression exercises
Each lives in its own folder and namespace and must end with `theorem ... : BF.Claim`.
Everything except `Core/` is free, including the compiler and the encoding.
Score = non-whitespace characters, comments included. Also tracked: Lean tokens (identifiers count 1 regardless of length).

1. `Golf/`: shortest possible, readability irrelevant.
2. `Exposition/`: most readable for humans, length irrelevant.
3. `Elegant/`: as short as possible while staying elegant and readable.

Baseline (chars / tokens): Reference = 38076 / 15793. Golf v1 (redesigned, not yet squashed) = 18711 / 10472.

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
