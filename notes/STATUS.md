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

Current (chars / tokens): Reference = 38076 / 15793. Golf = 17572 / 9629 (v1 was 10472). Elegant = 25392 / 10204 (with docs). Exposition = 37571 / 14284 (prose throughout).

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

## Elegant (done, 2026-11-24): two layers, no offset arithmetic in the TM part
`BF.Elegant.claim : Claim` is proven (axioms: propext, Classical.choice, Quot.sound). No warnings of its own.
- `Elegant/Flags.lean` (Layer A): running BF code; flag programs `FProg F` (`skip | set | clr | shift |
  ⨾ | when`) with meaning `den : FProg F → Set (ℤ × F) → Option (Set (ℤ × F))` and derived forms
  (`all`, `hop`, with `den_all`/`den_when_on`/`den_when_off`/`den_hop`); flag sets on the tape (`Holds`,
  the only layout arithmetic is `cell_eq`); tapes of blocks (`block`, `holds_mk₁`, `right₀_eq`);
  the compiler and `compile_spec`, plus `loop_pass`/`loop_exit` (the compiled `when` as a while loop).
- `Elegant/Machine.lean` (Layer B): `Flag Γ Λ`, `pend` (flags a transition raises), `tapeSet`/`cfgSet`,
  then one section per phase (program followed by its `den` lemma), and `step_den`.
  Set equalities close by `flags` (ext, cases on the flag, simp, aesop).
- `Elegant/Main.lean`: the block code `enc = block ∘ symFlags`, main loop on `run`, `Tracks` +
  `Respects`, `eval_eq`, `claim`.
Possible further polish: `eval_eq` (Part.ext with `tr_eval`/`tr_eval_rev`, ~400 tokens).

## Exposition (done, 2026-11-24)
`BF.Exposition.claim` proven (standard axioms). Elegant's proof, plus:
- Computable compiler: `[FinEnum F]` instead of `[Fintype F]`; `Flag` derives `DecidableEq` and lists
  its flags via `FinEnum.ofList`; `block` takes `[DecidablePred S]`; classical decidability only in
  `den` (noncomputable, never run) and `Holds`. The claim builds `FinEnum` from `Fintype.equivFin`.
  Lesson: a file-wide `attribute [local instance] Classical.propDecidable` outranks FinEnum's
  `decEq` (priority 100) and silently makes defs noncomputable; keep it out of files with programs.
- Literate prose in every file (four-part reading order: Flags, Machine, Main, Example).
- `Example.lean`: swap-1↔2-and-rewind TM over `Fin 3`/`Fin 4`; compiles to 4058 chars of BF;
  `runBF`/`runTM` with fuel; `#guard` checks BF output = TM output on three inputs (runs in ~2 s).

## Verso book (`book/`, done, 2026-11-24)
- Separate Lake package requiring only `verso` @ `v4.36.0` (no Mathlib). Build: `cd book && lake exe book`
  (first build compiles Verso, ~10+ min; later ~1 min). Output: `book/_out/html-multi/`.
- Code is pulled from the main project via `-- ANCHOR: name` / `-- ANCHOR_END: name` comments
  (currently in `Exposition/Flags.lean`: FProg, den, compile, compile_spec), with
  `set_option verso.exampleProject "../"` and `verso.exampleModule`. The main repo requires `subverso`
  at the rev Verso pins (`no-modules/f9c40d40…`) for this. Anchor blocks must match the source text
  exactly; inline `{anchorTerm A}` must quote text that appears in anchor `A`.
- Four chapters (Flag Machines, One Step, The Whole Run, A Worked Example); code blocks generated from
  the anchors' exact text; `anchorInfo` blocks check the `#eval` outputs. Deployed by
  `.github/workflows/book.yml` to GitHub Pages (Pages source: GitHub Actions).
