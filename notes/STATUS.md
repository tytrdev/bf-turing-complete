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
- Dark mode: `book/Book/Theme.lean`, wired in via `extraCss`/`extraJs` in `book/Main.lean`. Overrides Verso's
  CSS variables plus the few hardcoded colors in `book.css`; follows the OS setting, with a header button
  cycling auto/light/dark (stored in `localStorage`). Verso's search box is absolutely positioned at the
  header's right edge, so the button carries a right margin of `--search-bar-width`.

## Mathlib fingerprint pass over Elegant (2026-11-25)
Run: fingerprint tool rebuilt for v4.36.0 (`lean-explorer/corpus/tools/fingerprint436`), all of Mathlib + this
project in one run (`corpus/data/bf/folded.jsonl`); `corpus/tools/reprove/Triage.lean` tries each Elegant theorem's
statement with rfl/simp/omega/aesop/grind/exact? (rejecting proofs that use the theorem itself).
- Term-level matches with Mathlib: only compiler output (equation lemmas, omega certificates).
- Triage of 60 Elegant theorems: `card_pos` is `Fintype.card_pos`; the `den_*` equations and `compile_when`
  are one-line `simp`/`aesop`; the other 48 need their proofs.
- Shared-premise search finds nothing useful: our premises are generic glue.
- What matters (found by reading Mathlib, not by the fingerprints): `Turing.TM0to1` (TM0 -> TM1) and
  `Turing.TM1to1` (TM1 over Γ -> TM1 over Bool, symbols as fixed-width bit blocks with
  `enc default = replicate n false`, i.e. our BlockCode conditions). A version where BF only simulates
  *binary TM1* would drop the whole symbol layer (one-hot symbol flags, symbol dispatch, pending-symbol
  flush) and leave states, one bit read/write, and moves.

## Binary reduction (2026-11-25): `Binary/Reduce.lean`
`BF.Binary.claim_of_binary : BinaryClaim.{max u v} → Claim.{u, v}` is proven (axioms: propext, Classical.choice,
Quot.sound): if BF simulates every finite TM0 over `Bool`, it simulates every finite TM0. Chain:
`TM0to1` → `TM1to1` (symbols as bit blocks via `exists_enc_dec`) → `TM1to0` → restrict to the reachable
states (`TM0.Machine.map` onto `{q // q ∈ insert default S}`); the block code for Γ is "bits of the symbol,
each bit a binary block" (`compose`). 2,128 tokens with docs; built by `lake build` (imported from the root).
- About 1,180 of those tokens are generic and missing from Mathlib: an `eval` lemma along any `Respects`
  across universes (`eval_map`), `TM0to1` eval + finiteness, `TM1to1` eval, eval after restricting to a support.
  BF-specific part: about 940 (statement, `compose`, final chain).
- Verdict: a Bool-only compiler would save less than the reduction costs. Elegant's symbol handling is
  already generic (`all fun a ↦ ...`), so fixing Γ = Bool trims a few hundred tokens, not a layer.
  The reduction is still a clean, readable module, and the generic part is a Mathlib contribution candidate.

## Book: two parts and simulators (2026-11-25)
- One book, two parts: *Part I. The Tour* (`book/Book/Tour.lean`, for programmers with no background; so far
  chapter 1, "Brainfuck in Five Minutes") and *Part II. The Proof* (`book/Book/Proof.lean`, the four existing
  chapters). URLs `/tour/...` and `/proof/...` (`file :=` metadata).
- Widgets (`book/Book/Widgets.lean`, a raw-HTML `block_extension` plus code blocks): ```` ```bfPlayground ````
  (editable program, optional `input:` line) and ```` ```bfPlayer ```` (path to an exported trace).
  JS in `book/sim/sim.js` (pulled in with `include_str`), styles use Verso's color variables (dark mode works).
- Truthfulness: Lean produces the data, JS animates it. `scripts/ExportTrace.lean` (run from the root)
  writes `book/data/swap-trace.json` from the real compiled program. `book/test/golden.mjs` (node) checks the JS
  interpreter reproduces Lean's run exactly: 13 passes, 9709 steps, tape and pointer at every pass. In the page,
  "Run Brainfuck to next step" runs the program live and compares with Lean's tape (shows ✓).
- Tour, 8 chapters: Brainfuck in five minutes (playgrounds); Turing machines (`tmStepper`); What we claim (the full
  `Core/Statement.lean` via Verso's `module` block, checked against the source); Spelling a tape (`encoding`); A tiny
  language of flags (playgrounds of compiled flag programs); One step in four phases (`bfPhases`, each phase run live
  and checked against Lean's tape at that moment); The whole run (`bfPlayer`); What Lean checked and what you trust.
  "Pause and predict" fold-outs (```` ```predict ````: first line question, rest answer).
- Phase boundaries in the trace: the code left to run is not enough on its own (just after a `when` body, the code
  left equals `mv (pos f) ++ [loop ..] ++ ..` again), so phases are matched in order after each loop top.
- CI (`.github/workflows/book.yml`): regenerates the trace and fails if `book/data` differs, runs the golden test
  (13 passes, 48 phase starts, 9709 steps), then builds the book.
- Preview locally: `cd book && lake exe book`, then serve `_out/html-multi` (e.g. `python3 -m http.server --directory _out/html-multi`).
