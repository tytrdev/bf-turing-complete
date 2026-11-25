import VersoManual

/-!
# Interactive widgets

`sim/sim.js` (loaded by `Main` when the book is generated) holds a Brainfuck interpreter (tested against Lean's own runs by `test/golden.mjs`)
and two widgets; this module gives the book code blocks that place them on a page.

* ` ```bfPlayground ` with the program as its body: an editable Brainfuck playground.
  An optional first line `input: 1 2 3` sets the starting cells.
* ` ```bfPlayer ` with a path to a trace exported by `scripts/ExportTrace.lean`: the worked
  example's Turing machine and its compiled Brainfuck program, side by side.
-/

open Lean Elab
open Verso Doc Elab Genre.Manual Html ArgParse
open Verso.Output

namespace Book.Widgets

-- Raw HTML, emitted as is in HTML output and dropped from TeX.
block_extension Block.rawHtml (html : String) where
  data := .str html
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ data _ => do
    let .str s := data | pure .empty
    pure (Html.raw s)
  toTeX := some fun _ _ _ _ _ => pure .empty

/-- Escape text for an HTML attribute. -/
def attr (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "\"" "&quot;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

@[code_block]
def bfPlayground : CodeBlockExpanderOf Unit
  | (), str => do
    let lines := str.getVersoCodeBlock.splitOn "\n"
    let (input, prog) := match lines with
      | l :: rest => if l.startsWith "input:" then ((l.drop 6).trimAscii.toString, rest) else ("", lines)
      | [] => ("", [])
    let html := s!"<div class=\"bf-playground\" data-program=\"{attr ("\n".intercalate prog).trimAscii.toString}\" data-input=\"{attr input}\"></div>"
    ``(Verso.Doc.Block.other (Block.rawHtml $(quote html)) #[])

/-- A trace-driven widget: the body is the trace's path; `cls` the widget class. -/
def traceWidget (cls : String) (extra : String) (str : VersoCodeBlock) : DocElabM Term := do
  let path := str.getVersoCodeBlock.trimAscii.toString
  let json ← IO.FS.readFile path
  let id := "trace-" ++ toString (hash (path ++ cls ++ extra))
  let html := s!"<script type=\"application/json\" id=\"{id}\">{json.replace "</" "<\\/"}</script>" ++
    s!"<div class=\"{cls}\" data-trace=\"{id}\"{extra}></div>"
  ``(Verso.Doc.Block.other (Block.rawHtml $(quote html)) #[])

/-- The worked example, Turing machine and Brainfuck side by side. -/
@[code_block]
def bfPlayer : CodeBlockExpanderOf Unit
  | (), str => traceWidget "bf-player" "" str

/-- The same, with a button that runs to the next phase of a step. -/
@[code_block]
def bfPhases : CodeBlockExpanderOf Unit
  | (), str => traceWidget "bf-player" " data-phases" str

/-- The worked example's Turing machine alone: rule table, tape, one rule at a time. -/
@[code_block]
def tmStepper : CodeBlockExpanderOf Unit
  | (), str => traceWidget "bf-stepper" "" str

/-- The worked example's input tape next to its encoding as Brainfuck blocks. -/
@[code_block]
def encoding : CodeBlockExpanderOf Unit
  | (), str => traceWidget "bf-encoding" "" str

/-- Escape text for HTML element content. -/
def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- A "pause and predict" question: first line the question, the rest the answer (folded). -/
@[code_block]
def predict : CodeBlockExpanderOf Unit
  | (), str => do
    let lines := str.getVersoCodeBlock.trimAscii.toString.splitOn "\n"
    let q := lines.headD ""
    let a := "\n".intercalate (lines.drop 1)
    let html := s!"<details class=\"bf-predict\"><summary><strong>Pause and predict.</strong> {esc q}</summary>" ++
      s!"<p>{esc a.trimAscii.toString}</p></details>"
    ``(Verso.Doc.Block.other (Block.rawHtml $(quote html)) #[])

/-- Styles for the widgets, in terms of Verso's (and the dark theme's) color variables. -/
def css : String := r#"
.bf-playground, .bf-player, .bf-stepper, .bf-encoding {
  border: 1px solid var(--verso-border-color, #ccc); border-radius: 6px; padding: 0.8rem;
  margin: 1rem 0; font-size: 0.9rem; background: var(--verso-background-color, #fff);
  font-family: var(--verso-text-font-family, sans-serif);
}
.bf-playground button, .bf-playground input, .bf-player button, .bf-stepper button { font-family: inherit; font-size: 0.85rem; }
.bf-src {
  width: 100%; min-height: 4rem; box-sizing: border-box; font-family: var(--verso-code-font-family, monospace);
  background: var(--verso-tactic-state-bg-color, #f7f7f7); color: var(--verso-code-color, inherit);
  border: 1px solid var(--verso-border-color, #ccc); border-radius: 4px; padding: 0.4rem;
}
.bf-row, .bf-controls { display: flex; gap: 0.5rem; align-items: center; flex-wrap: wrap; margin: 0.4rem 0; }
.bf-in { flex: 1; min-width: 8rem; font-family: var(--verso-code-font-family, monospace); }
.bf-label { color: var(--verso-muted-color, #666); font-size: 0.8rem; }
.bf-btn {
  padding: 0.2rem 0.6rem; border: 1px solid var(--verso-border-color, #ccc); border-radius: 4px;
  background: none; color: var(--verso-text-color, inherit); cursor: pointer;
}
.bf-btn:hover { background: var(--verso-code-hover-bg-color, #eee); }
.bf-code {
  font-family: var(--verso-code-font-family, monospace); word-break: break-all; max-height: 6rem;
  overflow-y: auto; margin: 0.4rem 0; line-height: 1.5;
}
.bf-op.bf-pc { background: #e8a33d; color: #000; border-radius: 2px; }
.bf-tape { display: flex; gap: 2px; overflow-x: auto; padding: 0.3rem 0; }
.bf-cell {
  min-width: 2.2rem; text-align: center; border: 1px solid var(--verso-border-color, #ccc);
  border-radius: 3px; padding: 0.15rem 0;
}
.bf-cell.bf-nz { background: rgba(76, 139, 245, 0.18); }
.bf-cell.bf-ptr, .bf-tm-cell.bf-ptr { outline: 2px solid #e8a33d; }
.bf-val { font-family: var(--verso-code-font-family, monospace); }
.bf-idx { font-size: 0.65rem; color: var(--verso-muted-color, #888); text-align: center; }
.bf-status { color: var(--verso-muted-color, #666); font-size: 0.8rem; margin-top: 0.3rem; }
.bf-tm-label { font-weight: 600; margin-bottom: 0.3rem; }
.bf-tm-row { display: flex; gap: 4px; }
.bf-tm-cell {
  width: 2rem; height: 2rem; display: flex; align-items: center; justify-content: center;
  border: 1px solid var(--verso-border-color, #ccc); border-radius: 4px; font-family: var(--verso-code-font-family, monospace);
}
.bf-blocks { display: flex; gap: 4px; overflow-x: auto; padding: 0.4rem 0; }
.bf-block { display: flex; flex-direction: column; gap: 1px; padding: 2px; border-radius: 3px; border: 1px solid transparent; }
.bf-block-head { border-color: #e8a33d; }
.bf-flag { width: 0.9rem; height: 0.55rem; border: 1px solid var(--verso-border-color, #ccc); border-radius: 1px; }
.bf-flag-ptr { outline: 2px solid var(--verso-text-color, #000); }
.bf-slider { flex: 1; min-width: 8rem; }
.bf-legend { display: flex; flex-wrap: wrap; gap: 0.2rem 0.8rem; font-size: 0.75rem; color: var(--verso-muted-color, #666); margin-top: 0.4rem; }
.bf-legend-item { display: inline-flex; align-items: center; gap: 0.25rem; }
.bf-rules { border-collapse: collapse; margin-top: 0.6rem; font-size: 0.85rem; }
.bf-rules th, .bf-rules td { border: 1px solid var(--verso-border-color, #ccc); padding: 0.2rem 0.5rem; text-align: left; }
.bf-rules td.bf-rule-now { background: rgba(232, 163, 61, 0.35); font-weight: 600; }
.bf-enc { display: flex; gap: 0.8rem; }
.bf-enc-col { display: flex; flex-direction: column; align-items: center; gap: 0.2rem; }
.bf-enc-arrow { color: var(--verso-muted-color, #888); }
.bf-enc-col .bf-flag { width: 1.6rem; height: 0.8rem; }
.bf-enc-col .bf-flag.bf-enc-name {
  width: auto; border-color: transparent; font-size: 0.62rem; line-height: 0.8rem;
  color: var(--verso-muted-color, #666); white-space: nowrap;
}
.bf-predict { border-left: 3px solid #e8a33d; padding: 0.3rem 0.8rem; margin: 1rem 0; background: rgba(232, 163, 61, 0.08); border-radius: 0 4px 4px 0; }
.bf-predict summary { cursor: pointer; }
.bf-predict p { margin: 0.5rem 0 0.2rem; }
.bf-swatch { width: 0.7rem; height: 0.7rem; border-radius: 2px; display: inline-block; }
"#

end Book.Widgets
