import VersoManual
import Book
import Book.Theme
import Book.Widgets

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {(Book.Theme.css : CSS), (Book.Widgets.css : CSS)}
  extraJs := {(Book.Theme.js : JS)}

/-- The simulators' script is read when the book is generated, not when `Main` is compiled:
Lake does not track files pulled in with `include_str`, so an edit would not reach the book. -/
def main (args : List String) : IO UInt32 := do
  let sim ← IO.FS.readFile "sim/sim.js"
  manualMain (%doc Book) (options := args)
    (config := { config with extraJs := config.extraJs.insert (sim : JS) })
