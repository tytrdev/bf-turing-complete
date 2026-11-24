import VersoManual
import Book
import Book.Theme

open Verso Doc
open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := {(Book.Theme.css : CSS)}
  extraJs := {(Book.Theme.js : JS)}

def main := manualMain (%doc Book) (config := config)
