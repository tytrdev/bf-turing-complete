import VersoManual

/-!
# Dark mode for the HTML output

Verso's manual genre has no dark theme, but almost all of its colors are CSS variables
(`verso-vars.css`, `book.css`, the search and tooltip styles). This module overrides them, plus the
handful of rules in `book.css` that hardcode `black`/`white`.

The theme follows the reader's OS setting by default. A button in the header cycles
auto → light → dark and remembers the choice in `localStorage`, stored as `data-theme` on `<html>`.
Selectors are made more specific than Verso's own (`:root[...]`, `html[...] header`), so they win
regardless of where the inline `<style>` lands relative to the stylesheet links.
-/

namespace Book.Theme

open Verso.Genre.Manual

/-- Variable overrides for the dark palette. -/
def darkVars : String := r#"
    color-scheme: dark;
    --verso-background-color: #16181d;
    --verso-text-color: #d8dce3;
    --verso-code-color: #d8dce3;
    --verso-structure-color: #e8ebf0;
    --verso-muted-color: #9aa0aa;
    --verso-border-color: #3a3f4a;
    --verso-selected-color: #2a3d5c;
    --bf-link-color: #8ab4ff;
    --bf-link-visited-color: #c3a6ff;

    --verso-toc-background-color: #1c1f25;
    --verso-toc-border-color: #343842;
    --verso-toc-resize-handle-color: #6b7280;
    --verso-burger-toc-visible-shadow-color: #16181d;
    --verso-burger-toc-hidden-color: #d8dce3;
    --verso-burger-toc-hidden-shadow-color: #16181d;

    --verso-tooltip-color: #e0e3e8;
    --verso-tooltip-bg-color: #262a32;
    --verso-tooltip-border-color: #555b66;
    --verso-tooltip-separator-color: #444a55;

    --verso-code-hover-bg-color: #2c313a;
    --verso-code-info-hover-bg-color: #2c4580;
    --verso-info-indicator-color: #6b93ff;
    --verso-tooltip-info-border-color: #6b93ff;
    --verso-code-warning-hover-bg-color: #6b5418;
    --verso-tooltip-warning-border-color: #b8860b;
    --verso-code-error-hover-bg-color: #6e2a2a;
    --verso-error-indicator-color: #ff5c5c;
    --verso-message-error-color: #ff7b7b;
    --verso-tooltip-error-border-color: #a94442;

    --verso-tactic-state-color: #d8dce3;
    --verso-tactic-state-bg-color: #1c1f25;
    --verso-tactic-state-border-color: #555b66;
    --verso-tactic-toggle-color: #666b75;
    --verso-tactic-toggle-checked-color: #8a909b;

    --bf-accent: #8ea6ff;
    --bf-accent-2: #f0a35e;
    --bf-heading: #b4c3ff;
    --bf-code-bg: #1d2027;
    --bf-code-border: #2f343e;
    --bf-inline-bg: #262a33;
    --bf-output-edge: #4fbf8a;
    --bf-tok-keyword: #c792ea;
    --bf-tok-const: #82aaff;
    --bf-tok-var: #f6b26b;
    --bf-tok-literal: #a5d6a7;
    --bf-tok-sort: #f07178;
    --bf-tok-comment: #7f8796;
    --bf-tok-punct: #9aa3b2;
    --bf-bf-inc: #7fd17f;
    --bf-bf-dec: #ff8a80;
    --bf-bf-move: #82aaff;
    --bf-bf-loop: #d59cff;
"#

/-- Rules that Verso writes with literal colors, rewritten in terms of the variables. -/
def darkRules (sel : String) : String :=
  let r (s : String) := s.replace "$" sel
  r r#"
$ body { background-color: var(--verso-background-color); color: var(--verso-text-color); }
$ header { background: var(--verso-background-color); box-shadow: 0 0 6px #000; }
$ .header-title, $ .prev-next-buttons > * { color: var(--verso-structure-color); }
$ #toc a { color: var(--verso-text-color); }
$ #toc a:hover { color: #fff; }
$ #toc .split-toc label.toggle-split-toc::before { background-color: var(--verso-text-color); }
$ body:has(#toggle-toc:checked) .toc-backdrop { background-color: #0008; }
$ a { color: var(--bf-link-color); }
$ a:visited { color: var(--bf-link-visited-color); }
$ #toc a, $ #toc a:visited, $ .header-title, $ .header-title:visited { color: var(--verso-text-color); }
"#

/-- The light palette (the dark one is part of `darkVars`) and the styles that use it. -/
def style : String := r#"
:root {
  --bf-accent: #3451b2;
  --bf-accent-2: #d9822b;
  --bf-heading: #22357a;
  --bf-code-bg: #f6f7fb;
  --bf-code-border: #e1e5ef;
  --bf-inline-bg: #eef1f8;
  --bf-output-edge: #2f9e6b;
  --bf-tok-keyword: #8a2bb8;
  --bf-tok-const: #1d5fc4;
  --bf-tok-var: #a8520e;
  --bf-tok-literal: #127a50;
  --bf-tok-sort: #c2185b;
  --bf-tok-comment: #6b7280;
  --bf-tok-punct: #5b6472;
  --bf-bf-inc: #1f8a3b;
  --bf-bf-dec: #c62828;
  --bf-bf-move: #1d5fc4;
  --bf-bf-loop: #8a2bb8;
}

/* Reading comfort */
main p, main li { line-height: 1.65; }

/* Headings: chapter titles underlined in the accent color, sections with a side bar. */
main h1 { color: var(--bf-heading); border-bottom: 3px solid var(--bf-accent); padding-bottom: 0.3rem; }
main h2 { color: var(--bf-heading); border-left: 4px solid var(--bf-accent-2); padding-left: 0.6rem; margin-top: 2rem; }
main h3, main h4 { color: var(--bf-accent); }
header .header-title h1 { color: var(--bf-accent); }

/* Code blocks: a tinted panel with an accent edge; Lean's output with a green edge. */
main code.hl.lean.block, main pre {
  display: block; background: var(--bf-code-bg); border: 1px solid var(--bf-code-border);
  border-left: 3px solid var(--bf-accent); border-radius: 6px; padding: 0.7rem 0.9rem; overflow-x: auto;
}
main pre.hl.lean.lean-output { border-left-color: var(--bf-output-edge); margin-top: -0.4rem; }

/* Inline code as a soft chip. */
main :not(pre) > code:not(.block) {
  background: var(--bf-inline-bg); padding: 0.05em 0.35em; border-radius: 4px;
}

/* Lean syntax colors (Verso marks every token with its kind). */
.hl.lean .keyword.token { color: var(--bf-tok-keyword); font-weight: 600; }
.hl.lean .const.token, .hl.lean .module-name.token { color: var(--bf-tok-const); }
.hl.lean .var.token, .hl.lean .level-var.token { color: var(--bf-tok-var); }
.hl.lean .literal.token { color: var(--bf-tok-literal); }
.hl.lean .sort.token { color: var(--bf-tok-sort); }
.hl.lean .comment.token, .hl.lean .doc-comment.token { color: var(--bf-tok-comment); font-style: italic; }
.hl.lean .punctuation.token, .hl.lean .delim.token { color: var(--bf-tok-punct); }

/* Brainfuck snippets (see `js`): adds, subtracts, moves, loops. */
.bf-c-inc { color: var(--bf-bf-inc); font-weight: 600; }
.bf-c-dec { color: var(--bf-bf-dec); font-weight: 600; }
.bf-c-move { color: var(--bf-bf-move); }
.bf-c-loop { color: var(--bf-bf-loop); font-weight: 700; }
"#

/-- The full stylesheet: explicit choice first, then the OS preference when no choice is stored. -/
def css : String :=
  style ++
  ":root[data-theme=\"dark\"] {" ++ darkVars ++ "}\n" ++
  darkRules "html[data-theme=\"dark\"]" ++
  "@media (prefers-color-scheme: dark) {\n" ++
  ":root:not([data-theme=\"light\"]) {" ++ darkVars ++ "}\n" ++
  darkRules "html:not([data-theme=\"light\"])" ++ "}\n" ++
  r#"
:root { color-scheme: light dark; }
:root[data-theme="light"] { color-scheme: light; }
#bf-theme-toggle {
  /* Verso's search box is absolutely positioned at the header's right edge; sit left of it. */
  margin: 0 calc(var(--search-bar-width, 0px) + 1.5rem) 0 0.75rem; padding: 0.2rem 0.5rem; font-size: 1rem; line-height: 1;
  background: none; border: 1px solid var(--verso-border-color, #ccc); border-radius: 0.3rem;
  color: var(--verso-text-color, black); cursor: pointer; white-space: nowrap;
}
#bf-theme-toggle:hover { background: var(--verso-code-hover-bg-color, #eee); }
"#

/-- Applies the stored choice before first paint, then adds the toggle to the header. -/
def js : String := r#"
(function () {
  var KEY = "bf-book-theme", root = document.documentElement;
  function get() { try { return localStorage.getItem(KEY); } catch (e) { return null; } }
  function set(v) { try { v ? localStorage.setItem(KEY, v) : localStorage.removeItem(KEY); } catch (e) {} }
  function apply(v) { v ? root.setAttribute("data-theme", v) : root.removeAttribute("data-theme"); }
  apply(get());
  var labels = { "": "◐ Auto", "light": "☀ Light", "dark": "☾ Dark" };
  var next = { "": "light", "light": "dark", "dark": "" };
  function addToggle() {
    var header = document.querySelector("header");
    if (!header || document.getElementById("bf-theme-toggle")) return;
    var b = document.createElement("button");
    b.id = "bf-theme-toggle"; b.type = "button";
    function label() {
      var v = get() || "";
      b.textContent = labels[v];
      b.title = "Theme: " + (v || "follow system") + " (click to change)";
    }
    b.addEventListener("click", function () {
      var v = next[get() || ""]; set(v); apply(v); label();
    });
    label();
    header.appendChild(b);
  }
  // Color Brainfuck snippets in prose: inline code made only of BF instructions.
  var KIND = { "+": "inc", "-": "dec", "<": "move", ">": "move", "[": "loop", "]": "loop" };
  function colorBF() {
    document.querySelectorAll("main code:not(.hl)").forEach(function (c) {
      var t = c.textContent;
      if (!/^[+\-<>\[\]\s]+$/.test(t) || !/[+\-<>\[\]]/.test(t) || c.children.length) return;
      c.textContent = "";
      for (var i = 0; i < t.length; i++) {
        var k = KIND[t[i]];
        if (!k) { c.appendChild(document.createTextNode(t[i])); continue; }
        var s = document.createElement("span");
        s.className = "bf-c-" + k; s.textContent = t[i]; c.appendChild(s);
      }
    });
  }
  // Keyboard: ⌘K / Ctrl+K focuses the search box.
  function focusSearch() {
    var input = document.getElementById("cb1-input");
    if (!input) return;
    input.focus();
    var sel = window.getSelection(), range = document.createRange();
    range.selectNodeContents(input); sel.removeAllRanges(); sel.addRange(range);
  }
  document.addEventListener("keydown", function (e) {
    if (!(e.metaKey || e.ctrlKey) || e.altKey || e.shiftKey) return;
    if (e.key.toLowerCase() === "k") { e.preventDefault(); focusSearch(); }
  });
  function hints() {
    var mac = /Mac|iPhone|iPad/.test(navigator.platform), mod = mac ? "⌘" : "Ctrl+";
    var input = document.getElementById("cb1-input");
    if (input) input.title = "Search (" + mod + "K)";
  }
  function init() { addToggle(); colorBF(); hints(); setTimeout(hints, 500); }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init);
  else init();
})();
"#

end Book.Theme
