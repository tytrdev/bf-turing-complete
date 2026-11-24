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

/-- The full stylesheet: explicit choice first, then the OS preference when no choice is stored. -/
def css : String :=
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
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", addToggle);
  else addToggle();
})();
"#

end Book.Theme
