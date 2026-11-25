/*
 * Brainfuck simulators for the book.
 *
 * The interpreter follows `BfTuringComplete/Core/Basic.lean` exactly: 8-bit wrapping cells, a tape
 * unbounded both ways, and Lean's step counting (a loop's `[` check is one step; jumping back from
 * `]` is free, because in Lean a loop unrolls its body in front of itself). `book/test/golden.mjs`
 * checks it against the trace Lean exports (`scripts/ExportTrace.lean`), step for step.
 *
 * Widgets (mounted on page load):
 *   <div class="bf-playground" data-program="..." data-input="1 2 3"></div>
 *   <div class="bf-player" data-trace="ID"></div> with <script type="application/json" id="ID">.
 */
(function (root) {
  "use strict";

  // ---------- Brainfuck core ----------

  function parse(src) {
    const code = [];
    const stack = [];
    for (const ch of src) {
      if ("+-<>[]".indexOf(ch) < 0) continue;
      const i = code.length;
      code.push({ op: ch, jump: -1, depth: stack.length });
      if (ch === "[") stack.push(i);
      else if (ch === "]") {
        if (!stack.length) throw new Error("unmatched ]");
        const j = stack.pop();
        code[j].jump = i;
        code[i].jump = j;
        code[i].depth = stack.length;
      }
    }
    if (stack.length) throw new Error("unmatched [");
    return code;
  }

  class Machine {
    constructor(src, input) {
      this.code = parse(src);
      this.reset(input || []);
    }
    reset(input) {
      this.tape = new Map();
      (input || []).forEach((v, i) => this.set(i, v));
      this.ptr = 0;
      this.pc = 0;
      this.steps = 0;
      this.settle();
    }
    get(i) { return this.tape.get(i) || 0; }
    set(i, v) {
      v = ((v % 256) + 256) % 256;
      if (v) this.tape.set(i, v); else this.tape.delete(i);
    }
    /** Follow `]` back to its `[` (free in Lean's semantics). */
    settle() {
      while (this.pc < this.code.length && this.code[this.pc].op === "]") this.pc = this.code[this.pc].jump;
    }
    halted() { return this.pc >= this.code.length; }
    step() {
      if (this.halted()) return false;
      const ins = this.code[this.pc];
      switch (ins.op) {
        case "+": this.set(this.ptr, this.get(this.ptr) + 1); this.pc++; break;
        case "-": this.set(this.ptr, this.get(this.ptr) - 1); this.pc++; break;
        case "<": this.ptr--; this.pc++; break;
        case ">": this.ptr++; this.pc++; break;
        case "[": this.pc = this.get(this.ptr) === 0 ? ins.jump + 1 : this.pc + 1; break;
      }
      this.steps++;
      this.settle();
      return true;
    }
    window(lo, n) {
      const a = [];
      for (let i = 0; i < n; i++) a.push(this.get(lo + i));
      return a;
    }
  }

  /** Index of the last top-level `[`: the compiled program's main loop. */
  function mainLoopIndex(code) {
    let k = -1;
    code.forEach((ins, i) => { if (ins.op === "[" && ins.depth === 0) k = i; });
    return k;
  }

  const api = { parse, Machine, mainLoopIndex };
  if (typeof module !== "undefined" && module.exports) { module.exports = api; return; }
  root.BFSim = api;

  // ---------- DOM helpers ----------

  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function button(label, onClick) {
    const b = el("button", "bf-btn", label);
    b.type = "button";
    b.addEventListener("click", onClick);
    return b;
  }

  // ---------- Playground ----------

  function mountPlayground(host) {
    const program = host.dataset.program || "";
    const inputText = host.dataset.input || "";
    host.innerHTML = "";
    const src = el("textarea", "bf-src");
    src.value = program;
    src.spellcheck = false;
    const inp = el("input", "bf-in");
    inp.value = inputText;
    inp.placeholder = "starting cells, e.g. 3 5";
    const codeView = el("div", "bf-code");
    const tapeView = el("div", "bf-tape");
    const status = el("div", "bf-status");
    const speed = el("input", "bf-speed");
    speed.type = "range"; speed.min = "0"; speed.max = "4"; speed.value = "1";
    let m = null, timer = null;

    function load() {
      stop();
      try {
        const input = inp.value.trim() ? inp.value.trim().split(/[\s,]+/).map(Number) : [];
        m = new Machine(src.value, input);
        status.textContent = "";
      } catch (e) { m = null; status.textContent = "Error: " + e.message; }
      render();
    }
    function render() {
      codeView.innerHTML = "";
      tapeView.innerHTML = "";
      if (!m) return;
      m.code.forEach((ins, i) => {
        const s = el("span", "bf-op" + (i === m.pc ? " bf-pc" : ""), ins.op);
        codeView.appendChild(s);
      });
      if (m.halted()) codeView.appendChild(el("span", "bf-op bf-pc", "■"));
      const lo = Math.min(-2, m.ptr - 6), hi = Math.max(12, m.ptr + 6);
      for (let i = lo; i <= hi; i++) {
        const c = el("div", "bf-cell" + (i === m.ptr ? " bf-ptr" : "") + (m.get(i) ? " bf-nz" : ""));
        c.appendChild(el("div", "bf-val", String(m.get(i))));
        c.appendChild(el("div", "bf-idx", String(i)));
        tapeView.appendChild(c);
      }
      status.textContent = (m.halted() ? "Halted" : "Running") + " · " + m.steps + " steps";
    }
    function tick() {
      if (!m || m.halted()) return stop();
      const per = [1, 1, 10, 100, 10000][+speed.value];
      for (let i = 0; i < per && !m.halted(); i++) m.step();
      render();
    }
    function stop() { if (timer) clearInterval(timer); timer = null; }
    function run() {
      stop();
      const delay = [300, 60, 30, 30, 30][+speed.value];
      timer = setInterval(tick, delay);
    }

    const controls = el("div", "bf-controls");
    controls.append(
      button("Step", () => { if (m) { m.step(); render(); } }),
      button("Run", run), button("Pause", stop), button("Reset", load),
      el("span", "bf-label", "speed"), speed);
    const top = el("div", "bf-row");
    top.append(el("span", "bf-label", "input"), inp);
    host.append(src, top, controls, codeView, tapeView, status);
    src.addEventListener("change", load);
    inp.addEventListener("change", load);
    load();
  }

  // ---------- Worked-example player ----------

  const FLAG_COLORS = {
    sym: "#4c8bf5", state: "#e8a33d", blank: "#888", write: "#3dbb7a",
    next: "#c45dd8", left: "#e05555", right: "#e05555", run: "#d4c13a",
  };

  function mountPlayer(host) {
    const data = JSON.parse(document.getElementById(host.dataset.trace).textContent);
    const W = data.width, lo = data.windowStart;
    const nBlocks = data.passes[0].tape.length / W;
    host.innerHTML = "";

    const tmView = el("div", "bf-tm");
    const bfView = el("div", "bf-blocks");
    const legend = el("div", "bf-legend");
    const status = el("div", "bf-status");
    const slider = el("input", "bf-slider");
    slider.type = "range"; slider.min = "0"; slider.max = String(data.passes.length - 1); slider.value = "0";
    let k = 0, live = null, timer = null;

    data.layout.forEach((name) => {
      const kind = name.split(" ")[0];
      const item = el("span", "bf-legend-item");
      const sw = el("span", "bf-swatch");
      sw.style.background = FLAG_COLORS[kind] || "#999";
      item.append(sw, document.createTextNode(name));
      legend.appendChild(item);
    });

    function tmAt(i) { return data.tm[Math.min(i, data.tm.length - 1)]; }

    function drawTM(i) {
      const c = tmAt(i);
      tmView.innerHTML = "";
      const label = el("div", "bf-tm-label",
        i < data.tm.length ? `Turing machine · step ${i} · state ${c.q}` : `Turing machine · halted · state ${c.q}`);
      const row = el("div", "bf-tm-row");
      c.tape.forEach((s, j) => {
        const pos = j - 2;
        row.appendChild(el("div", "bf-tm-cell" + (pos === c.head ? " bf-ptr" : ""), s === 0 ? "·" : String(s)));
      });
      tmView.append(label, row);
    }

    function drawBF(tape, ptr, stepNo, note) {
      bfView.innerHTML = "";
      for (let b = 0; b < nBlocks; b++) {
        const blk = el("div", "bf-block");
        const start = lo + b * W;
        if (ptr >= start && ptr < start + W) blk.classList.add("bf-block-head");
        for (let f = 0; f < W; f++) {
          const v = tape[b * W + f];
          const cell = el("div", "bf-flag");
          cell.title = `${data.layout[f]} = ${v}`;
          if (v) cell.style.background = FLAG_COLORS[data.layout[f].split(" ")[0]] || "#999";
          if (start + f === ptr) cell.classList.add("bf-flag-ptr");
          blk.appendChild(cell);
        }
        blk.appendChild(el("div", "bf-idx", String(b - 2)));
        bfView.appendChild(blk);
      }
      status.textContent = `Brainfuck · step ${stepNo} of ${data.bfSteps}` + (note ? " · " + note : "");
    }

    function show(i) {
      stopLive();
      k = i;
      slider.value = String(i);
      drawTM(i);
      const p = data.passes[i];
      drawBF(p.tape, p.head, p.step, i === data.passes.length - 1 ? "loop exits, program halts" : "top of the main loop");
    }

    function stopLive() { if (timer) clearInterval(timer); timer = null; live = null; }

    /** Run the real interpreter from pass k to pass k+1, then check it against Lean's trace. */
    function playToNext() {
      if (k >= data.passes.length - 1) return;
      stopLive();
      const m = new Machine(data.program, data.encodedInput);
      const target = data.passes[k];
      while (m.steps < target.step) m.step();
      const end = data.passes[k + 1];
      live = m;
      timer = setInterval(() => {
        for (let i = 0; i < 25 && m.steps < end.step; i++) m.step();
        drawBF(m.window(lo, nBlocks * W), m.ptr, m.steps, "running");
        if (m.steps >= end.step) {
          clearInterval(timer); timer = null;
          const ok = JSON.stringify(m.window(lo, nBlocks * W)) === JSON.stringify(end.tape) && m.ptr === end.head;
          k = k + 1;
          slider.value = String(k);
          drawTM(k);
          drawBF(end.tape, end.head, end.step, ok ? "✓ matches Lean's trace" : "✗ differs from Lean's trace");
        }
      }, 30);
    }

    const PHASE_TEXT = {
      dispatch: "dispatch: find the raised state flag, read the symbol, raise the flags for what to do",
      write: "write: replace the symbol with the one the rule says to write",
      move: "move: carry the pending flags one block left or right",
      commit: "commit: turn the pending next-state flag into the new state flag",
    };
    let ph = -1; // index into data.phases of the last phase shown
    /** Run the real interpreter to the next phase boundary and check it against Lean's tape. */
    function playPhase() {
      stopLive();
      const cur = ph >= 0 ? data.phases[ph].step : data.passes[k].step;
      let j = data.phases.findIndex((x) => x.step > cur);
      if (j < 0) return;
      const target = data.phases[j];
      const m = new Machine(data.program, data.encodedInput);
      while (m.steps < cur) m.step();
      timer = setInterval(() => {
        for (let i = 0; i < 6 && m.steps < target.step; i++) m.step();
        drawBF(m.window(lo, nBlocks * W), m.ptr, m.steps, "running toward " + target.phase);
        if (m.steps >= target.step) {
          clearInterval(timer); timer = null;
          const ok = JSON.stringify(m.window(lo, nBlocks * W)) === JSON.stringify(target.tape) && m.ptr === target.head;
          ph = j;
          let pass = 0;
          data.passes.forEach((p, i) => { if (p.step <= target.step) pass = i; });
          k = pass; slider.value = String(k); drawTM(k);
          drawBF(target.tape, target.head, target.step,
            PHASE_TEXT[target.phase] + (ok ? " · ✓ matches Lean" : " · ✗ differs from Lean"));
        }
      }, 30);
    }

    const controls = el("div", "bf-controls");
    controls.append(
      button("◀ Prev", () => { ph = -1; show(Math.max(0, k - 1)); }),
      button("Next ▶", () => { ph = -1; show(Math.min(data.passes.length - 1, k + 1)); }),
      button("Run Brainfuck to next step", () => { ph = -1; playToNext(); }));
    if (host.dataset.phases !== undefined) controls.append(button("Next phase ▶", playPhase));
    controls.append(slider);
    slider.addEventListener("input", () => { ph = -1; show(+slider.value); });
    host.append(tmView, controls, bfView, status, legend);
    show(0);
  }

  // ---------- Turing machine stepper ----------

  function mountStepper(host) {
    const data = JSON.parse(document.getElementById(host.dataset.trace).textContent);
    host.innerHTML = "";
    const table = el("table", "bf-rules");
    const tapeRow = el("div", "bf-tm-row");
    const label = el("div", "bf-tm-label");
    const caption = el("div", "bf-status");
    let i = 0;
    const head = el("tr");
    head.appendChild(el("th", "", "state \\ reads"));
    ["0 (blank)", "1", "2"].forEach((h) => head.appendChild(el("th", "", h)));
    table.appendChild(head);
    const cells = data.rules.map((row, q) => {
      const tr = el("tr");
      tr.appendChild(el("th", "", String(q)));
      const tds = row.map((r) => { const td = el("td", "", r); tr.appendChild(td); return td; });
      table.appendChild(tr);
      return tds;
    });
    function draw() {
      const c = data.tm[i];
      const sym = c.tape[c.head + 2];
      label.textContent = `step ${i} · state ${c.q}` + (i === data.tm.length - 1 ? " · halted" : "");
      tapeRow.innerHTML = "";
      c.tape.forEach((s, j) => tapeRow.appendChild(
        el("div", "bf-tm-cell" + (j - 2 === c.head ? " bf-ptr" : ""), s === 0 ? "·" : String(s))));
      cells.forEach((row, q) => row.forEach((td, a) => td.classList.toggle("bf-rule-now", q === c.q && a === sym)));
      const rule = data.rules[c.q][sym];
      caption.textContent = rule === "halt"
        ? `In state ${c.q} reading ${sym}: no rule, so the machine halts. The tape is the output.`
        : `In state ${c.q} reading ${sym}: ${rule}.`;
    }
    const controls = el("div", "bf-controls");
    controls.append(
      button("◀ Back", () => { i = Math.max(0, i - 1); draw(); }),
      button("Step ▶", () => { i = Math.min(data.tm.length - 1, i + 1); draw(); }),
      button("Reset", () => { i = 0; draw(); }));
    host.append(label, tapeRow, caption, controls, table);
    draw();
  }

  // ---------- Encoding view ----------

  function mountEncoding(host) {
    const data = JSON.parse(document.getElementById(host.dataset.trace).textContent);
    const W = data.width;
    host.innerHTML = "";
    const row = el("div", "bf-enc");
    const syms = data.input.concat([0, 0]);
    syms.forEach((a, b) => {
      const col = el("div", "bf-enc-col");
      col.appendChild(el("div", "bf-tm-cell", a === 0 ? "·" : String(a)));
      col.appendChild(el("div", "bf-enc-arrow", "↓"));
      const blk = el("div", "bf-block");
      for (let f = 0; f < W; f++) {
        const v = b < data.input.length ? data.encodedInput[b * W + f] : 0;
        const cell = el("div", "bf-flag");
        cell.title = `${data.layout[f]} = ${v}`;
        if (v) cell.style.background = FLAG_COLORS[data.layout[f].split(" ")[0]];
        blk.appendChild(cell);
      }
      col.appendChild(blk);
      col.appendChild(el("div", "bf-idx", `cells ${b * W}–${b * W + W - 1}`));
      row.appendChild(col);
    });
    // Flag names: a column built like the others (same spacers, same cell boxes), so rows line up.
    const names = el("div", "bf-enc-col");
    const sp1 = el("div", "bf-tm-cell", "·"); sp1.style.visibility = "hidden";
    const sp2 = el("div", "bf-enc-arrow", "↓"); sp2.style.visibility = "hidden";
    const nblk = el("div", "bf-block");
    data.layout.forEach((n) => nblk.appendChild(el("div", "bf-flag bf-enc-name", n)));
    names.append(sp1, sp2, nblk);
    row.appendChild(names);
    host.append(row);
  }

  function mountAll() {
    document.querySelectorAll(".bf-playground").forEach(mountPlayground);
    document.querySelectorAll(".bf-player").forEach(mountPlayer);
    document.querySelectorAll(".bf-stepper").forEach(mountStepper);
    document.querySelectorAll(".bf-encoding").forEach(mountEncoding);
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", mountAll);
  else mountAll();
})(typeof window !== "undefined" ? window : globalThis);
