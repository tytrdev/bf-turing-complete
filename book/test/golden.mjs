// Golden test: the book's JS interpreter must reproduce Lean's run of the worked example exactly.
// Run from book/: node test/golden.mjs   (regenerate the trace with `lake env lean scripts/ExportTrace.lean`
// from the project root).
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";

const require = createRequire(import.meta.url);
const { Machine, mainLoopIndex } = require("../sim/sim.js");
const data = JSON.parse(readFileSync(new URL("../data/swap-trace.json", import.meta.url)));

const m = new Machine(data.program, data.encodedInput);
const main = mainLoopIndex(m.code);
const len = data.passes[0].tape.length;
const passes = [];
const phaseAt = new Map(data.phases.map((p) => [p.step, p]));
let phasesChecked = 0;
for (;;) {
  if (m.pc === main) passes.push({ step: m.steps, head: m.ptr, tape: m.window(data.windowStart, len) });
  const ph = phaseAt.get(m.steps);
  if (ph) {
    phasesChecked++;
    if (ph.head !== m.ptr || JSON.stringify(ph.tape) !== JSON.stringify(m.window(data.windowStart, len)))
      { console.error(`FAIL: phase ${ph.phase} at step ${ph.step} differs`); process.exitCode = 1; }
  }
  if (!m.step()) break;
}

let failures = 0;
const check = (cond, msg) => { if (!cond) { failures++; console.error("FAIL:", msg); } };
check(passes.length === data.passes.length, `passes ${passes.length} vs ${data.passes.length}`);
passes.forEach((p, i) => {
  const q = data.passes[i];
  if (!q) return;
  check(p.step === q.step, `pass ${i}: step ${p.step} vs ${q.step}`);
  check(p.head === q.head, `pass ${i}: head ${p.head} vs ${q.head}`);
  check(JSON.stringify(p.tape) === JSON.stringify(q.tape), `pass ${i}: tape differs`);
});
check(m.steps === data.bfSteps, `total steps ${m.steps} vs ${data.bfSteps}`);
check(JSON.stringify(m.window(data.windowStart, len)) === JSON.stringify(data.final), "final tape differs");
check(phasesChecked === data.phases.length, `phases checked ${phasesChecked} vs ${data.phases.length}`);
console.log(failures ? `${failures} failures` : `ok: ${passes.length} passes, ${phasesChecked} phase starts, ${m.steps} steps match Lean`);
process.exit(failures || process.exitCode ? 1 : 0);
