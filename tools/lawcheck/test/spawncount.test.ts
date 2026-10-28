// Regression: the checker's batch size is fixed and independent of --jobs, so
// `checkerRuns` must not grow when more cores are offered (the old
// `min(50, items/jobs)` shrank batches as jobs grew and multiplied spawns).
import { expect, test } from "bun:test";
import * as path from "node:path";
import { defaultJobs, runBounded } from "../src/checker.ts";
import { lawcheck } from "../src/lawcheck.ts";

const FX = path.join(import.meta.dir, "fixtures");
const T = 180_000;
const runsAt = (fixture: string, jobs: number) =>
  lawcheck(path.join(FX, fixture), { maxInstances: 100, jobs, seed: 1, size: 3, shrink: false });

test("checkerRuns is decoupled from --jobs and stays low", async () => {
  const base = await runsAt("correct.bend", 4);
  const many = await runsAt("correct.bend", 16);
  expect(many.checkerRuns).toBeLessThanOrEqual(base.checkerRuns);
  expect(base.checkerRuns).toBeLessThanOrEqual(80);
}, T);

test("a false law is still caught and counted (no hidden counterexample)", async () => {
  const base = await runsAt("buggy.bend", 4);
  const many = await runsAt("buggy.bend", 16);
  expect(base.laws.some((l) => l.status === "fail")).toBe(true);
  expect(many.laws.some((l) => l.status === "fail")).toBe(true);
  expect(many.checkerRuns).toBeLessThanOrEqual(base.checkerRuns);
}, T);

test("the default --jobs runs at most 4 bend processes, however many cores the machine has", () => {
  const j = defaultJobs();
  expect(j).toBeGreaterThanOrEqual(1);
  expect(j).toBeLessThanOrEqual(4);
});

test("a bend process above --mem-mb is killed and its instance dropped as too large, never passed", async () => {
  const r = await lawcheck(path.join(FX, "u32_huge.bend"), { maxInstances: 12, seed: 1, size: 3, memMb: 300 });
  const l = r.laws[0];
  expect(l.status).toBe("pass");
  expect(l.tooLarge).toBeGreaterThan(0);
  expect(l.instances).toBeGreaterThan(0);
  expect(l.instances + l.tooLarge!).toBe(l.generated);
}, T);

test("measured with ps, as where there is no /proc (macOS), a process above --mem-mb is killed for memory, not at the timeout", async () => {
  const saved = process.env.BENDLIB_RSS;
  process.env.BENDLIB_RSS = "ps";
  try {
    const E = { header: "", dir: "", bend: "", timeoutMs: 60_000, memMb: 100, jobs: 1, runs: 0, display: (s: string) => s, unsafe: [] };
    // capped at 640 MB, so a watchdog that never fires costs the timeout, not the machine
    const grow = "const bs = []; setInterval(() => { if (bs.length < 40) bs.push(Buffer.alloc(16 << 20, 1)); }, 50)";
    const t0 = performance.now();
    const r = await runBounded(E, [process.execPath, "-e", grow]);
    expect([r.overMemory, r.timedOut]).toEqual([true, false]);
    expect(performance.now() - t0).toBeLessThan(30_000);
  } finally {
    if (saved === undefined) delete process.env.BENDLIB_RSS; else process.env.BENDLIB_RSS = saved;
  }
}, T);
