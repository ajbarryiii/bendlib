// Regression: the checker's batch size is fixed and independent of --jobs, so
// `checkerRuns` must not grow when more cores are offered (the old
// `min(50, items/jobs)` shrank batches as jobs grew and multiplied spawns).
import { expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
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

// A fake bend that, like `--native` (bend builds with spawnSync(cc)), leaves a child running when it alone is killed.
async function survivingChild(child: string, limits: { timeoutMs: number; memMb: number }) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lawcheck-tree-"));
  const pidFile = path.join(dir, "child.pid"), fake = path.join(dir, "bend.sh");
  fs.writeFileSync(fake, `#!/bin/sh\n${child} >/dev/null 2>&1 &\necho $! > '${pidFile}'\nexec sleep 300\n`);
  fs.chmodSync(fake, 0o755);
  const E = { header: "", dir: "", bend: "", jobs: 1, runs: 0, display: (s: string) => s, unsafe: [], ...limits };
  const r = await runBounded(E, [fake]);
  const pid = Number(fs.readFileSync(pidFile, "utf8"));
  const alive = () => { try { process.kill(pid, 0); return !/^\d+ \(.*\) Z/.test(fs.readFileSync(`/proc/${pid}/stat`, "utf8")); } catch { return false; } };
  for (let i = 0; i < 50 && alive(); i++) await Bun.sleep(100);
  const survived = alive();
  if (survived) process.kill(pid, "SIGKILL");
  return { r, survived };
}

test.skipIf(process.platform !== "linux")("a timed-out run kills the whole process tree, not only bend", async () => {
  const { r, survived } = await survivingChild("sleep 300", { timeoutMs: 1_000, memMb: 1024 });
  expect([r.timedOut, survived]).toEqual([true, false]);
}, T);

test.skipIf(process.platform !== "linux")("a run killed over --mem-mb kills the child that used the memory", async () => {
  const grow = "const bs = []; setInterval(() => { if (bs.length < 40) bs.push(Buffer.alloc(16 << 20, 1)); }, 50)";
  const { r, survived } = await survivingChild(`'${process.execPath}' -e '${grow}'`, { timeoutMs: 60_000, memMb: 100 });
  expect([r.overMemory, r.timedOut, survived]).toEqual([true, false, false]);
}, T);
