// CLI tests for the `mutate` subcommand and `--version`; real bend, nothing mocked.

import { describe, expect, test } from "bun:test";
import * as path from "node:path";

const CLI = path.join(import.meta.dir, "..", "cli.ts");
const FX = path.join(import.meta.dir, "fixtures");
const T = 240_000;

async function run(...args: string[]) {
  const p = Bun.spawn([process.execPath, CLI, ...args], { stdout: "pipe", stderr: "pipe" });
  const [stdout, stderr] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  return { code: await p.exited, stdout, stderr };
}

describe("mutate CLI", () => {
  test("--version prints lawcheck 0.4.0", async () => {
    const r = await run("--version");
    expect(r.code).toBe(0);
    expect(r.stdout.trim()).toBe("lawcheck 0.4.0");
  });

  test("weak laws: exit 1, header shape and a survivor line", async () => {
    const r = await run("mutate", path.join(FX, "mut_weak.bend"), "--max-instances", "5", "--jobs", "4");
    expect(r.code).toBe(1);
    expect(r.stderr).toBe("");
    expect(r.stdout).toMatch(/^lawcheck mutate 0\.4\.0 · .+ \(impl lib_ok\.bend\) · bend .+ · ≤5 instances\/law$/m);
    expect(r.stdout).toMatch(/^size {2}\d+\/\d+ valid mutants killed · \d+ survived · \d+ invalid$/m);
    expect(r.stdout).toMatch(/^ +survived {2}\S+ {2}line \d+ {2}.+ → .+$/m);
    expect(r.stdout).toContain("survivor(s): your laws do not pin these changes.");
  }, T);

  test("a genuine arg-swap survivor is reported", async () => {
    const r = await run("mutate", path.join(FX, "mut_argswap.bend"), "--max-instances", "5", "--jobs", "4");
    expect(r.code).toBe(1);
    expect(r.stdout).toContain("survived  arg-swap");
  }, T);

  test("strong laws with --def app: exit 0 and no survivors", async () => {
    const r = await run("mutate", path.join(FX, "mut_strong.bend"), "--def", "app", "--max-instances", "5", "--jobs", "4");
    expect(r.code).toBe(0);
    expect(r.stderr).toBe("");
    expect(r.stdout).toContain("no survivors: every valid mutant broke a law.");
  }, T);

  test("proofs in the laws file do not turn every behaviour-changing mutant invalid", async () => {
    const r = await run("mutate", path.join(FX, "mut_proved", "laws.bend"), "--impl", path.join(FX, "mut_proved", "lib.bend"), "--max-instances", "20", "--jobs", "4");
    expect(r.code).toBe(0);
    expect(r.stderr).toBe("");
    expect(r.stdout).toMatch(/^dbl +\d+\/\d+ valid mutants killed · 0 survived · \d+ invalid$/m);
    const killed = Number(/^dbl +(\d+)\/\d+ valid mutants killed/m.exec(r.stdout)![1]);
    expect(killed).toBeGreaterThanOrEqual(4);
  }, T);

  test("nothing evaluated on the base is exit 2, never all-survivors", async () => {
    for (const fixture of ["mut_allskip.bend", "mut_nolaws.bend"]) {
      const r = await run("mutate", path.join(FX, fixture), "--jobs", "4", "--max-instances", "5");
      expect(r.code).toBe(2);
      expect(r.stdout).toBe("");
      expect(r.stderr).toContain("no law was evaluated on the unmutated code");
      expect(r.stderr).not.toContain("survived");
    }
  }, T);

  test("a missing file is a usage error, exit 2", async () => {
    const r = await run("mutate", "nope.bend");
    expect(r.code).toBe(2);
    expect(r.stdout).toBe("");
    expect(r.stderr).toContain("no such file: nope.bend");
  });

  test("--json prints the MutateReport", async () => {
    const r = await run("mutate", path.join(FX, "mut_strong.bend"), "--def", "app", "--max-instances", "5", "--jobs", "4", "--json");
    expect(r.code).toBe(0);
    expect(r.stderr).toBe("");
    const rep = JSON.parse(r.stdout);
    expect(rep.schema).toBe(1);
    expect(rep.tool).toBe("lawcheck-mutate");
    expect(rep.version).toBe("0.4.0");
    expect(rep.impl).toContain("lib_ok.bend");
    expect(rep.defs.map((d: any) => d.name)).toEqual(["app"]);
    expect(rep.defs[0].mutants.length).toBeGreaterThan(0);
  }, T);
});
