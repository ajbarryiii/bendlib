// Public division laws compose in importing proofs; the positive-divisor premise is essential.
import { expect, test } from "bun:test";
import { cpSync, mkdtempSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { BEND, CLEAN, ROOT } from "./lib.ts";
import { scratchBase } from "../lawcheck/src/lawcheck.ts";

const scratch = mkdtempSync(join(scratchBase(), "bend-division-contract-"));
const modulePath = join(ROOT, "packages/bend-mathlib");
cpSync(modulePath, join(scratch, "mathlib"), { recursive: true });

test("division reflection accepts every divisor and composes with divisor antitonicity", () => {
  const file = join(scratch, "consumer.bend");
  writeFileSync(file, `import Base
import ./mathlib/nat.bend as N
import ./mathlib/u32.bend as U

law quotient:
  for a: U32
  for b: U32
  {U32.to_nat(U32.div(a, b)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}

def quotient(a, b):
  U.u32_to_nat_div(a, b)

law zero_divisor:
  for a: U32
  {U32.to_nat(U32.div(a, 0)) == Nat.div(U32.to_nat(a), 0n) : Nat}

def zero_divisor(a):
  U.u32_to_nat_div(a, 0)

law nat_divisor_order:
  for a: Nat
  for s: Nat
  for t: Nat
  for st: N.le(s, t)
  for positive: N.lt(0n, s)
  N.le(Nat.div(a, t), Nat.div(a, s))

def nat_divisor_order(a, s, t, st, positive):
  N.div_antitone(a, s, t, st, positive)

law machine_divisor_order:
  for a: U32
  for s: U32
  for t: U32
  for st: {U32.is_le(s, t) == True{} : Bool}
  for positive: {U32.is_lt(0, s) == True{} : Bool}
  {U32.is_le(U32.div(a, t), U32.div(a, s)) == True{} : Bool}

def machine_divisor_order(a, s, t, st, positive):
  U.u32_div_antitone(a, s, t, st, positive)
`);
  const p = Bun.spawnSync([BEND, file, "--check-only"]);
  expect((p.stdout.toString() + p.stderr.toString()).trim()).toBe(CLEAN);
  expect(p.stderr.toString()).toBe("");
  expect(p.exitCode).toBe(0);
});

test("zero is a counterexample to divisor antitonicity without positivity", () => {
  for (const [name, claim] of [
    ["nat", "Nat.is_le(Nat.div(1n, 1n), Nat.div(1n, 0n))"],
    ["u32", "U32.is_le(U32.div(1, 1), U32.div(1, 0))"],
  ]) {
    const file = join(scratch, `missing_premise_${name}.bend`);
    writeFileSync(file, `import Base\nlaw bad:\n  {${claim} == True{} : Bool}\ndef bad():\n  {==}\n`);
    const p = Bun.spawnSync([BEND, file, "--check-only"]);
    const output = p.stdout.toString() + p.stderr.toString();
    expect(p.exitCode).toBe(1);
    expect(output).toContain("False{}");
    expect(output).toContain("True{}");
    expect(output).not.toContain("ALL PROOFS CHECK");
    expect(output).not.toMatch(/RangeError|stack overflow|\n\s+at /);
  }
});
