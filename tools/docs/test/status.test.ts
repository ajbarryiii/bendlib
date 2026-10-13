// Checker-output classification. The strings are verbatim outputs of
// `bend <file> --check-only` on 2.0.37 (hub files or experiments named in each test).

import { describe, expect, test } from "bun:test";
import { chmodSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { BEND, checkCommand, checkFile, classify, crossCheck, sandboxProbe, worst, type FileStatus } from "../src/status.ts";
import { stale, DEFAULT_TIMEOUT } from "../build.ts";

const CLEAN_OUT = "ALL PROOFS CHECK\nUse --verdict for mathematical validity.\n";

describe("classify", () => {
  test("exactly the clean verdict with exit 0 is checks", () => {
    const s = classify(CLEAN_OUT, 0, false, 1);
    expect(s.class).toBe("checks");
    expect(s.summary).toBe("ALL PROOFS CHECK");
  });
  test("planted negative: the same text with a non-zero exit is not checks", () => {
    expect(classify(CLEAN_OUT, 1, false, 1).class).toBe("fails");
  });
  test("planted negative: the verdict line without its hint line is not checks", () => {
    expect(classify("ALL PROOFS CHECK\n", 0, false, 1).class).toBe("fails");
  });
  test("the unsafe line lists its defs (0xb1a81026…/Engine.bend)", () => {
    const out = "SOME PROOFS FAIL\nError: 8 defs rely on unsafe or foreign code:\n"
      + "- 0xb1a81026c64fbbc00a8570155d77383d/Genetics.get_subtree_step\n- 0xb1a81026c64fbbc00a8570155d77383d/Genetics.get_subtree\n"
      + "- 0xb1a81026c64fbbc00a8570155d77383d/Genetics.replace_subtree_step\n- 0xb1a81026c64fbbc00a8570155d77383d/Genetics.replace_subtree\n"
      + "- 0xb1a81026c64fbbc00a8570155d77383d/Genetics.crossover\n- breed_child\n- generate_next_pop\n- evolve\n";
    const s = classify(out, 1, false, 1);
    expect(s.class).toBe("unsafe");
    expect(s.unsafeDefs).toEqual([
      "0xb1a81026c64fbbc00a8570155d77383d/Genetics.get_subtree_step", "0xb1a81026c64fbbc00a8570155d77383d/Genetics.get_subtree",
      "0xb1a81026c64fbbc00a8570155d77383d/Genetics.replace_subtree_step", "0xb1a81026c64fbbc00a8570155d77383d/Genetics.replace_subtree",
      "0xb1a81026c64fbbc00a8570155d77383d/Genetics.crossover", "breed_child", "generate_next_pop", "evolve",
    ]);
    expect(s.summary).toBe("8 defs rely on unsafe or foreign code");
  });
  test("singular form (a file with one @unsafe def)", () => {
    const s = classify("SOME PROOFS FAIL\nError: 1 def relies on unsafe or foreign code:\n- u\n", 1, false, 1);
    expect(s.class).toBe("unsafe");
    expect(s.unsafeDefs).toEqual(["u"]);
    expect(s.summary).toBe("1 def relies on unsafe or foreign code");
  });
  test("TODOs are open laws (0xf5a52e74…/src/LAWS.bend)", () => {
    const s = classify("SOME PROOFS FAIL\nError: 5 TODOs found.\nThe code is incomplete, and not a valid proof yet.\n", 1, false, 1);
    expect(s.class).toBe("open");
    expect(s.summary).toBe("5 TODOs found.");
  });
  test("an error block is fails with its message as the summary (research/experiments/ctor.bend)", () => {
    const out = "SOME PROOFS FAIL\nError:\n- expected : a fresh constructor name (duplicate declaration: Some)\n- observed : 'Some'\n"
      + "Location:\n3 | type opt is Data:\n4>|   Some{v: Nat}\n  |   ^^^^\n5 |   nothing{}\n";
    const s = classify(out, 1, false, 1);
    expect(s.class).toBe("fails");
    expect(s.summary).toBe("- expected : a fresh constructor name (duplicate declaration: Some)");
    expect(s.detail).toContain("4>|   Some{v: Nat}");
  });
  test("a kill on timeout is timeout, whatever was printed", () => {
    expect(classify("", null, true, 20.2).class).toBe("timeout");
  });
  test("planted negative: bwrap failing before the checker is sandbox, not fails", () => {
    const s = classify("bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted\n", 1, false, 0.01);
    expect(s.class).toBe("sandbox");
    expect(s.summary).toBe("checker did not run: sandbox setup failed");
  });
  test("planted negative: a real checker error that mentions bwrap later is still fails", () => {
    const s = classify("Error:\n- expected : a fresh constructor name\nbwrap: nope\n", 1, false, 1);
    expect(s.class).toBe("fails");
  });
  test("package status is the worst file status", () => {
    expect(worst(["checks", "unsafe", "checks"])).toBe("unsafe");
    expect(worst(["open", "timeout", "unsafe"])).toBe("timeout");
    expect(worst(["checks", "fails", "timeout"])).toBe("fails");
    expect(worst([])).toBe("checks");
  });
});

describe("crossCheck", () => {
  const clean = () => classify(CLEAN_OUT, 0, false, 1);
  test("a clean verdict over @unsafe source is downgraded to unsafe (bend issue #1001)", () => {
    const s = crossCheck(clean(), "@unsafe\ndef f() -> Nat:\n  0n\n");
    expect(s.class).toBe("unsafe");
    expect(s.unsafeDefs).toEqual(["f"]);
    expect(s.summary).toBe("source has @unsafe, but bend printed a clean verdict (bend issue #1001)");
  });
  test("every def after an @unsafe is named, including the ? form", () => {
    const src = "@unsafe\ndef f() -> Nat:\n  0n\n\n@unsafe\ndef g?(x) -> Nat:\n  x\n";
    expect(crossCheck(clean(), src).unsafeDefs).toEqual(["f", "g"]);
  });
  test("planted negative: @unsafe in a comment is not counted", () => {
    expect(crossCheck(clean(), "# @unsafe\ndef f() -> Nat:\n  0n\n").class).toBe("checks");
  });
  test("planted negative: @unsafe inside a string is not counted", () => {
    expect(crossCheck(clean(), 'def f() -> String:\n  "@unsafe"\n').class).toBe("checks");
  });
  test("planted negative: @unsafe never upgrades a fails status", () => {
    const fails = classify("Error:\n- expected : a fresh constructor name (duplicate declaration: Zero)\n", 1, false, 1);
    expect(fails.class).toBe("fails");
    expect(crossCheck(fails, "@unsafe\ndef f() -> Nat:\n  0n\n").class).toBe("fails");
  });
});

describe("checkCommand", () => {
  const o = { bendLib: "/lib", timeoutSec: 20, memMb: 4096, rssMb: 3072, cwd: "/pkg" };
  test("sandboxed: bwrap with a read-only root and read-only BEND_LIB, inner check unchanged", () => {
    const argv = checkCommand("/lib/h/f.bend", o, true);
    expect(argv[0]).toBe("bwrap");
    expect(argv).toContain("--unshare-all");
    expect(argv).toContain("--die-with-parent");
    const ro = argv.indexOf("--ro-bind");
    expect(argv.slice(ro, ro + 3)).toEqual(["--ro-bind", "/", "/"]);
    const tmp = argv.indexOf("--tmpfs");
    expect(argv.slice(tmp, tmp + 2)).toEqual(["--tmpfs", "/tmp"]);
    // The lib is bound read-only after --tmpfs /tmp: visible when the lib lives under /tmp, never writable.
    const lib = argv.indexOf("--ro-bind", tmp + 1);
    expect(argv.slice(lib, lib + 3)).toEqual(["--ro-bind", "/lib", "/lib"]);
    expect(argv).not.toContain("--bind");
    const c = argv.indexOf("--chdir");
    expect(argv.slice(c, c + 2)).toEqual(["--chdir", "/pkg"]);
    expect(argv.slice(argv.indexOf("bash"))).toEqual(checkCommand("/lib/h/f.bend", o, false));
  });
  test("unsandboxed: today's argv, with the memory cap and no bwrap", () => {
    const argv = checkCommand("/lib/h/f.bend", o, false);
    expect(argv[0]).toBe("bash");
    expect(argv).not.toContain("bwrap");
    expect(argv[2]).toContain("ulimit -v 4194304");
    expect(argv.slice(-2)).toEqual([BEND, "/lib/h/f.bend"]);
  });
});

/** Writes a fake bwrap executable in a fresh temp dir and returns its path. */
function fakeBwrap(script: string): string {
  const dir = mkdtempSync(join(tmpdir(), "bend-docs-bwrap-"));
  const p = join(dir, "bwrap");
  writeFileSync(p, script);
  chmodSync(p, 0o755);
  return p;
}

describe("sandboxProbe", () => {
  test("planted negative: a bwrap that only answers --version fails the real probe", () => {
    const fake = fakeBwrap("#!/bin/sh\n[ \"$1\" = \"--version\" ] && exit 0\necho \"bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted\" >&2\nexit 1\n");
    const r = sandboxProbe(fake);
    expect(r.ok).toBe(false);
    expect(r.why).toContain("RTM_NEWADDR");
  });
  test("a real namespace start passes", () => {
    const probe = sandboxProbe();
    if (probe.ok) expect(probe.why).toBe("");
  });
});

describe("memory cap", () => {
  // verbatim: bend 2.0.34 on hub 0x636ea893…/jwt.bend under `ulimit -v 4194304`, exit 134
  const CRASH = "ASSERTION FAILED: MemoryExhaustion: Crash intentionally because memory is exhausted.\nfailureMode != AllocationFailureMode::Assert\nvendor/WebKit/Source/JavaScriptCore/heap/LocalAllocator.cpp(150) : void *JSC::LocalAllocator::allocateSlowCase(JSC::Heap &, size_t, GCDeferralContext *, AllocationFailureMode)\n";
  test("the checker aborting under the address-space cap is `limit`, not a verdict", () => {
    const st = classify(CRASH, 134, false, 3);
    expect(st.class).toBe("limit");
    expect(worst(["checks", "limit"])).toBe("limit");
  });
  test("planted negative: an ordinary checker error is still `fails`", () => {
    expect(classify("SOME PROOFS FAIL\nError:\n- expected : a defined name\n- observed : Nat.div.fin\n", 1, false, 1).class).toBe("fails");
  });
  test("a cached cap abort, old (`fails`) or new (`limit`), is re-checked", () => {
    const at = (c: FileStatus["class"]): FileStatus => ({ class: c, summary: "", detail: CRASH, exitCode: 134, seconds: 3 });
    expect(stale(at("fails"), 60)).toBe(true);
    expect(stale(at("limit"), 60)).toBe(true);
  });
});

describe("stale", () => {
  const s = (c: FileStatus["class"], detail = "", seconds = 0): FileStatus => ({ class: c, summary: "", detail, exitCode: 1, seconds });
  test("a pre-probe bwrap failure in the cache is re-checked", () => {
    expect(stale(s("fails", "bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted"), 20)).toBe(true);
  });
  test("planted negative: a genuine checker failure stays cached", () => {
    expect(stale(s("fails", "- expected : a fresh constructor name"), 20)).toBe(false);
  });
  test("planted negative: a timeout keeps its time budget rule", () => {
    expect(stale(s("timeout", "", 5), 20)).toBe(true);
    expect(stale(s("timeout", "", 19.5), 20)).toBe(false);
  });
  test("a timeout cached under the old 20 s default is re-checked with the new 60 s budget", () => {
    expect(stale(s("timeout", "", 20), DEFAULT_TIMEOUT)).toBe(true);
  });
  test("a missing entry is stale and a fresh check is not", () => {
    expect(stale(undefined, 20)).toBe(true);
    expect(stale(s("checks"), 20)).toBe(false);
  });
});

describe("build defaults", () => {
  test("the default checker timeout is 180 s (PLAN §5.2)", () => {
    expect(DEFAULT_TIMEOUT).toBe(180);
  });
});

const hasBwrap = sandboxProbe().ok;

describe("checkFile under the sandbox", () => {
  test.skipIf(!hasBwrap)("the good fixture checks inside bwrap", async () => {
    const entry = join(import.meta.dir, "..", "..", "mathlib", "fixtures", "good", "list.bend");
    const lib = mkdtempSync(join(tmpdir(), "bend-docs-sandbox-"));
    const s = await checkFile(entry, { bendLib: lib, timeoutSec: 120, memMb: 16384, rssMb: 3072, cwd: dirname(entry) });
    expect(s.class).toBe("checks");
  }, 180_000);
});

describe("resident-memory limit", () => {
  const entry = join(import.meta.dir, "..", "..", "..", "packages", "bend-mathlib", "nat.bend");
  test.skipIf(process.platform !== "linux")("a check over the limit is killed and reported as `limit`, with the limit", async () => {
    const lib = mkdtempSync(join(tmpdir(), "bend-docs-rss-"));
    const s = await checkFile(entry, { bendLib: lib, timeoutSec: 120, memMb: 16384, rssMb: 20, cwd: dirname(entry) });
    expect(s.class).toBe("limit");
    expect(s.rssMb).toBe(20);
  }, 180_000);
  test("a cached `limit` is re-checked only when the limit has grown", () => {
    const at = (rssMb?: number): FileStatus => ({ class: "limit", summary: "", detail: "", exitCode: null, seconds: 1, rssMb });
    expect(stale(at(3072), 60, 3072)).toBe(false);
    expect(stale(at(3072), 60, 8192)).toBe(true);
    expect(stale(at(), 60, 3072)).toBe(true);
  });
});
