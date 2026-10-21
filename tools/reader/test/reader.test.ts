// Tests for @bendlib/reader against the installed bend (goldens are for 2.0.38).
// usage: cd tools/reader && bun test   (network: first source fetch + hub package)

import { describe, expect, test } from "bun:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { BendReadError, bendSource, decls, inNamespace, installedVersion, load, localName, sourcePin, SourceError, type Decl } from "../index.ts";
import { CASES, dump, freshBendLib, goldenPath, HUB_PKG, REPO } from "./golden.ts";

const FIX = path.join(import.meta.dir, "fixtures");
const HOME_LIB = path.join(os.homedir(), ".bend", "lib");

async function readErr(p: Promise<unknown>): Promise<BendReadError> {
  try {
    await p;
  } catch (e) {
    expect(e).toBeInstanceOf(BendReadError);
    return e as BendReadError;
  }
  throw new Error("expected a BendReadError, but the load succeeded");
}

// A minimal separate cache: only what verifyCache reads (manifest, archive hash, archive, bend2).
function copyCache(s: { dir: string; version: string }): string {
  const vdir = path.dirname(s.dir);
  const man = JSON.parse(fs.readFileSync(path.join(vdir, "manifest.json"), "utf8"));
  const cache = fs.mkdtempSync(path.join(os.tmpdir(), "bendlib-reader-cache-"));
  const copy = path.join(cache, "bend", s.version);
  fs.mkdirSync(copy, { recursive: true });
  for (const name of ["manifest.json", "archive.sha256", man.archive]) {
    fs.copyFileSync(path.join(vdir, name), path.join(copy, name));
  }
  fs.cpSync(path.join(vdir, "src", "bend2"), path.join(copy, "src", "bend2"), { recursive: true });
  return cache;
}

describe("source", () => {
  test("installed version matches the pinned toolchain", () => {
    const pinned = JSON.parse(fs.readFileSync(path.join(REPO, "toolchain.json"), "utf8")).bend.version;
    expect(installedVersion()).toBe(pinned);
  });

  test("cached tag source matches the installed version and re-verifies", async () => {
    const s = await bendSource();
    expect(s.version).toBe(installedVersion());
    expect(fs.readFileSync(path.join(s.dir, "bend2", "main.ts"), "utf8")).toContain(`const VERSION = "${s.version}";`);
    if (s.origin !== "local") {
      expect(s.archiveSha256).toMatch(/^[0-9a-f]{64}$/);
      const again = await bendSource();
      expect(again.origin).toBe("cache");
      expect(again.archiveSha256).toBe(s.archiveSha256);
    }
  });

  test("sourcePin reproduces toolchain.json's source pin", async () => {
    const s = await bendSource();
    if (s.origin === "local") return;
    const pin = await sourcePin();
    const pinned = JSON.parse(fs.readFileSync(path.join(REPO, "toolchain.json"), "utf8")).bend.source;
    expect(pin.version).toBe(s.version);
    expect(pin.files).toEqual(pinned.files);
    if (pin.commit !== undefined && pinned.commit !== undefined) expect(pin.commit).toBe(pinned.commit);
  });

  test("cli --pin prints the same source pin", async () => {
    const s = await bendSource();
    if (s.origin === "local") return;
    const r = Bun.spawnSync(["bun", path.join(REPO, "tools/reader/cli.ts"), "--pin"], { stdout: "pipe", stderr: "pipe" });
    expect(r.exitCode).toBe(0);
    const pin = JSON.parse(r.stdout.toString());
    const pinned = JSON.parse(fs.readFileSync(path.join(REPO, "toolchain.json"), "utf8")).bend.source;
    expect(pin.files).toEqual(pinned.files);
  }, 60_000);

  test("a tampered cached bend.ts is refused", async () => {
    const s = await bendSource();
    if (s.origin === "local") return;
    const cache = copyCache(s);
    const copy = path.join(cache, "bend", s.version);
    fs.appendFileSync(path.join(copy, "src", "bend2", "bend.ts"), "\n// tampered\n");
    const old = process.env.BENDLIB_CACHE;
    process.env.BENDLIB_CACHE = cache;
    try {
      await expect(bendSource()).rejects.toThrow(/bend2\/bend\.ts has sha256 .* recorded/);
    } finally {
      if (old === undefined) delete process.env.BENDLIB_CACHE; else process.env.BENDLIB_CACHE = old;
      fs.rmSync(cache, { recursive: true, force: true });
    }
  });

  test("a poisoned cache with a rewritten manifest is refused by the pin", async () => {
    const s = await bendSource();
    if (s.origin === "local") return;
    const cache = copyCache(s);
    const copy = path.join(cache, "bend", s.version);
    const bend = path.join(copy, "src", "bend2", "bend.ts");
    fs.appendFileSync(bend, "\n// poisoned\n");
    const man = JSON.parse(fs.readFileSync(path.join(copy, "manifest.json"), "utf8"));
    man.files["bend2/bend.ts"] = new Bun.CryptoHasher("sha256").update(fs.readFileSync(bend)).digest("hex");
    fs.writeFileSync(path.join(copy, "manifest.json"), JSON.stringify(man, null, 2) + "\n");
    const old = process.env.BENDLIB_CACHE;
    process.env.BENDLIB_CACHE = cache;
    try {
      await expect(bendSource()).rejects.toThrow(/pinned/);
    } finally {
      if (old === undefined) delete process.env.BENDLIB_CACHE; else process.env.BENDLIB_CACHE = old;
      fs.rmSync(cache, { recursive: true, force: true });
    }
  });

  test("a fetched base.bend that differs from the installed one is refused", async () => {
    const s = await bendSource();
    if (s.origin === "local") return;
    const fake = fs.mkdtempSync(path.join(os.tmpdir(), "bendlib-reader-bin-"));
    try {
      const bin = path.join(fake, "bin", "bend");
      fs.mkdirSync(path.dirname(bin), { recursive: true });
      fs.writeFileSync(bin, `#!/bin/sh\necho "bend ${s.version}"\n`, { mode: 0o755 });
      fs.mkdirSync(path.join(fake, "bend2"), { recursive: true });
      fs.writeFileSync(path.join(fake, "bend2", "base.bend"), "not the installed base.bend\n");
      await expect(bendSource({ bin })).rejects.toThrow(/pinned/);
    } finally {
      fs.rmSync(fake, { recursive: true, force: true });
    }
  });

  test("a local checkout at another version is refused", async () => {
    const s = await bendSource();
    await expect(bendSource({ src: s.dir, version: "2.0.1" })).rejects.toBeInstanceOf(SourceError);
    const local = await bendSource({ src: s.dir });
    expect(local.origin).toBe("local");
  });
});

describe("goldens (bend 2.0.38)", () => {
  for (const c of CASES) {
    test(`${c.name}: ${c.file}`, async () => {
      const golden = JSON.parse(fs.readFileSync(goldenPath(c), "utf8"));
      const got = await dump(c);
      expect(got.decls).toEqual(golden.decls);
    }, 60_000);
  }
});

describe("decls", () => {
  test("glist: laws with readable statements, no HOAS leftovers", async () => {
    const L = await load(path.join(REPO, "research/experiments/glist.bend"));
    const ds = decls(L);
    const nil = ds.find((d) => d.name === "append_nil_r") as Decl;
    expect(nil.kind).toBe("law");
    expect(nil.proved).toBe(true);
    expect(nil.signature).toBe("@a:Quant -> @-A:Kind(a) -> @xs:List<a, A> -> {List.append(a, A, xs, []) == xs : List<a, A>}");
    expect(nil.statement).toEqual({ lhs: "List.append(a, A, xs, [])", rhs: "xs", type: "List<a, A>" });
    expect(nil.binders?.map((b) => b.quant)).toEqual(["affine", "erased", "affine"]);
    for (const d of decls(L, { scope: "all" })) {
      expect(d.signature).not.toContain("undefined");
      expect(d.signature).not.toMatch(/function|\[object|=>\s*$/);
    }
  });

  test("order: a type, its ctors, a predicate and a law", async () => {
    const L = await load(path.join(REPO, "research/experiments/v1/order.bend"));
    const k = Object.fromEntries(decls(L).map((d) => [d.name, d]));
    expect(k.tree.kind).toBe("type");
    expect(k.tree.ctors).toEqual(["tleaf", "tnode"]);
    expect(k.tnode.kind).toBe("ctor");
    expect(k.tnode.signature).toBe("@l:tree -> @v:Nat -> @r:tree -> tree");
    expect(k.le.predicate).toBe(true);
    expect(k.le.doc).toBe("a predicate as a type-level def over Base types");
    expect(k.le_refl.kind).toBe("law");
    expect(k.le_refl.statement).toBeUndefined();
  });

  test("constructors sharing one line: each is placed at its declaration", async () => {
    const src = fs.readFileSync(path.join(FIX, "ctors_one_line.bend"), "utf8");
    const line4 = src.split("\n")[3];
    const col = (n: string) => line4.indexOf(n) + 1;
    const k = Object.fromEntries(decls(await load(path.join(FIX, "ctors_one_line.bend"))).map((d) => [d.name, d]));
    for (const n of ["PTag", "RLen", "PKey"]) {
      expect(k[n]).toMatchObject({ kind: "ctor", line: 4, column: col(n), type: "Phase" });
    }
    expect(k.first).toMatchObject({ kind: "def", line: 6 });
  });

  test("constructors on the type header line are placed there", async () => {
    const k = Object.fromEntries(decls(await load(path.join(FIX, "ctors_header_line.bend"))).map((d) => [d.name, d]));
    expect(k.A).toMatchObject({ kind: "ctor", line: 3, column: 17, type: "T" });
    expect(k.B).toMatchObject({ kind: "ctor", line: 3, column: 21, type: "T" });
    expect(k.f).toMatchObject({ kind: "def", line: 5, column: 1 });
  });

  test("unindented constructors are placed and the body ends at the next def", async () => {
    const k = Object.fromEntries(decls(await load(path.join(FIX, "ctors_unindented.bend"))).map((d) => [d.name, d]));
    expect(k.A).toMatchObject({ kind: "ctor", line: 4, column: 1, type: "T" });
    expect(k.B).toMatchObject({ kind: "ctor", line: 5, column: 1, type: "T" });
    expect(k.f).toMatchObject({ kind: "def", line: 7, column: 1 });
  });

  test("a constructor named inside a comment is not matched", async () => {
    const k = Object.fromEntries(decls(await load(path.join(FIX, "ctor_in_comment.bend"))).map((d) => [d.name, d]));
    expect(k.B).toMatchObject({ kind: "ctor", line: 6, column: 3, type: "T", doc: "note} B{}" });
    expect(k.f).toMatchObject({ kind: "def", line: 8, column: 1 });
  });

  test("an indented type with its constructors still reads identically", async () => {
    const k = Object.fromEntries(decls(await load(path.join(FIX, "type_indented.bend"))).map((d) => [d.name, d]));
    expect(k.Color).toMatchObject({ kind: "type", line: 4, column: 1, doc: "A palette.", ctors: ["Red", "Green", "Blue"] });
    expect(k.Red).toMatchObject({ kind: "ctor", line: 5, column: 3, type: "Color" });
    expect(k.Green).toMatchObject({ kind: "ctor", line: 6, column: 3, type: "Color" });
    expect(k.Blue).toMatchObject({ kind: "ctor", line: 7, column: 3, type: "Color" });
    expect(k.rank).toMatchObject({ kind: "def", line: 9, column: 1 });
  });

  test("identical module contents in distinct namespaces resolve by namespace", async () => {
    const L = await load(path.join(FIX, "identical/main.bend"));
    const ds = decls(L, { scope: "all-non-base" });
    const k = Object.fromEntries(ds.map((d) => [d.name, d]));
    const dup = (ns: string) => ds.find((d) => d.namespace === ns && inNamespace(d.name, ns) && localName(d.name, ns) === "dup");
    const real = (p: string) => fs.realpathSync(path.join(FIX, "identical", p));
    expect(dup("libA")).toMatchObject({ kind: "def", namespace: "libA", file: real("libA.bend"), line: 3 });
    expect(dup("libB")).toMatchObject({ kind: "def", namespace: "libB", file: real("libB.bend"), line: 3 });
    expect(dup("libA")!.signature).toBe(dup("libB")!.signature);
    expect(k.use).toMatchObject({ kind: "def", namespace: "", file: real("main.bend"), line: 5 });
  });

  test("templates, effects and unsafe defs in Base are classified", async () => {
    const L = await load(path.join(REPO, "research/experiments/v1/order.bend"));
    const base = decls(L, { scope: "all" }).filter((d) => d.origin === "base");
    const by = (n: string) => base.find((d) => d.name === n) as Decl;
    expect(by("List.map").kind).toBe("template");
    expect(by("List.map").templates).toBe(3);
    expect(by("IO.print").kind).toBe("effect");
    expect(base.filter((d) => d.kind === "unsafe").length).toBeGreaterThan(0);
    expect(L.base.length).toBe(base.filter((d) => d.kind !== "ctor").length);
  });

  test("open law is reported unproved", async () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "bendlib-reader-open-"));
    try {
      const f = path.join(tmp, "open.bend");
      fs.writeFileSync(f, "import Base\n\n# stated, not proved\nlaw zero_add:\n  for n: Nat\n  {Nat.add(0n, n) == n : Nat}\n");
      const [d] = decls(await load(f));
      expect(d).toMatchObject({ kind: "law", proved: false, line: 4, doc: "stated, not proved" });
      expect(d.proof).toBeUndefined();
    } finally {
      fs.rmSync(tmp, { recursive: true, force: true });
    }
  });
});

describe("hub", () => {
  test("hub package by hash loads into a private BEND_LIB only", async () => {
    const homeBefore = fs.existsSync(HOME_LIB) ? fs.readdirSync(HOME_LIB).sort() : [];
    const lib = fs.realpathSync(freshBendLib());
    try {
      const L = await load(path.join(FIX, "hub_list.bend"), { bendLib: lib });
      expect(fs.existsSync(path.join(lib, HUB_PKG, "list.bend"))).toBe(true);
      const ns = HUB_PKG + "/list";
      const imp = decls(L, { scope: "all-non-base" }).filter((d) => d.origin === "imported");
      expect(imp.length).toBe(6);
      expect(imp.every((d) => d.namespace === ns && d.file === path.join(lib, HUB_PKG, "list.bend"))).toBe(true);
      expect(fs.existsSync(HOME_LIB) ? fs.readdirSync(HOME_LIB).sort() : []).toEqual(homeBefore);
    } finally {
      fs.rmSync(lib, { recursive: true, force: true });
    }
  }, 60_000);
});

describe("planted negatives", () => {
  test("syntax error: thrown, located at the offending line", async () => {
    const e = await readErr(load(path.join(FIX, "syntax_error.bend")));
    expect(e.file).toBe(fs.realpathSync(path.join(FIX, "syntax_error.bend")));
    expect(e.line).toBe(9);
    expect(e.column).toBe(3);
    expect(e.bendMessage).toContain("- expected : ':'");
    console.log("[negative] " + e.message);
  });

  test("syntax error inside an imported file points at that file", async () => {
    const e = await readErr(load(path.join(FIX, "imports_broken.bend")));
    expect(e.file).toBe(fs.realpathSync(path.join(FIX, "syntax_error.bend")));
    expect(e.line).toBe(9);
  });

  test("missing import: thrown, located at the import line", async () => {
    const e = await readErr(load(path.join(FIX, "missing_import.bend")));
    expect(e.file).toBe(fs.realpathSync(path.join(FIX, "missing_import.bend")));
    expect(e.line).toBe(2);
    expect(e.bendMessage).toContain("no such file: " + path.join(FIX, "does_not_exist.bend"));
    console.log("[negative] " + e.message);
  });

  test("type error with check: thrown with the def and its line", async () => {
    const f = path.join(FIX, "type_error.bend");
    expect(decls(await load(f)).map((d) => d.name)).toEqual(["wrong"]);
    const e = await readErr(load(f, { check: true }));
    expect(e.def).toBe("wrong");
    expect(e.file).toBe(fs.realpathSync(f));
    expect(e.line).toBe(4);
  });

  test("a missing root file is an error, not an empty result", async () => {
    const e = await readErr(load(path.join(FIX, "nope.bend")));
    expect(e.line).toBeNull();
    expect(e.message).toContain("no such file");
  });
});
