// End to end on the live hub: builds four real packages with a fresh cache (fetch,
// verify, extract, check on the installed bend) and inspects the generated site.

import { beforeAll, describe, expect, test } from "bun:test";
import { chmodSync, existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { compile, matchStatement } from "../src/shape.ts";
import type { SearchIndex } from "../src/searchindex.ts";
import { sha256 } from "../src/hub.ts";
import { hubHash, packageFiles } from "../../mathlib/hash.ts";

const MATHLIB = "0xafc61ca8b7738a6df7f28eddf80168f8";   // bend-mathlib@0.1.0.1
const KERNEL = "0xb5c8145e53a6a127d611f45f602666ec";    // bendlib-kernel-list@1.0.0.0 (ours, so its name stays)
// bend-tensors@0.0.0.2, by hash: a third-party name can be relinked or dropped, its content cannot.
const TENSORS = "0x39d8166231e68361eb37e8bef9287b8a";
const ANON = "0x6648eb78d8a978a0e437eabbfbc841cd";      // anonymous; imports 0xe49a3e65…/parse.bend
const PARSE = "0xe49a3e6521e1b71e55654a885f27bcc1";

/** Writes a fake bwrap executable in a fresh temp dir and returns its path. */
function fakeBwrap(script: string): string {
  const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-fakebwrap-"));
  const p = join(dir, "bwrap");
  writeFileSync(p, script);
  chmodSync(p, 0o755);
  return p;
}

const root = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-e2e-"));
const out = join(root, "dist");
let log = "";
// The live name of TENSORS, when bend-tensors still maps a version to it: the build must show it.
let tensorsName: string | null = null;
const read = (p: string) => readFileSync(join(out, p), "utf8");

beforeAll(async () => {
  const rec = (await fetch("https://hub.bend-lang.com/name/bend-tensors").then((r) => r.json()).catch(() => null)) as { versions?: { version: string; hash: string }[] } | null;
  const v = rec?.versions?.find((x) => x.hash === TENSORS);
  tensorsName = v ? `bend-tensors@${v.version}` : null;
  const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
    "--only", `bend-mathlib@0.1.0.1,bendlib-kernel-list@1.0.0.0,${TENSORS},${ANON}`, "--out", out, "--cache", join(root, "cache"), "--jobs", "4"]);
  log = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
  if (p.exitCode !== 0) throw new Error(`build exited ${p.exitCode}:\n${log}`);
}, 600_000);

describe("four-package build from the live hub", () => {
  test("pages exist for every package, module and name", () => {
    for (const f of ["index.html", "search.html", "search-index.json", "assets/style.css", "assets/search.js", "assets/site.js",
      `pkg/${MATHLIB}/index.html`, `pkg/${MATHLIB}/nat.bend.html`, `pkg/${MATHLIB}/list.bend.html`,
      `pkg/${TENSORS}/index.html`, `pkg/${TENSORS}/bend_tensors.bend.html`,
      `pkg/${ANON}/index.html`, `pkg/${ANON}/format.bend.html`, "name/bend-mathlib/index.html", "name/bendlib-kernel-list/index.html", `pkg/${KERNEL}/index.html`]) {
      expect(existsSync(join(out, f))).toBe(true);
    }
    expect(log).toContain(`packages   4 (${tensorsName ? 3 : 2} carry a name@version)`);
    expect(log).toContain("fetch: 4 new packages fetched and verified");
  });

  test("the author page exists and the site nav links to it", () => {
    const html = read("authors.html");
    expect(html).toContain("Document your package");
    expect(html).toContain("What the site reads");
    // GitHub runs the hourly cron every few hours, so the page promises no hourly rebuild.
    expect(html).toContain("the next scheduled rebuild (every few hours)");
    expect(html).not.toContain("hourly");
    expect(read("index.html")).toContain('href="authors.html">Authors</a>');
  });

  test("add_comm appears with its statement, doc, anchor and proved marker", () => {
    const html = read(`pkg/${MATHLIB}/nat.bend.html`);
    const at = html.indexOf('<section class="decl" id="add_comm"');
    expect(at).toBeGreaterThan(0);
    const sec = html.slice(at, html.indexOf("</section>", at));
    expect(sec).toContain("{Nat.add(n, m) == Nat.add(m, n) : Nat}");
    expect(sec).toContain("Addition is commutative: n + m = m + n.");
    expect(sec).toContain('<span class="pr pr-yes">proved</span>');
    expect(sec).toContain(`https://hub.bend-lang.com/${MATHLIB}/nat.bend`);
  });

  test("a module's header comment is rendered on its page", () => {
    expect(read(`pkg/${MATHLIB}/all.bend.html`)).toContain("machine-checked lemmas for Bend 2");
  });

  test("each declaration links to the module source page at its own line", () => {
    expect(read(`pkg/${MATHLIB}/nat.bend.src.html`)).toContain('id="L1"');
    const html = read(`pkg/${MATHLIB}/nat.bend.html`);
    const at = html.indexOf('<section class="decl" id="add_comm"');
    const sec = html.slice(at, html.indexOf("</section>", at));
    const href = sec.match(/href="([^"]*nat\.bend\.src\.html#L(\d+))"/);
    const line = sec.match(/source · line (\d+)/);
    expect(href).not.toBeNull();
    expect(line).not.toBeNull();
    expect(href![2]).toBe(line![1]);
  });

  test("llms.txt and lemmas.txt list every latest proved law as 3 tab-separated fields", () => {
    const llms = read("llms.txt");
    expect(llms).toContain("[bend-mathlib@0.1.0.1](");
    const lemmas = read("lemmas.txt");
    expect(lemmas.startsWith("# ")).toBe(true);
    const lines = lemmas.split("\n").filter((l) => l !== "" && !l.startsWith("#"));
    expect(lines.some((l) => l.startsWith("bend-mathlib@0.1.0.1/nat.bend\tadd_comm\t"))).toBe(true);
    for (const l of lines) expect(l.split("\t").length).toBe(3);
    // Expected line count = proved claim rows in search-index.json (same latest-lineage scope).
    const idx = JSON.parse(read("search-index.json")) as SearchIndex;
    expect(lines.length).toBe(idx.d.filter((r) => r[2] === "law" && r[7] === 1).length);
  });

  test("the search page reports the latest-lineage count of the search index", () => {
    const idx = JSON.parse(read("search-index.json")) as SearchIndex;
    expect(idx.p.length).toBeGreaterThan(0);
    expect(read("search.html")).toContain(`The index covers ${idx.p.length} packages (latest version of each).`);
  });

  test("the index claims checked statuses only when every file was checked", () => {
    expect(read("index.html")).toContain("each package checked on bend 2.0.37");
  });

  test("the index lists the four packages, named ones first, with statuses from the real checker", () => {
    const html = read("index.html");
    const tensors = tensorsName ? `${tensorsName.split("@")[0]}</a> <span class="pill">@${tensorsName.split("@")[1]}</span>` : `${TENSORS.slice(0, 10)}…</a>`;
    const [m, k, t, a] = ['bend-mathlib</a> <span class="pill">@0.1.0.1</span>', 'bendlib-kernel-list</a> <span class="pill">@1.0.0.0</span>', tensors, `${ANON.slice(0, 10)}…</a>`].map((s) => html.indexOf(`>${s}`));
    expect(m).toBeGreaterThan(0);
    expect(k).toBeGreaterThan(0);
    expect(t).toBeGreaterThan(0);
    expect(a).toBeGreaterThan(Math.max(m, k, t));
    if (tensorsName === null) expect(t).toBeGreaterThan(Math.max(m, k));
    expect(read(`pkg/${MATHLIB}/index.html`)).toMatch(/<h1>bend-mathlib@0\.1\.0\.1 <span class="st st-checks">/);
    expect(read(`pkg/${KERNEL}/index.html`)).toMatch(/<h1>bendlib-kernel-list@1\.0\.0\.0 <span class="st st-checks">/);
    expect(read(`pkg/${TENSORS}/index.html`)).toMatch(new RegExp(`<h1>${(tensorsName ?? TENSORS.slice(0, 10)).replace(/\./g, "\\.")} <span class="st st-unsafe">`));
  });

  test("the anonymous package shows its real hub dependency", () => {
    const html = read(`pkg/${ANON}/index.html`);
    const deps = html.slice(html.indexOf('id="deps"'), html.indexOf('id="rdeps"'));
    expect(deps).toContain(PARSE);
    expect(deps).toContain(`format.bend: import ${PARSE}/parse.bend as P`);
    expect(deps).toContain("not in this build");
  });

  test("law-shape search over the generated index finds append_nil and not nil_append", () => {
    const idx = JSON.parse(read("search-index.json")) as SearchIndex;
    const hits = (q: string) => {
      const p = compile(q);
      return idx.d.filter((r) => r[5] !== "" && matchStatement(p, r[5], r[6])).map((r) => `${idx.p[idx.f[r[0]][0]][0]}:${r[1]}`);
    };
    const h = hits("List.append(_, Nil{})");
    expect(h).toContain("bend-mathlib@0.1.0.1:append_nil");
    expect(h).not.toContain("bend-mathlib@0.1.0.1:nil_append");
    expect(hits("Nat.add(_, 0n)")).toContain("bend-mathlib@0.1.0.1:add_zero");
    expect(hits("Nat.add(_, 0n)")).not.toContain("bend-mathlib@0.1.0.1:zero_add");
    const row = idx.d.find((r) => r[1] === "append_nil" && idx.f[r[0]][1] === "list.bend")!;
    expect(existsSync(join(out, idx.f[row[0]][2]))).toBe(true);
    expect(read(idx.f[row[0]][2])).toContain(`id="${row[3]}"`);
  });

  test("every link is relative, or points at the hub or the source repository", () => {
    for (const f of ["index.html", "search.html", `pkg/${MATHLIB}/index.html`, `pkg/${MATHLIB}/nat.bend.html`, `pkg/${MATHLIB}/nat.bend.src.html`, "name/bend-mathlib/index.html"]) {
      for (const [, href] of read(f).matchAll(/(?:href|src)="([^"]*)"/g)) {
        if (/^https:\/\/(hub\.bend-lang\.com|github\.com\/bendlib\/bendlib)\b/.test(href)) continue;
        expect(href).not.toMatch(/^(\/|[a-z]+:)/);
      }
    }
  });

  test("every page carries the footer, and the compiler version", () => {
    for (const f of ["index.html", "search.html", `pkg/${ANON}/format.bend.html`]) {
      const html = read(f);
      expect(html).toContain("Community docs for BendHub packages · not affiliated with Higher Order Company · source");
      expect(html).toContain("on bend 2.0.37 only");
    }
  });
});

describe("the index filter hides rows on a phone", () => {
  test("planted negative: the narrow layout's display:block on rows cannot override [hidden]", () => {
    const css = readFileSync(join(import.meta.dir, "..", "assets", "style.css"), "utf8");
    // site.ts filters by setting `hidden`; an author `display` beats the browser's own [hidden] rule.
    expect(css).toMatch(/table\.pkgs tr\{display:block/);
    expect(css).toContain("[hidden]{display:none!important}");
  });
});

describe("--local preview", () => {
  test("stages an unpublished package, banners every page, and prints the package page path", () => {
    const entry = join(import.meta.dir, "..", "..", "mathlib", "fixtures", "good", "list.bend");
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-local-"));
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--local", entry, "--out", dir, "--cache", join(dir, "cache")]);
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    if (p.exitCode !== 0) throw new Error(`build exited ${p.exitCode}:\n${msg}`);
    const hash = hubHash(packageFiles(entry));
    expect(existsSync(join(dir, "pkg", hash, "index.html"))).toBe(true);
    expect(readFileSync(join(dir, "pkg", hash, "index.html"), "utf8")).toContain("Local preview of an unpublished package — not on BendHub.");
    // A preview of one package is not "a subset of the hub"; its banner says what it is.
    expect(readFileSync(join(dir, "pkg", hash, "index.html"), "utf8")).not.toContain("partial build");
    expect(readFileSync(join(dir, "pkg", hash, "list.bend.html"), "utf8")).toContain("Appending the empty list on the right changes nothing.");
    expect(msg).toContain(`local package page: pkg/${hash}/index.html`);
  }, 120_000);

  test("--local rejects a missing path and a directory with a typed usage error", () => {
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-local-bad-"));
    for (const bad of [join(dir, "nope.bend"), dir]) {
      const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"), "--local", bad]);
      const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
      expect(p.exitCode).toBe(2);
      expect(msg).toContain(`build: --local: ${bad} is not a file`);
      expect(msg).toContain("usage: bun tools/docs/build.ts");
      expect(msg).not.toContain("ENOENT");
      expect(msg).not.toContain("EISDIR");
    }
  }, 120_000);

  test("--local rejects a climbing package with a typed usage error", () => {
    const root = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-climb-"));
    mkdirSync(join(root, "pkg"));
    writeFileSync(join(root, "other.bend"), "import Base\n\ndef other() -> U32:\n  7\n");
    writeFileSync(join(root, "pkg", "all.bend"), "import Base\nimport ../other.bend as Other\n\ndef f() -> U32:\n  Other.other()\n");
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--local", join(root, "pkg", "all.bend"), "--out", join(root, "dist"), "--cache", join(root, "cache")]);
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    expect(p.exitCode).toBe(2);
    expect(msg).toContain("is outside the entry directory");
    expect(msg).toContain("usage: bun tools/docs/build.ts");
    expect(msg).not.toMatch(/\n\s+at /);
  }, 120_000);

  test("--no-check drops the 'each package checked' claim from the index", () => {
    const entry = join(import.meta.dir, "..", "..", "mathlib", "fixtures", "good", "list.bend");
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-nocheck-"));
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--local", entry, "--no-check", "--out", dir, "--cache", join(dir, "cache")]);
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    if (p.exitCode !== 0) throw new Error(`build exited ${p.exitCode}:\n${msg}`);
    expect(readFileSync(join(dir, "index.html"), "utf8")).not.toContain("each package checked on bend");
  }, 120_000);
});

describe("sandbox setup failures are not statuses", () => {
  const probeFails = "#!/bin/sh\n[ \"$1\" = \"--version\" ] && exit 0\necho \"bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted\" >&2\nexit 1\n";
  // Passes the probe (no --check-only), then fails every checked file like the CI symptom.
  const checkFails = "#!/bin/sh\nfor a in \"$@\"; do case \"$a\" in *--check-only*) echo \"bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted\" >&2; exit 1;; esac; done\nexit 0\n";

  test("--require-sandbox aborts with exit 2 before any status is written", () => {
    const fake = fakeBwrap(probeFails);
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-req-"));
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--only", "bend-mathlib@0.1.0.1", "--require-sandbox", "--out", join(dir, "dist"), "--cache", join(dir, "cache")],
      { env: { ...process.env, BEND_DOCS_BWRAP: fake } });
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    expect(p.exitCode).toBe(2);
    expect(msg).toContain("sandbox required but unusable");
    expect(msg).toContain("RTM_NEWADDR");
    expect(existsSync(join(dir, "cache", "status.json"))).toBe(false);
  }, 120_000);

  test("a sandbox that passes the probe but fails every check caches no status and renders not checked", () => {
    const fake = fakeBwrap(checkFails);
    const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-sbx-"));
    const out = join(dir, "dist");
    const p = Bun.spawnSync([process.execPath, join(import.meta.dir, "..", "build.ts"),
      "--only", "bend-mathlib@0.1.0.1", "--out", out, "--cache", join(dir, "cache"), "--jobs", "4"],
      { env: { ...process.env, BEND_DOCS_BWRAP: fake } });
    const msg = new TextDecoder().decode(p.stdout) + new TextDecoder().decode(p.stderr);
    expect(p.exitCode).toBe(0);
    expect(msg).toContain("sandbox: bwrap");
    expect(Object.keys(JSON.parse(readFileSync(join(dir, "cache", "status.json"), "utf8")))).toHaveLength(0);
    expect(readFileSync(join(out, "pkg", MATHLIB, "index.html"), "utf8")).toContain("not checked");
  }, 300_000);
});

describe("a broken hub package does not abort the build", () => {
  test("one package's ensurePackage failure is listed as 'could not fetch'", async () => {
    const body = "import Base\n\ndef f() -> U32:\n  7\n";
    const manifest = `${sha256(body)} m.bend\n`;
    const fine = "0x" + sha256(manifest).slice(0, 32);
    const broken = "0x" + "b".repeat(32);
    const index = [
      { hash: fine, files: { "m.bend": Buffer.byteLength(body) }, bytes: Buffer.byteLength(body), ts: 1, desc: "fine" },
      { hash: broken, files: { "n.bend": 1 }, bytes: 1, ts: 2, desc: "broken" },
    ];
    const server = Bun.serve({
      port: 0,
      fetch(req) {
        const p = new URL(req.url).pathname;
        if (p === "/index.json") return Response.json(index);
        if (p === "/names.json") return Response.json([]);
        if (p === "/packages.json") return Response.json({ total: index.length, packages: index });
        if (p === `/${fine}/manifest`) return new Response(manifest);
        if (p === `/${fine}/m.bend`) return new Response(body);
        return new Response("not found", { status: 404 });
      },
    });
    try {
      const dir = mkdtempSync(join(process.env.TMPDIR ?? tmpdir(), "bend-docs-brokenhub-"));
      const out = join(dir, "dist");
      // Async spawn: the in-process hub must keep serving while the child fetches.
      const proc = Bun.spawn([process.execPath, join(import.meta.dir, "..", "build.ts"),
        "--only", `${fine},${broken}`, "--no-check", "--out", out, "--cache", join(dir, "cache")],
        { env: { ...process.env, BEND_HUB: `http://127.0.0.1:${server.port}` }, stdout: "pipe", stderr: "pipe" });
      const [so, se] = await Promise.all([new Response(proc.stdout).text(), new Response(proc.stderr).text()]);
      const code = await proc.exited;
      expect(code).toBe(0);
      expect(so + se).toContain("could not fetch");
      expect(existsSync(join(out, "pkg", fine, "index.html"))).toBe(true);
      const html = readFileSync(join(out, "index.html"), "utf8");
      expect(html).toContain(broken);
      expect(html).toContain("could not fetch");
    } finally {
      server.stop(true);
    }
  }, 120_000);
});
