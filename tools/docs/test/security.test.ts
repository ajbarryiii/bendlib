// Hardening of untrusted hub input: HTML escaping, path containment, name validation,
// cached-manifest verification and a bounded fetch. Real code paths, no network for 1–4.

import { describe, expect, spyOn, test } from "bun:test";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, sep } from "node:path";
import { ensurePackage, fetchHub, fetchNames, NAMES_CAP, PACKAGES_PAGE, safePath, seedNames, sha256, underRoot, validNameRecords, type NameRecord } from "../src/hub.ts";
import { modPage, encPath, renderLlms, renderModule, renderPackage } from "../src/render.ts";
import type { Module, Package, Site } from "../src/model.ts";

const HASH = "0x" + "a".repeat(32);

const mod = (path: string): Module => ({ path, header: null, source: null, imports: [], foreign: [], decls: [], error: null, status: null, provedIn: {} });
const pkg = (modules: Module[]): Package => ({
  hash: HASH, ts: 0, desc: "", bytes: 0, files: modules.map((m) => ({ path: m.path, bytes: 1 })),
  names: [], licenses: [], modules, deps: [], rdeps: [], status: null,
  counts: { laws: 0, proved: 0, defs: 0, types: 0, decls: 0 },
});
const site = (p: Package): Site => {
  const g = { key: `files:${p.hash}`, latest: p, members: [p] };
  return {
    built: "2026-01-01T00:00:00Z", compiler: "2.0.27", checked: true, partial: false, local: false,
    packages: [p], byHash: new Map([[p.hash, p]]), groups: [g], groupOf: new Map([[p.hash, g]]), fetchFails: [], names: [],
  };
};

describe("hub filenames cannot inject HTML", () => {
  test("a hostile module path renders escaped, not as a tag or attribute", () => {
    const tag = "a<script>alert(1)</script>.bend";
    const attr = 'x" onmouseover="alert(1).bend';
    const p = pkg([mod(tag), mod(attr)]);
    const s = site(p);
    const html = renderPackage(s, p) + renderModule(s, p, p.modules[0]) + renderModule(s, p, p.modules[1]);
    expect(html).not.toContain("<script>alert(1)</script>");
    expect(html).not.toContain('onmouseover="alert(1)');
    expect(html).toContain("&lt;script&gt;alert(1)&lt;/script&gt;");
    expect(html).toContain("onmouseover=&quot;alert(1)");
  });
});

describe("a .. module path cannot escape --out", () => {
  test("underRoot refuses traversal and safePath rejects hostile manifest paths", () => {
    const out = mkdtempSync(join(tmpdir(), "bend-docs-out-"));
    expect(() => underRoot(out, `pkg/${HASH}/../../../evil.html`)).toThrow();
    expect(() => underRoot(out, "../evil.html")).toThrow();
    expect(() => underRoot(out, "/etc/passwd")).toThrow();
    expect(underRoot(out, `pkg/${HASH}/nat.bend.html`).startsWith(out + sep)).toBe(true);
    expect(safePath("../evil.bend")).toBe(false);
    expect(safePath('x" onmouseover=".bend')).toBe(false);
    expect(safePath("a<script>.bend")).toBe(false);
    expect(safePath("a\tb.bend")).toBe(false);
    expect(safePath("list.bend")).toBe(true);
    expect(safePath("sub/dir.bend")).toBe(true);
  });
});

describe("seedNames validates names", () => {
  const rec = (name: string, version: string): NameRecord => ({
    name, owner_login: "o", ts: 0,
    latest: { version, hash: HASH, ts: 0, desc: "" },
    versions: [{ version, hash: HASH, ts: 0 }],
  });
  test("an invalid name or version writes nothing", () => {
    const lib = mkdtempSync(join(tmpdir(), "bend-docs-lib-"));
    seedNames(lib, [rec("../../escape", "1.2.3.4"), rec("BadName", "1.2.3.4"), rec("valid-package-name", "1.2.3.4/../..")]);
    expect(existsSync(join(lib, "names"))).toBe(false);
    seedNames(lib, [rec("valid-package-name", "1.2.3.4")]);
    expect(existsSync(join(lib, "names", "valid-package-name@1.2.3.4"))).toBe(true);
  });
});

describe("a torn or hostile cached manifest is not trusted", () => {
  const cacheDir = () => {
    const cache = mkdtempSync(join(tmpdir(), "bend-docs-cache-"));
    mkdirSync(join(cache, "manifests"), { recursive: true });
    return cache;
  };
  test("ensurePackage rejects a manifest that does not hash to its name", async () => {
    const cache = cacheDir();
    writeFileSync(join(cache, "manifests", HASH), "torn");
    await expect(ensurePackage(HASH, join(cache, "lib"), cache)).rejects.toThrow(/corrupt/);
  });
  test("ensurePackage rejects a valid-hash manifest with an unsafe path", async () => {
    const cache = cacheDir();
    const text = `${"0".repeat(64)} ../evil.bend\n`;
    const hash = "0x" + sha256(text).slice(0, 32);
    writeFileSync(join(cache, "manifests", hash), text);
    await expect(ensurePackage(hash, join(cache, "lib"), cache)).rejects.toThrow(/unsafe path/);
  });
});

describe("hub fetches are bounded", () => {
  test("a stalled fetch rejects within the timeout", async () => {
    const server = Bun.serve({ port: 0, fetch: () => new Promise<Response>(() => {}) });
    try {
      const t0 = performance.now();
      await expect(fetchHub(`http://127.0.0.1:${server.port}/`, 150)).rejects.toThrow();
      expect(performance.now() - t0).toBeLessThan(5000);
    } finally {
      server.stop(true);
    }
  });
});

describe("hub names are validated (PLAN F1)", () => {
  const rec = (name: string, versions: { version: string; hash: string }[]): NameRecord => ({
    name, owner_login: "o", ts: 0, latest: { version: versions[0]?.version ?? "1.0.0.0", hash: versions[0]?.hash ?? HASH, ts: 0, desc: "" },
    versions: versions.map((v) => ({ ...v, ts: 0 })),
  });
  test("planted negative: a hostile name is dropped, a valid one is kept", () => {
    const kept = validNameRecords([
      rec("../index", [{ version: "1.0.0.0", hash: HASH }]),
      rec("valid-package-name", [{ version: "1.0.0.0", hash: HASH }]),
    ]);
    expect(kept.map((n) => n.name)).toEqual(["valid-package-name"]);
  });
  test("planted negative: a record whose versions are all malformed is dropped", () => {
    expect(validNameRecords([rec("valid-package-name", [{ version: "1.0", hash: "0xzz" }])])).toEqual([]);
  });
  test("a name with no versions is reported as such, not as invalid", () => {
    const err = spyOn(console, "error").mockImplementation(() => {});
    try {
      expect(validNameRecords([rec("reserved-name", [])])).toEqual([]);
      expect(err.mock.calls.map((c) => String(c[0]))).toEqual(["hub: skipped 1 name(s) with no versions: reserved-name"]);
    } finally {
      err.mockRestore();
    }
  });
});

describe("the name list is fetched whole", () => {
  const latest = { version: "1.0.0.0", hash: HASH, ts: 0, desc: "" };
  type Hub = { names: number; rows: { hash: string; name: string | null }[]; ignoreAfter?: boolean; ignoreAfterOnce?: boolean; record?: (name: string) => Response | null };
  // A hub like the real one (observed 2026-10-17): names.json stops at NAMES_CAP, packages.json pages by `after`.
  const serveHub = (h: Hub, seen: string[]) => { let passes = 0; return Bun.serve({
    port: 0,
    fetch(req) {
      const u = new URL(req.url);
      seen.push(u.pathname + u.search);
      if (u.pathname === "/packages.json" && Number(u.searchParams.get("after") ?? 0) === 0) passes++;
      if (h.ignoreAfterOnce && passes === 1 && u.pathname === "/packages.json") {
        return Response.json({ total: h.rows.length, packages: h.rows.slice(0, PACKAGES_PAGE).map((r) => ({ ...r, ts: 0, version: null })) });
      }
      if (u.pathname === "/names.json") {
        const all = Array.from({ length: h.names }, (_, i) => ({ name: `name-number-${i}`, owner_login: "o", ts: 0, latest }));
        return Response.json(all.slice(0, NAMES_CAP));
      }
      if (u.pathname === "/packages.json") {
        const after = h.ignoreAfter ? 0 : Number(u.searchParams.get("after") ?? 0);
        const page = h.rows.slice(after, after + PACKAGES_PAGE).map((r) => ({ ...r, ts: 0, version: r.name ? "1.0.0.0" : null }));
        return Response.json({ total: h.rows.length, packages: page });
      }
      const name = decodeURIComponent(u.pathname.replace(/^\/name\//, ""));
      return h.record?.(name) ?? Response.json({ name, owner_login: "o", ts: 0, latest, versions: [{ version: "1.0.0.0", hash: HASH, ts: 0 }] });
    },
  }); };
  const rows =(n: number, named: (i: number) => string | null) => Array.from({ length: n }, (_, i) => ({ hash: "0x" + i.toString(16).padStart(32, "0"), name: named(i) }));
  const url = (s: { port: number | undefined }) => `http://127.0.0.1:${s.port}`;

  test("names.json is asked for its cap, and a shorter list is taken whole", async () => {
    const seen: string[] = [];
    const server = serveHub({ names: 31, rows: [] }, seen);
    try {
      expect((await fetchNames(4, url(server))).length).toBe(31);
      expect(seen).toContain(`/names.json?limit=${NAMES_CAP}`);
    } finally {
      server.stop(true);
    }
  });
  test("planted negative: a names.json list as long as the cap is truncated; names only packages.json carries are still fetched", async () => {
    const seen: string[] = [];
    // 150 names on the hub; names.json shows 100, the other 50 appear only on packages.json's second and third pages.
    const server = serveHub({ names: 150, rows: rows(250, (i) => (i >= 150 && i < 200 ? null : i >= 200 ? `name-number-${i - 100}` : null)) }, seen);
    try {
      const names = (await fetchNames(4, url(server))).map((n) => n.name);
      expect(names.length).toBe(150);
      expect(names).toContain("name-number-149");
      expect(seen).toContain(`/packages.json?sort=new&limit=${PACKAGES_PAGE}&after=200`);
    } finally {
      server.stop(true);
    }
  });
  test("planted negative: packages.json pages that hold fewer packages than its total are an error, never a partial name list", async () => {
    const server = serveHub({ names: 100, rows: rows(250, () => null), ignoreAfter: true }, []);
    try {
      await expect(fetchNames(4, url(server))).rejects.toThrow(/listed 100 packages over its pages, but reports 250/);
    } finally {
      server.stop(true);
    }
  });
  test("a short packages.json read (a publish between two pages) is retried once, not fatal", async () => {
    const server = serveHub({ names: 100, rows: rows(250, (i) => (i === 249 ? "name-only-on-the-last-page" : null)), ignoreAfterOnce: true }, []);
    try {
      expect((await fetchNames(4, url(server))).map((n) => n.name)).toContain("name-only-on-the-last-page");
    } finally {
      server.stop(true);
    }
  });
  test("planted negative: a vanished name is dropped and an unreachable one keeps the listing's latest; the rest still build", async () => {
    const record = (name: string) => (name === "name-number-3" ? new Response("gone", { status: 404 }) : name === "name-number-4" ? new Response("down", { status: 503 }) : null);
    const server = serveHub({ names: 6, rows: [], record }, []);
    try {
      const names = await fetchNames(4, url(server));
      expect(names.map((n) => n.name).sort()).toEqual(["name-number-0", "name-number-1", "name-number-2", "name-number-4", "name-number-5"]);
      expect(names.find((n) => n.name === "name-number-4")!.versions).toEqual([{ version: "1.0.0.0", hash: HASH, ts: 0 }]);
    } finally {
      server.stop(true);
    }
  }, 20_000);
});

describe("hub descriptions cannot break llms.txt", () => {
  test("planted negative: a CR or newline in a description stays inside its package's one line", () => {
    const p = { ...pkg([]), desc: "first\r\n## Injected heading\r- [fake](x)\tend" };
    const lines = renderLlms(site(p)).split("\n");
    expect(lines.filter((l) => l.startsWith("## "))).toEqual(["## Packages"]);
    expect(lines).toContain(`- [${HASH.slice(0, 10)}](pkg/${HASH}/index.html): first ## Injected heading - [fake](x) end (not checked, 0/0 laws proved)`);
    expect(lines.some((l) => l.includes("\r"))).toBe(false);
  });
});

describe("module paths in links are URL-encoded", () => {
  test("planted negative: # becomes %23, and / separators survive", () => {
    expect(modPage(HASH, "a#b.bend")).toBe(`pkg/${HASH}/a%23b.bend.html`);
    expect(encPath("sub/a b#c.bend")).toBe("sub/a%20b%23c.bend");
  });
  test("a rendered package page links the encoded module URL, never the raw one", () => {
    const p = pkg([mod("a#b.bend")]);
    const html = renderPackage(site(p), p);
    expect(html).toContain(`href="a%23b.bend.html"`);
    expect(html).not.toContain(`href="a#b.bend.html"`);
  });
});
