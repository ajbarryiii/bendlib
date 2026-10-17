// hash: compute the BendHub content hash of a package, exactly as `bend --publish` does
// (bend2/main.ts cli_publish + pkg_files): the entry at its basename, every local import (read
// like bend.ts book_load: `./x.bend`, `x.bend`, indented or commented) at its path, every foreign `.c`/`.js` a def imports (tld.i, main.ts:646-648) at its path, a
// LICENSE beside any file; "0x" + sha256 of "sha256(content) path\n" lines, 32 hex.
//
// A path that climbs above the entry's directory (`../`) is refused (exit 2): bend re-roots such
// a package at an ancestor and drops the ancestor's name (main.ts:639-644), so we cannot mirror
// its keys without a verified hub package to check the result against.
// usage: bun tools/mathlib/hash.ts <entry.bend>   (hash on stdout, files on stderr)
// exit: 0 printed · 2 usage (missing, non-file, or climbing entry)

import { createHash } from "node:crypto";
import { existsSync, readFileSync, statSync } from "node:fs";
import { basename, dirname, join, normalize, relative } from "node:path";
import { PkgError, importPaths, isHubImport } from "./lib.ts";

const USAGE = "usage: bun tools/mathlib/hash.ts <entry.bend>";
const usage = (msg: string): never => { console.error(`hash: ${msg}\n${USAGE}`); process.exit(2); };

const sha256 = (s: string) => createHash("sha256").update(s).digest("hex");

export function hubHash(files: Record<string, string>): string {
  const lines = Object.keys(files).sort().map((p) => sha256(files[p]) + " " + p + "\n");
  return "0x" + sha256(lines.join("")).slice(0, 32);
}

// A def's foreign effect files, recorded by bend's parser as indented `import "./f.c"` lines (bend.ts:2605-2616).
const FOREIGN = /^\s+import\s+"([^"]+)"/gm;

/** Collect the files `bend <entry> --publish` would upload (local and foreign imports; hub imports stay out). */
export function packageFiles(entry: string): Record<string, string> {
  if (!existsSync(entry) || !statSync(entry).isFile()) throw new PkgError(`not a .bend file: ${entry}`);
  const root = dirname(entry);
  const files: Record<string, string> = {};
  // bend drops a leading BOM before hashing (main.ts pkg_files).
  const read = (file: string): string => {
    try { return readFileSync(file, "utf8").replace(/^﻿/, ""); }
    catch { throw new PkgError(`cannot read ${file}`); }
  };
  const key = (file: string, at: string): string => {
    const k = normalize(at);
    if (k.startsWith("..") || k.startsWith("/")) {
      throw new PkgError(`${file} is outside the entry directory ${root}; bend re-roots such a package at an ancestor, which this tool refuses`);
    }
    if (k.split("/").slice(0, -1).some((s) => s.toLowerCase() === "license")) {
      throw new PkgError(`${file} is in a directory named license, which bend refuses to publish`);
    }
    return k;
  };
  const add = (file: string, k: string): void => {
    if (k in files) return;
    files[k] = read(file);
    const lic = join(dirname(file), "LICENSE");
    if (existsSync(lic)) files[join(dirname(k), "LICENSE").replace(/^\.\//, "")] = read(lic);
  };
  const visit = (file: string): void => {
    const k = file === entry ? basename(entry) : key(file, relative(root, file));
    if (k in files) return;
    add(file, k);
    const text = files[k];
    for (const p of importPaths(text)) if (!isHubImport(p)) visit(join(dirname(file), p));
    for (const m of text.matchAll(FOREIGN)) {
      if (!/\.(c|js)$/.test(m[1])) continue;
      const real = join(dirname(file), m[1]);
      add(real, key(real, join(relative(root, dirname(file)), m[1])));
    }
  };
  visit(entry);
  return files;
}

if (import.meta.main) {
  const entry = process.argv[2];
  if (!entry) usage("need <entry.bend>");
  let files: Record<string, string>;
  try { files = packageFiles(entry); } catch (e) { if (e instanceof PkgError) usage(e.message); throw e; }
  console.log(hubHash(files));
  for (const p of Object.keys(files).sort()) console.error(`  ${p}`);
}
