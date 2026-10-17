# @bendlib/reader

`@bendlib/reader` lets tools read Bend 2 source the same way the installed `bend` compiler does. It does not include a parser of its own. Instead it fetches the official `bend2/bend.ts` from github.com/bendlang/bend at the exact version that `bend version` reports, imports it with Bun, loads a file and its imports through bend.ts's own `book_load`, and lists the declarations. Each declaration comes with its kind, namespace, file:line:column, doc comment, and a signature printed by bend.ts's own `term_show`, so it reads the same as types in `bend`'s error messages. A syntax error or a missing import throws a `BendReadError` that carries the file, line and column. It never returns an empty result.

## Usage

```sh
bun tools/reader/cli.ts research/experiments/glist.bend           # table of the file's own declarations
bun tools/reader/cli.ts research/experiments/glist.bend --json    # the same as JSON
bun tools/reader/cli.ts file.bend --all                           # also imported (non-Base) declarations
bun tools/reader/cli.ts file.bend --check                         # also type-check (bend.ts book_valid)
bun tools/reader/cli.ts file.bend --bend-src ~/src/bend --bend-lib /tmp/mylib
```

Exit codes: 0 means the declarations were listed. 1 means a load, parse, check or source error, printed on stderr with its location. 2 means a usage error.

## API (`index.ts`)

```ts
bendSource(opts?: { version?, src?, bin? } | version): Promise<BendSource>
  // { version, dir, bendTs, origin: "cache" | "fetched" | "local", archiveSha256?, commit? }
installedVersion(bin?): string             // "2.0.37"
importBend(src, { bendLib?, bendHub? })    // the bend.ts module instance
load(file, { bendLib?, bendHub?, check?, src?, version?, bendSrc? }): Promise<Loaded>
  // Loaded = { bend, source, book, file, n0, files, own[], imported[], base[], checked }
decls(loaded, { scope?: "own" | "all-non-base" | "all" }): Decl[]
show(bend, hoasTerm, bnd?): string         // term_show(term_lower(t)): how bend prints types
BendReadError { file, line, column, def, bendMessage }  // bendMessage = bend.ts err_show output
inNamespace(key, ns): boolean; localName(key, ns): string  // a key's namespace prefix, either separator
printedName(key): string                   // the key as bend prints it: ns:name -> ns.name
```

`Decl.name` is the key bend.ts uses: `ns.name` up to 2.0.34, `ns:name` from 2.0.35 (bend prints
both as `ns.name`). Use `inNamespace`/`localName` instead of splitting on a separator.

```ts
type Decl = {
  name; namespace; kind: "type" | "ctor" | "def" | "law" | "template" | "effect" | "unsafe";
  origin: "own" | "imported" | "base"; file; line; column;
  doc: string | null;          // contiguous `#` lines directly above, "# " stripped
  signature: string;           // e.g. @a:Quant -> @-A:Kind(a) -> @xs:List<a, A> -> {List.append(a, A, xs, []) == xs : List<a, A>}
  statement?: { lhs; rhs; type };                      // type ends in {lhs == rhs : type}
  binders?: { name; quant: "affine" | "reusable" | "erased" | "template"; type }[]; // laws and equality-typed defs
  proved?: boolean; proof?: { line; column };          // laws
  unsafe?; effects?: string[]; templates?: number; predicate?: boolean;
  ctors?: string[];            // kind "type"
  type?: string;               // kind "ctor": its datatype
}
```

How kinds are assigned: a declaration written with `law` is a `law`, with `proved` true once a `def` fills it. Otherwise the first rule that matches wins: `u` set means `unsafe`, `i` (foreign imports) set means `effect`, a leading `~` parameter means `template`, and everything else is `def`. A datatype is `type`, and each of its constructors is a `ctor`. `predicate` marks a def or law whose type ends in a kind (`Type`, `Data`, `Kind(..)`).

## Version-matching rule

The reader always parses with the bend.ts whose `bend2/main.ts` declares `const VERSION = "<v>"`, where `<v>` is the output of `bend version` for `BEND_BIN`, falling back to `~/.bend/bin/bend` and then to `bend` on `PATH`.

1. If `{src}` or `BENDLIB_BEND_SRC=<dir>` is set, that local checkout is used. Its declared VERSION must equal `<v>`, or the reader throws.
2. Otherwise it uses `~/.cache/bendlib/bend/<v>/` (the root can be moved with `BENDLIB_CACHE`). On every reuse it re-hashes the cached `v<v>.tar.gz` against `archive.sha256` and `manifest.json`, and re-hashes `bend2/bend.ts`, `main.ts` and `base.bend` against the hashes recorded when the archive was extracted. Any mismatch throws.
3. If the cache is missing, the reader fetches `https://github.com/bendlang/bend/archive/refs/tags/v<v>.tar.gz`. A 404 means there is no such tag, and the reader throws. It then checks that the extracted `bend2/main.ts` declares `<v>`, records the archive's sha256 and the tag's commit (from the GitHub API, best effort), and moves everything into the cache.

For 2.0.37, tag `v2.0.37` points to commit `4ff8545f`, and the tag archive sha256 is `04b3ff5838f601ed611f37f822c0054fb583fba78d0e86a68fadd7239f4cfa5f`.

## Known limits

- **Only tested on bend 2.0.37.** The goldens prove behaviour on that version and nothing more. bend.ts is an internal module whose exports can change, so rerun `bun test` whenever the compiler updates. If the goldens differ, review the change and then run `bun test/golden.ts`.
- **The archive hash is trust-on-first-use.** GitHub publishes no checksums for tag archives. The first fetch records the sha256, and later runs detect changes against it. The first fetch itself is only as trustworthy as HTTPS to github.com.
- **Signatures show the type as declared, not normalized.** They use bend's own printer, so a plain arrow prints as `@_:A -> B` and `Nil{}` prints as `[]`, exactly as in `bend`'s error messages.
- **Positions are recovered from spans.** bend.ts keeps no span for a declaration itself. The reader takes the span of the declaration's type, maps its text back to a file, and searches backwards for `def|type|law <name>`, which must be the first token on its line. If that search fails, the reader throws. It never guesses. Constructors carry no span, so they are found in order after their type's header. `proof` is reported only when the filling `def` is in the same file as the law.
- **No type-checking by default.** `load` only parses and elaborates, like `book_load`. Pass `check: true` (or `--check`) to also run `book_valid`.
- **`BEND_LIB` is read when bend.ts loads.** bend.ts reads `BEND_LIB` and `BEND_HUB` once, when the module is evaluated. The reader therefore imports a separate bend.ts instance for each distinct `(bendLib, bendHub)` pair. As with `bend` itself, loading a hub package by hash writes it into that `BEND_LIB`. Pass a private directory so that `~/.bend/lib` is never touched. Importing a package by `name@version` also writes into `BEND_LIB/names/`.
- **Base comes from the fetched source.** Base is loaded from the fetched `bend2/base.bend`, not from `~/.bend/bend2/base.bend`. At 2.0.37 the two files are byte-identical.
- **Tests clean up after themselves.** They create their temp directories (a private `BEND_LIB`, a copy of the cache for the tamper test) under `$TMPDIR` and remove them when done.
