# lawcheck

`lawcheck` looks for counterexamples to the `law`s of a Bend 2 file before anyone tries to prove them, and shrinks the ones it finds. **It never proves anything.** A ✓ only means that no counterexample turned up among the instances it tried.

## Install

```sh
curl -fsSL https://raw.githubusercontent.com/bendlib/bendlib/main/tools/lawcheck/install.sh | sh
```

It installs the binary for your OS and CPU from the newest `lawcheck-v*` release into `~/.local/bin`
(`LAWCHECK_DIR` changes that, `LAWCHECK_VERSION` pins a release), after checking it against the
release's `SHA256SUMS`. lawcheck needs `bend` installed; its first run downloads the matching
`bend.ts` (network). Or download `lawcheck-<os>-<arch>` from
https://github.com/bendlib/bendlib/releases yourself, `chmod +x` it and put it on PATH (on macOS,
clear the quarantine: `xattr -d com.apple.quarantine ./lawcheck-darwin-*`).

```sh
bun tools/lawcheck/cli.ts LAWS.bend                  # every law in the file, open or proved
bun tools/lawcheck/cli.ts LAWS.bend --law ins_sorted # one law
bun tools/lawcheck/cli.ts LAWS.bend --json           # machine output
bun tools/lawcheck/cli.ts LAWS.bend --impl other.bend  # swap the file's local import for another implementation
```

Options: `--size N` sets the depth of the exhaustive small-scope phase (default 3). `--max-instances N` caps the instances per law (default 200). `--max-nat N` bounds the random `Nat`s (default 30): half the random draws stay within `0..min(maxNat, 3·max(size, 3))`, the other half reach the full bound (the exhaustive small-scope phase is unchanged). `--seed S` seeds the random phase (default 1, so runs are reproducible, including with `--law`). `--jobs N` sets how many `bend` processes run at once, checker runs and `--native` builds and runs alike (default: 4, fewer with fewer cores or less than 2 GiB of free memory per process). `--timeout MS` sets the limit for each `bend` run (default 120000). `--mem-mb MB` sets the resident memory each `bend` process may use (default 1024, so about 4 GB at the default 4 jobs). A process killed over the memory limit has its instances bisected like a stack overflow, so the others are still decided and only an instance that alone exceeds the limit is dropped as too large to evaluate and reported, never passed. A batch that times out is split too: a timed-out run splits only while its batch (of 32) has seen fewer than 6, which isolates one slow instance down to itself and decides every other instance. When only timeouts split a batch, it spends at most 11 timed-out runs and, since halves run at once, at most 6 timeouts of wall time. Memory and overflow splits are not charged to that budget, and a rerun after a failure adds runs that stop at the next failure, so a mixed case can take more runs; it stays bounded by the halving depth (5 for a batch of 32). Instances still undecided then are reported as `timed out`, never passed, and a failure among the others is still found. A law with timed-out instances still passes when the rest pass, with the count on its line; under `--strict` any timed-out instance fails the run. In `mutate`, a mutant whose law drops more instances as too large than the unmutated code did is `unknown` as well: a memory kill can hide the instance that would have killed it. In `mutate`, a mutant with any timed-out instance is `unknown`, never `survived`. `--native` also evaluates eligible instances with a compiled program and reports where it disagrees with the checker (possible compiler or runtime bug). `--strict` makes a skipped law (`~`) a gate failure unless it is named in `--allow-skip module.law,…` (a comma-separated list; `module` is the checked file's basename without `.bend`, so `list.sorted_append` allows that law in `list.bend` only, and an entry without a module is a usage error); the mathlib gate runs with `--strict --allow-skip <list>`, where the list (in `.github/workflows/ci.yml` and the full gate in `AGENTS.md`) names the laws lawcheck cannot decide yet.

Exit codes: 0 means no counterexample was found (with `--strict`, also no disallowed skip and no timed-out instance). 1 means at least one counterexample was found, or `--strict` and a law was skipped that is not in `--allow-skip`, or `--strict` and an instance timed out (a `strict:` line names those laws; `--allow-skip` does not excuse a timeout). 2 means a usage error, a file that does not load or type-check, or a tool error (such as a `bend` that cannot be started).

`--json` output carries `schema: 1` and the exact `seed`/`size`/`maxInstances`/`maxNat` it ran with. Under `--json`, errors are written to stdout as `{"error":{"kind":…,"message":…}}` (kinds: `usage`, `load`, `source`, `module`, `error`) with the same exit code 2, instead of text on stderr.

```
✗ ins_sorted  counterexample (shrunk from x = 0n, xs = [5n, 6n] in 3 steps); 1/3 instances failed
             x = 0n
             xs = [1n]
             premise  {is_sorted([1n]) == True{} : Bool}  (holds)
             lhs  is_sorted(ins(0n, [1n])) = False{}
             rhs  True{} = True{}
             checker: expected False{} · observed True{}
✓ dbl_add     10 instances, 0 failures (sizes ≤ 3)
~ fn_binder   skipped: function-typed binder f: @_:Nat -> Nat
```

## How it works

1. **Load.** `@bendlib/reader` (the official `bend.ts` parser) lists the laws, their binders and their claims, plus every datatype and its constructors.
2. **Instantiate.** Quantity parameters become `&2`. Type parameters (`Type`, `Data`, `Kind(a)`, including `~A` template type parameters) are instantiated as `U32` and then as `Nat`, and the instance budget is split between the two. Each combination of catalog functions for the template function binders (see Known limits) is a context with its own share of the budget; when there are more contexts than `--max-instances`, the kept contexts are picked greedily to cover every pair of catalog entries first, alternating the type choices.
3. **Generate.** The first phase is an exhaustive small-scope search at depths 0..size, sampled once a depth no longer fits the budget. A seeded random phase then fills the budget. There are generators for `Nat`, `U32` (0 to 3, 4294967295 from depth 3; random values mostly as small as random `Nat`s, some up to 65536, and 1 in 20 with the top bit set. A claim that applies `U32.to_nat` to a value near 2^32 cannot be evaluated, so U32 wrap-around is exercised only through `Word(n)` laws at small widths), `Char`, `String`, `List`, `Pair`/`A & B`, `Word(n)`, and every datatype whose constructor fields can themselves be generated. That covers `Bool`, `Maybe`, `Result`, `Either`, `Cmp`, `Unit` and user types. Recursive fields are bounded by depth. A `Word(n)` width is a `Nat` literal (`Word(32n)`, so also `U32{w}`) or an earlier `Nat` binder (`for n: Nat` `for w: Word(n)`, also `-n`/`+n`): the exhaustive phase takes every word with at most `depth` bits set or clear (all words of a small width), the random phase all-zero, all-one, single-bit, top-bit and uniform words, and a width binder is drawn from 0..6, 8 and 12 (Word.to_nat at 16 bits or more builds unary Nats too large to evaluate); a shrunk width truncates its words.
4. **Evaluate (engine C, PLAN F22).** Each instance becomes `law lc_i: {lhs == rhs : T}` plus `def lc_i(): {==}`, written into a batch file in a temp directory. The batch file imports the user's file by absolute path as `U` and every other non-Base module it loads as `LCk`, and it names the user's declarations through those aliases. Batches run in parallel with `bend --check-only`. The checker checks declarations in file order and stops at the first failure. lawcheck parses `Location: lc_i` and the `expected`/`observed` pair, counts every earlier instance as passed, and re-runs the batch from `lc_i+1`. A clean batch is exactly `ALL PROOFS CHECK` and `Use --verdict for mathematical validity.` (PLAN F18); a verdict of `SOME PROOFS FAIL` with `Error: N defs rely on unsafe or foreign code:` is **not** a pass — the laws whose instances rest on `@unsafe`/foreign code are skipped, with the reliance count surfaced, so a `✓` always means the checker's own verdict was clean.
5. **Shrink.** A `Nat` shrinks toward 0, a list by dropping or shrinking elements, a datatype value to a recursive subterm, a nullary constructor, or smaller fields. All candidates for one step go into a single batch, ordered smallest first, so the checker's first failure is the best candidate.
6. **Display.** A `?g` hole on the shrunk instance makes the checker print the fully normalized goal, which gives the `lhs = …` and `rhs = …` values.

Claim kinds:
- An **equation** `{lhs == rhs : T}` is checked as described above. An equation whose type is a top-level function type (for example `{(x => f(x)) == g : A -> B}`) is skipped: definitional inequality of two functions is not a counterexample.
- A **predicate** claim that is a single application of a `Type`/`Data`-valued def, such as `le(a, b)`, is tried with `{==}`. When its goal reduces to `Unit` the claim holds and when it reduces to `Empty` it is refuted (a counterexample); any other normal form is reported as "not decidable by evaluation".
- **Implication premises** (a binder whose type is an equation or a predicate application, such as `for h: {is_sorted(xs) == True{} : Bool}` or `for ab: le(a, b)`) are evaluated first. An instance whose premise fails is dropped, and the output reports how many instances satisfied the premises. When no instance does, the law is reported as vacuous.
- A **refutation** (claim `Empty` with premises) fails when some instance satisfies all of its premises.

## Mutation mode

`lawcheck mutate LAWS.bend` checks the laws against every small mutant of the target's defs. A mutant is **killed** when some law finds a counterexample on it, **survived** when every law that passed on the unmutated code still passes (the laws do not pin that change), **unknown** when one of those laws is no longer evaluated on the mutant (skipped or errored, so it is neither killed nor a survivor), and **invalid** when it does not type-check (discarded, never a kill). A survivor can also be an equivalent mutant (same behaviour) — check it by hand. Proofs are stripped from the laws file and from the target before every run, in both modes: the defs that fill proved laws, and every def whose type is a proposition (an equation, `Empty` or a predicate application) unless a non-proof def uses it. So a mutant that changes behaviour is classified by running the laws, not by breaking a proof. The copies keep the target's local imports, and the laws file's, resolvable. A def none of whose mutants is valid is reported `no valid mutants: not tested`.

Operators: `arm-swap`/`arm-copy` (swap or copy `match` arm bodies), `literal` (`0n↔1n`, `True{}↔False{}`), `drop-succ` (`1n+E → E`), `drop-cons` (`A <> B → B`), `arg-swap` (swap adjacent call arguments), `projection` (replace the body with a parameter or a constant), `base-swap` (`Nat.is_le↔Nat.is_lt`, `&&↔||`, `Nat.add→Nat.sub`, …).

```sh
bun tools/lawcheck/cli.ts mutate LAWS.bend                 # all defs
bun tools/lawcheck/cli.ts mutate LAWS.bend --def app       # one def
bun tools/lawcheck/cli.ts mutate LAWS.bend --json          # machine output
```

```
$ bun tools/lawcheck/cli.ts mutate tools/lawcheck/test/fixtures/mut_weak.bend
lawcheck mutate 0.3.2 · tools/lawcheck/test/fixtures/mut_weak.bend (impl lib_ok.bend) · bend 2.0.38 · ≤50 instances/law
size  1/4 valid mutants killed · 3 survived · 6 invalid
      survived  arm-copy  line 12  1n+size(r) → 0n
      survived  drop-succ  line 12  1n+size(r) → size(r)
      survived  projection  line 8  match s: → 0n
app   3/3 valid mutants killed · 0 survived · 7 invalid
3 survivor(s): your laws do not pin these changes. A survivor can also be an equivalent mutant (same behaviour); check it by hand.
```

Exit codes: 0 no survivors and every valid mutant decided · 1 at least one survivor · 2 usage, load, tool error, no law was evaluated on the unmutated code, no valid mutants, or an `unknown` mutant. A target with no mutable defs is a usage error (`no mutable defs`), never `no survivors`. Plain `lawcheck` on a file with no laws still exits 0. A survivor shows a weakness of the laws for these operators; zero survivors does not prove the laws pin the def.

## Native comparison (`--native`)

For equation laws whose claim type is `Nat`, `U32`, `Bool`, or `List<Nat>`/`List<U32>`/`List<Bool>`, `--native` evaluates each instance a second way (engine N, PLAN §4.2 step 6): it emits one `main` that prints `lhs == rhs` for every instance (emitting a small recursive equality for lists, since Base has none), builds it with `bend -o`, runs it, and compares the result with the checker (engine C). Any instance where the two engines disagree is a likely compiler or runtime bug; it is reported with the instance bindings and a minimal reproduction file. A law whose claim is not such an equation, or whose harness cannot build or run, carries a `native skipped: <reason>` note instead of a silent absence.

## Known limits (v0.2)

- A law whose evaluation rests on `@unsafe` or foreign code is skipped, never passed. When the checker prints `Error: N defs rely on unsafe or foreign code:` the verdict is surfaced with its reliance count; when open proofs make bend suppress that summary (`Error: N TODOs found.`), lawcheck scans the target and its non-Base imports for `@unsafe` and skips the law with a note. That scan is conservative and file-level: any `@unsafe` in those files skips a law whose verdict was suppressed, even if that law happens not to use the unsafe def.
- Function-typed template binders (`for ~f: A -> B`) are instantiated from a small catalog of closed lambdas per instantiated signature; a signature outside the catalog (`no catalog functions for ~f: …`), a proposition-typed template binder such as `~assoc: … -> {op(op(x, y), z) == op(x, op(y, z)) : A}` (`proposition-typed template binder ~assoc: …`), a template value binder such as `for ~x: Nat` (`template binder ~x: Nat`), and a non-template function-typed binder (`function-typed binder f: …`) are skipped with that reason.
- `where` premises (`for y: B where P(y)`) are evaluated like implication premises: an instance whose premise fails is dropped and the satisfied fraction is reported. An `exs` claim (`exs y: T`) is checked by searching the generated values for a witness — a witness found within the budget passes the law, otherwise the law is skipped with `no witness found in N candidates`, N counting distinct witnesses (a `Bool` witness has 2). A witness type with no finite value is skipped with `no generator for type …`. It is never a fail: a finite search refutes nothing. Claims that are neither an equation nor a single predicate application (such as `Either<…>`) are skipped with a reason.
- Values are kept small because the checker evaluates unary `Nat`s: random `Nat`s are drawn from `0..maxNat`, but half the draws stay within `0..min(maxNat, 3·max(size, 3))`, so `--max-nat` (default 30) bounds every draw and small values stay common. Random lists have length `0..max(size+2, 8)`. An instance whose evaluation overflows the checker's unary `Nat`s (such as `Nat.pow(20n, 25n)`) is dropped as too large to evaluate and reported on the law's line; it neither passes nor fails the law, and if every instance is dropped this way the law is skipped. The reason says the claim or its premises build unary `Nat`s too large for the checker, and suggests lowering `--max-nat` only when the law has a plain `Nat` binder. A law's line adds up: `N instances` are the ones whose claim was evaluated, and with the `with premises false`, `too large to evaluate` and `timed out` ones they make up the `(G generated)`. `--json` carries the same `instances`, `premiseFalse`, `tooLarge`, `timedOut` and `generated`. A `Nat`-typed instance whose value exceeds the checker's recursion bound (about `2·10^5` constructors) is dropped the same way without spending a checker run. Types with no generator (`F32`, `Array`, `Map`, `IO`, indexed families other than `Word(n)`) make lawcheck skip the law and name the type.
- If the file, or anything it imports, fails to type-check, no instance can be evaluated, because bend re-checks imports (F8). lawcheck exits 2 and shows the checker's error. This includes a file with no laws at all: lawcheck validates the target up front, so a rejected file exits 2 rather than reporting `0 laws`. Open laws are fine.
- Hub imports (`0x…`) are re-imported by their hash, and a `name@version` import is resolved through `names/<name>@<version>` (F21), including a `name@version` import made by another hub module (nested). A module imported that way is lawchecked like any other import, and reads back in output under the alias the root gave it. Both routes are exercised hermetically (a temporary `BEND_LIB`), so no hub fetch is needed.
- The raw-text display back-map carries no filesystem-path entry for a hub module, because the generated batch imports a hub module by its canonical `0x<hash>/…` name, never by path: `bend --check-only` and the native build print that canonical name, which the same display pass already translates to the root's alias. A hub module the root did not import directly keeps its canonical `0x…` name (there is no root alias for it); a hub filesystem path is never printed. The one exception is a hub module that fails to parse or load: the loader reports its resolved path, exactly as it does for a local import, and that message is built before any alias map exists.
- A target directory is a typed load error (exit 2), never a raw stack. A target path containing whitespace is copied into the batch temp directory under a safe basename (bend `import` lines are unquoted) with its local imports rewritten to absolute realpaths; a symlink to such a path works the same way.
- Batch files are left in `$TMPDIR/lawcheck-*` (the path is printed) and are never deleted.
- lawcheck is tested only on bend 2.0.38. bend 2.0.28+ imports only paths made of plain names (a letter or `_`, then letters/digits/`_`/`-`; PLAN F3), so every file the batch must import by path — the target, a `--impl` file, and the files they import by `./`, `../` or absolute path — is checked: when it, or anything it imports, sits at a path that is not plain (a directory such as `.cache`, `-home-…` or macOS's `$TMPDIR`, or a basename such as `1st.bend` or `x.y.bend`), it is copied under `root/` in the batch temp directory with a sanitized name and its path imports pointed at importable files, and checked there; reported locations are mapped back to the original path. The scratch directory falls back to `/tmp` when `os.tmpdir()` is not itself plain (macOS).
