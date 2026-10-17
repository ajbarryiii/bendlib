# bendlib-kernel-list

Frozen step-list permutations over `List`, generic over `-A: Data`. The exported API is exactly
`swap_head`, `swap_at`, `apply`, `perm_steps` and `perm`; the file's bytes are its type identity
(F3), so any edit is a different type.

- **Publish root:** `list.bend` (single file, no `all.bend`); `LICENSE` (Apache-2.0) ships with it.
- **Published** 2026-09-25 as `bendlib-kernel-list@1.0.0.0`, hash `0xb5c8145e53a6a127d611f45f602666ec`.
- bend-mathlib's `perm.bend` imports it by content hash. That hash resolves from the hub, or to this
  directory under `tools/mathlib/devlib.ts`, whose `--check` fails if these bytes drift.
