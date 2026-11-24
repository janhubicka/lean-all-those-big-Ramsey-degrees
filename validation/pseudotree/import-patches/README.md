# Local import-only validation variant

The package pins the original upstream commits in `lakefile.toml` and
`lake-manifest.json`. The local validation run used detached copies of those
commits with the two import-only patches in this directory applied. These
patches replace `import Mathlib` in `Milliken/AmbientTree.lean` and
`RamseySpace/Basic.lean` with narrower imports, and add the previously implicit
`Mathlib.Order.Sigma` import to `HeterogeneousWedgeOrder.lean`. Every line
outside those import blocks is unchanged. In particular, no definition, theorem statement, proof,
axiom, compiler option, or dependency pin was changed.

The purpose is practical: importing the whole Mathlib library caused each
upstream module to use about 4.5–5 GB of memory and to take tens of seconds
in the validation environment. The narrower imports let the same proof
bodies compile in roughly two seconds per upstream module.

`source-integrity.json` records both pinned commits and SHA-256 hashes of
the three source files before and after patching. It also records the common
hash of each file with import lines removed. The original upstream checkout
remains an alternative build route; these patches are not applied by Lake
automatically.

## Reproduce the local variant

From `validation/pseudotree`, after `lake update` and the usual Mathlib cache
download, the optional patches can be applied to the freshly fetched
dependency checkouts:

```sh
git -C .lake/packages/milliken apply --check ../../../import-patches/milliken.patch
git -C .lake/packages/milliken apply ../../../import-patches/milliken.patch
git -C .lake/packages/ramsey-space-todorcevic apply --check ../../../import-patches/ramsey-space.patch
git -C .lake/packages/ramsey-space-todorcevic apply ../../../import-patches/ramsey-space.patch
LEAN_NUM_THREADS=2 lake build PseudotreeValidation
```

The paths above assume ordinary Lake dependency directories rather than
symlinks. If local dependency directories are symlinks, pass the absolute
patch paths to `git apply` instead. Apply the patches only to disposable
dependency checkouts: they intentionally leave those checkouts with a
visible import-only diff.

The narrower imports change only the dependency graph. Coverage is determined
by the actual local theorem statements and their checked proof dependencies;
see the package README and audit for the final endpoints and their scope.
