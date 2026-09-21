# Third-party licenses and attribution

The root [LICENSE](LICENSE) covers original contributions by material type. Existing third-party licenses and notices continue to govern the material to which they apply, including retained copies and derived portions. Inclusion in this release does not relicense external records, third-party quotations, or dependency code.

## Retained dependencies

| Dependency | Retained license |
|---|---|
| Lean | [Apache-2.0](vendor/lean4/LICENSE) and retained [third-party notices](vendor/lean4/LICENSES) |
| mathlib | [Apache-2.0](vendor/mathlib/LICENSE) |
| aesop | [Apache-2.0](vendor/aesop/LICENSE) |
| batteries | [Apache-2.0](vendor/batteries/LICENSE) |
| importGraph | [Apache-2.0](vendor/importGraph/LICENSE) |
| LeanSearchClient | [Apache-2.0](vendor/LeanSearchClient/LICENSE) |
| plausible | [Apache-2.0](vendor/plausible/LICENSE) |
| proofwidgets | [Apache-2.0](vendor/proofwidgets/LICENSE) |
| Qq | [Apache-2.0](vendor/Qq/LICENSE) |
| Cli | [MIT](vendor/Cli/LICENSE), Copyright (c) 2021 mhuisi |

The current dependency manifest pins dependency versions. File-level notices and Lean’s composite LICENSES file are preserved.

## Lean-derived replay helper

[Replay helper](tools/ReplayModule.lean) adapts `LeanChecker.replayFromImports` from [Lean 4.31.0](https://github.com/leanprover/lean4/blob/v4.31.0/src/LeanChecker.lean). The upstream notice reads: “Copyright (c) 2023 Kim Morrison. All rights reserved.” The named upstream authors are Kim Morrison and Sebastian Ullrich. This helper, including its adaptations, is distributed under [Apache-2.0](vendor/lean4/LICENSE), as an exception to the original-code MIT scope.

The adaptation checks one target module against its imported environment and adds command-line handling, declaration counts, and JSON reporting. Its required attribution is preserved here and applies to the retained helper.

## Research attribution

Ashwin Sanjay is the sole author of the independently developed research in this release. Preserve the named authors and source attributions associated with individual works; this attribution does not assert ownership of all imported material. See the [provenance note](docs/Provenance.md).
