# Completed Lean verification

The [machine-readable receipt](receipt.json) records the completed full Lean run from September 20, 2026.

- Status: **passed**
- Modules: **1,915 passed out of 1,915; 0 failed or blocked**
- Statement checks: **passed**
- Negative controls: the wrong risk constant, missing sample-size hypothesis and injected extra axiom were all rejected
- Toolchain: **Lean 4.31.0**
- Verification scope: fresh compilation, exact-module kernel replay and an audit of every declaration owned by each module

The receipt identifies the run, compiler, pinned dependency revisions, module manifest and verification tools by SHA-256. It also records SHA-256 hashes for the retained runner summary, source manifest, standard output and standard error. The source-bundle hash identifies the exact upload used by the remote job. The [release manifest](../../release-manifest.json) separately identifies the current full release, including documentation added after the run.

The verified Lean inputs in the current release match the hashes recorded in the receipt. Documentation-only additions do not change that input set. To repeat the verification, follow the [reproduction guide](../../docs/Reproducing.md).
