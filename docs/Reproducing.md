# Reproducing the evidence

Use the pinned Lean toolchain and dependency versions supplied with this package. The [statement-to-evidence guide](Evidence.md) connects each mathematical statement to its corresponding sources and evidence type. Import the module linked for a result; the verifier checks each module in its own dependency context, preserving the separate variants used by different proofs.

Release integrity checks compare current file hashes and sizes. Lean checks compile the current source closure, replay project declarations and inspect their axiom dependencies. Statistical bridges check that selected theorem types match the separately written physical propositions. These checks preserve the actual premises of conditional statements.

The numerical suite checks the arithmetic engine, positive interval simplex, continuum interpolation, two wall-cover checkers, eight-tent symbolic identities and the two-stage exact rational certificate. The two-stage auxiliary tests check four additional regressions. Directed-enclosure producers supply the interval inputs; finite checks of those inputs and regeneration of the enclosures have distinct scopes.

Run the current release and source checks from the release root:

```sh
python tools/verify_release.py
python3 tools/verify_lean.py --static
```

Install the pinned numerical dependencies in a separate Python environment and run the finite suite in a new work directory outside the release:

```sh
python -m pip install -r certificates/requirements.txt
python -B tools/verify_certificates.py --work /absolute/path/outside/release/new-certificate-work
```

The [numerical evidence guide](../certificates/README.md) describes directed-enclosure regeneration separately from the finite suite and links the exact input identities. The [finite-suite record](../certificates/verification/result.json) records the supplied suite's executed checks.

For the Lean checks, prepare Lean 4.31.0 and the pinned dependencies from `lake-manifest.json`, including their matching build cache, then run:

```sh
lake env python3 tools/verify_lean.py --jobs 4 --emit-audits
```

The dependency libraries and their upstream build cache form the trusted dependency boundary. The command checks the current public modules and their owned declarations, replays them against the imported environment, and runs statement, nonvacuity and negative controls. Dependency setup and cache hydration precede this proof-verification command.

The [supplied finite-suite record](../certificates/verification/result.json) identifies the executed numerical checks and outcomes. The [completed Lean verification receipt](../verification/lean/README.md) records a full passing run, and its [machine-readable record](../verification/lean/receipt.json) identifies the verified inputs, toolchain, dependency revisions, statement controls and retained run artifacts by SHA-256. The [Lean module manifest](../verification/modules.json) fixes the Lean modules, source hashes and control inputs for that run. Running the Lean command above produces a new execution report. Written analytic arguments retain the role specified in the [proof guide](Proofs.md).
