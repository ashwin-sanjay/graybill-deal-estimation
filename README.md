# Graybill–Deal Common-Mean Estimation:
### *Admissible Strict Improvements, Exact Uniform-Gain Classification, Sharp Oracle Minimax Limits, and Exact Risk and Inference*

![Lean 4.31.0](https://img.shields.io/badge/Lean-4.31.0-345b80)

For independent normal samples with a shared mean and unknown, possibly unequal variances, these results connect strict improvement of Graybill–Deal with admissibility and sharp minimax limits. They establish improvements at every design with at least two groups and at least two observations per group, classify the attainable uniform percentage gains for two groups, and quantify performance relative to an estimator that knows the variances.

This evidence release contains the result statements, Lean proofs, complete standalone written proofs, numerical certificates, and verification records.

[Results](#results) · [Proof evidence](#proof-evidence) · [Verification](#verification) · [Reproduce](#reproduce) · [Provenance](#provenance)

## Results

The setting is squared-error estimation of a shared mean from $k\ge2$ independent normal groups, with unknown positive variances and sample sizes $n_i\ge2$. The Graybill–Deal (GD) estimator weights the sample means using estimated inverse variances.

1. **Strict improvement and admissibility.** For every such design, there is a finite-risk Borel estimator that strictly improves on GD at every parameter, is admissible against all Borel competitors, and minimizes the worst risk ratio to GD. Such an estimator cannot retain full location–scale equivariance. For two samples, GD remains admissible among linear rules with sample-variance-only weights summing to one. [Restricted admissibility](docs/Evidence.md#result-0025) · [Strict completion](docs/Evidence.md#result-0029) · [Relative optimum](docs/Evidence.md#result-0022).

2. **Exact limits on uniform percentage gains.** For two samples, a fixed positive percentage reduction in risk at every parameter is possible exactly at $(2,3)$, $(3,2)$ and $(3,3)$. Other two-sample designs still admit strict improvement at every parameter, but no positive uniform percentage gain. [Evidence](docs/Evidence.md#result-0008).

3. **Sharp oracle minimax limits.** Normalizing risk by the optimal known-variance estimator gives an attained minimax value, finite exactly when $(n_i-1)(n_j-1)\ge4$ for every distinct pair. At $(3,3)$ the exact value is $1+\pi/4$, with an explicit attaining rule. At every two-sample design with finite value, requiring GD domination strictly raises the optimum. [Finiteness](docs/Evidence.md#result-0031) · [Exact value and written proof](docs/Evidence.md#result-0013) · [Incompatibility](docs/Evidence.md#result-0019).

4. **Near-oracle performance as samples grow.** For $k\ge3$ and all $n_i\ge4$, an admissible strict GD improvement has worst oracle risk ratio at most $1+\frac{k-1}{2}\sum_i(n_i-3)^{-1}$. This bound approaches one as all sample sizes grow with $k$ fixed; a positive adaptation cost remains at each fixed design. [Evidence](docs/Evidence.md#result-0015).

5. **Exact inference and likelihood structure.** Exact common-mean confidence intervals use every group and have uniformly bounded expected width relative to the oracle standard error. For two samples with positive residual scatters, the likelihood has at most two global maximizers. [Confidence intervals](docs/Evidence.md#result-0006) · [Likelihood](docs/Evidence.md#result-0032).

The [complete result-to-evidence guide](docs/Evidence.md) gives precise hypotheses and supporting sources. The [release scope](docs/Scope.md) covers all 34 result groups.

### Named final results

The following 20 named results link directly to their statements and evidence. Each result links to its exact statement; the family links give the written proof and supporting evidence. Here $R_\theta$ is squared-error risk, and $\sigma_i$ (or $\sigma,\tau$) denotes a population standard deviation.

#### Real-shape eight-tent construction

For each fixed positive shape pair, the reduced Gamma construction supplies an explicit correction; its Gaussian specialization uses integer sample sizes $m,n\ge2$.

[Written proof](proofs/Proof0001.md) · [Proof sources](docs/Evidence.md#result-0026).

| Named result | Statement |
|---|---|
| [Real-shape reduced-risk improvement](docs/Evidence.md#named-0016) | For every fixed $\alpha,\beta>0$, at most eight normalized product tents and one positive step strictly reduce the reduced risk for every $e\in(0,1)$. |
| [Physical Gaussian strict improvement](docs/Evidence.md#named-0013) | For every $m,n\ge2$, the coherent correction gives a finite-risk Borel rule that strictly improves GD at every common mean and pair of positive scales. |
| [Balanced rank obstruction](docs/Evidence.md#named-0003) | For every $\gamma>0$, the specified balanced four-channel system has rank three; adjoining the constant target raises the rank to four, so that target is outside its span. |

#### Historical two-stage descent and packet floor

At the $(2,2)$ design, use the written eight-tent seed $d_a$ with $\eta=10^{-5}$ and $a=1/250$, and the two-bump correction $\widetilde d$ with $\rho=10^{-12}$ and $t=10^{-4}$.

[Written proof](proofs/Proof0002.md) · [Proof sources](docs/Evidence.md#result-0026).

| Named result | Statement |
|---|---|
| [First physical strict margin](docs/Evidence.md#named-0009) | At every physical parameter, $R_\theta(GD)-R_\theta(d_a)>\frac{351\eta^2\sigma^4\tau^4}{500000\pi(\sigma^2+\tau^2)^3}>0$. |
| [Doubled-step counterexample](docs/Evidence.md#named-0007) | At population scales $(19,1)$, doubling the seed step worsens risk: $R_\theta(d_{2a})>R_\theta(d_a)$. |
| [Second physical strict descent](docs/Evidence.md#named-0018) | The specified two-bump correction satisfies $R_\theta(\widetilde d)<R_\theta(d_a)$ at every physical parameter. |
| [Positive finite-packet floor](docs/Evidence.md#named-0015) | For this fixed seed, every finite nonnegative weighted packet with weight-one reference atom $(\mu,\sigma,\tau)=(0,1,1)$ has posterior error $B_a>27t^2\rho^2/131072>10^{-36}$. |

#### Double-Haar domination and degree-six obstruction

At the $(11,11)$ design, written integral arguments and directed numerical certificates supply the physical enclosures used by the linked Lean implications.

[Written proof](proofs/Proof0003.md) · [Proof sources](docs/Evidence.md#result-0026).

| Named result | Statement |
|---|---|
| [Physical double-Haar domination](docs/Evidence.md#named-0014) | The finite-risk Borel double scale-Haar posterior mean strictly improves GD for every positive variance ratio. |
| [Degree-six weak-improvement exclusion](docs/Evidence.md#named-0005) | Every nonzero correction in the specified ten-dimensional degree-six correction class increases the Haar rule's physical risk at some positive variance ratio. |

#### Native (3,3) minimax and its consequences

The written packet argument and linked Lean results connect the reduced coefficient problem to oracle-normalized risk in the physical Gaussian experiment.

[Written proof](proofs/Proof0004.md) · [Proof sources](docs/Evidence.md#result-0013).

| Named result | Statement |
|---|---|
| [Reduced minimax and dual nonattainment](docs/Evidence.md#named-0017) | The reduced minimax value is $\pi/4$, attained by the squared-precision coefficient; no finite interior mixture attains the dual supremum. |
| [Exact unrestricted native minimax](docs/Evidence.md#named-0008) | At $(3,3)$, the minimax values over all Borel, finite-risk Borel and affine finite-risk rules equal $1+\pi/4$, attained by the squared-precision rule with midpoint fallback. |
| [Size-three-pair lower bound](docs/Evidence.md#named-0020) | Every ordinary many-group design containing two distinct groups of size three has oracle minimax value at least $1+\pi/4$. |
| [Both-sample-means impossibility](docs/Evidence.md#named-0004) | At $(3,3)$, no Borel estimator has risk at most $\min(\sigma^2/3,\tau^2/3)$ at every physical parameter. |
| [GD-relative gain ceiling](docs/Evidence.md#named-0010) | At $(3,3)$, the all-Borel uniform relative gain over GD obeys $\Gamma_{3,3}\le1/2-\pi/8$. |

#### Two-observation exact risk and limiting behavior

For $k\ge1$ independent groups with two observations each, the written Gaussian integral calculation and linked Lean identities give the following results.

[Written proof](proofs/Proof0005.md) · [Proof sources](docs/Evidence.md#result-0027).

| Named result | Statement |
|---|---|
| [All-two physical exact risk](docs/Evidence.md#named-0001) | At every common mean and positive scale vector, $R_\theta(GD)=\frac14\left[\frac{\sum_i\sigma_i}{\sum_i\sigma_i^{-1}}+\frac{k}{(\sum_i\sigma_i^{-1})^2}\right]$. |
| [Sharp oracle ratio and equal-scale risk](docs/Evidence.md#named-0019) | The oracle-normalized GD risk is at least $(k+1)/2$, with equality at equal scales; there GD risk is $\sigma^2(k+1)/(4k)$ and oracle risk is $\sigma^2/(2k)$. |
| [Nonvanishing equal-scale risk](docs/Evidence.md#named-0012) | For fixed $\sigma>0$, the equal-scale GD risk stays above $\sigma^2/4$ as the number of groups grows. |
| [Divergent three-group risk](docs/Evidence.md#named-0006) | Along the positive scale curve $(1,1,r)$, GD risk exceeds $r/8$ and diverges as $r\to\infty$. |
| [Almost-sure deletion and finite limiting risk](docs/Evidence.md#named-0002) | Along that curve under the fixed Gaussian coupling, GD converges almost surely to the first-two-group GD rule, whose risk is $3/8$. |
| [Nonuniform integrability](docs/Evidence.md#named-0011) | The squared losses along that curve are not uniformly integrable; their expectations diverge although the almost-sure limiting loss has expectation $3/8$. |

## Proof evidence

- **[Result-to-evidence guide](docs/Evidence.md):** theorem statements, proof sources, computational support, and conditional premises.
- **[Complete standalone written proofs](docs/Proofs.md):** all five written-proof families, retaining their full arguments, assumptions, and dependencies.

## Verification

The [statement-to-evidence guide](docs/Evidence.md) identifies Lean statements and their hypotheses, complete written arguments, and numerical certificate inputs. Some statistical conclusions combine written analytic proofs and numerical certificates with Lean theorems whose premises specify bounds or identities. The guide identifies which parts Lean checks and which parts the written or numerical arguments establish. The [supplied numerical verification record](certificates/verification/result.json) lists the finite checks and outcomes. The [completed Lean verification receipt](verification/lean/README.md) records a full run in which all 1,915 modules passed compilation, exact-module kernel replay and owned-declaration axiom audit, together with passing statement checks and negative controls. The [Lean module manifest](verification/modules.json) specifies the modules and control inputs for that run.

## Reproduce

The [reproduction guide](docs/Reproducing.md) describes integrity checks, numerical certificate checks and Lean verification with the pinned toolchain. The [statement-to-evidence guide](docs/Evidence.md) links mathematical statements to their proof sources.

## AI use

The results in this project were obtained using an early version of a proprietary AI research system. Further results and next steps will be cataloged on a new website for this project, [palanquinai.com](https://palanquinai.com).

## Provenance

Current file identities are recorded in the [release manifest](release-manifest.json). The [provenance note](docs/Provenance.md) explains the retained research chronology and supporting records.

### Acknowledgment

I acknowledge [Dale Matthews’s valuable work](https://github.com/dalematthews/graybill-deal-inadmissibility) on the Graybill–Deal problem. While some of his results overlap with mine, I developed this research independently, without relying on his work. My retained internal research records date my initial proof of the Graybill–Deal estimator’s inadmissibility at (11,11), by construction of an explicit everywhere-strict dominating estimator, to **July 9, 2026**, preceding his initial public release on **July 24, 2026**. The chronology and supporting records are documented in the [provenance note](docs/Provenance.md).

## License

Original software, Lean source, and executable tooling use MIT; original mathematical exposition, written proofs, and documentation use CC BY 4.0. See [LICENSE](LICENSE) for these scopes and [third-party notices](THIRD_PARTY_NOTICES.md) for retained terms and exceptions.
