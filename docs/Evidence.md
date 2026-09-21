# Statement-to-evidence guide

The statements below retain their hypotheses, competitor classes and evidence types. Each source link identifies the corresponding current mathematical evidence.

[Written proofs](Proofs.md) · [Scope](Scope.md) · [Reproduction](Reproducing.md)

## Results

| Mathematical statement |
|---|
| [Why the risk normalization and experiment matter](#result-0034) |
| [Full-summary reduction, purification, and the exact risk cost](#result-0018) |
| [Exact conditions for transporting a comparison to another experiment](#result-0012) |
| [Residual admissibility, coefficient rigidity, and the exact restricted cap](#result-0025) |
| [A class-preserving repair and a distinct residual-admissible family](#result-0001) |
| [Clipping, automatic finite risk, and a quantitative coefficient obstruction](#result-0007) |
| [Strict seeds and their tunable correction rays](#result-0028) |
| [Retained explicit examples and finite-dimensional construction limits](#result-0026) |
| [Strict terminal completion and the symmetry that can be retained](#result-0029) |
| [Conditional partial-symmetry characterization](#result-0010) |
| [One strict terminal rule attains the relative optimum, with singular limiting priors](#result-0022) |
| [Complete native gain classification and the surviving many-group bounds](#result-0008) |
| [The complete oracle-finiteness boundary and its residual restriction](#result-0031) |
| [Explicit finite-cap pair selectors, including the critical designs](#result-0014) |
| [The actual symmetric pair aggregator and its oracle bound](#result-0030) |
| [Exact unrestricted value at (3,3), attained by a displayed rule](#result-0013) |
| [GD domination and unrestricted oracle minimaxity are incompatible exactly at finite native values](#result-0019) |
| [Affine admissibility and minimaxity have different attaining rules](#result-0004) |
| [Sharp GD envelopes, exact small-sample risks, and nonuniform integrability](#result-0027) |
| [All native boundary rates, with exact leading constants](#result-0005) |
| [Explicit near-oracle strict terminal caps and a positive adaptation cost](#result-0015) |
| [Positive affine-character gauges and separately selected cap-preserving endpoints](#result-0023) |
| [Finite physical posterior duality and robust infeasibility certificates](#result-0016) |
| [Admissible posterior examples, deficiency criteria, and distance bounds](#result-0003) |
| [Finite-stage nonattainment and a convergent posterior sequence for one selected completion](#result-0017) |
| [What a finite primal–dual gap and a multiplier error certify](#result-0033) |
| [Conditional effective stopping from energy certificates](#result-0009) |
| [A sharp three-rule disagreement-to-gain identity](#result-0002) |
| [Native variable envelopes retain their exact bounds under projective reduction](#result-0021) |
| [Radial moment constraints on native terminal projections](#result-0024) |
| [Cone values, transported optimizers, and exact symmetry regret](#result-0011) |
| [Identical collar profiles do not identify a rule inside the canonical cap](#result-0020) |
| [An exact covariant interval that essentially uses every group](#result-0006) |
| [The positive-scatter common-mean likelihood has at most two maximizers](#result-0032) |

<a id="result-0034"></a>

### Why the risk normalization and experiment matter

Multiplying each parameter's loss by any strictly positive parameter-only factor preserves dominance, admissibility and terminality at the same competitor scope. It need not preserve the minimax objective: the order of risks at each parameter is different information from their supremum after normalization. Indeed, every Borel estimator in the full Gaussian location–scale experiment has infinite **unnormalized** worst squared risk.

Restriction to a submodel preserves weak risk inequalities, but a strict domination assertion survives only when a strict witness remains in that submodel. The specified finite two-rule countermodels show that neither direction of admissibility transfer, nor minimax invariance under positive normalization, holds automatically. The countermodels are finite comparison experiments.

[Supporting result](../GD/Module0039.lean), [Supporting result](../GD/Module0247.lean).

**Evidence sources**

- [Lean source](../GD/Module0039.lean)
- [Lean source](../GD/Module0552.lean)
- [Lean source](../GD/Module0247.lean)
- [Lean source](../GD/Module0247.lean)
- [Lean source](../GD/Module0810.lean)
- [Lean source](../GD/Module0810.lean)
- [Lean source](../GD/Module0984.lean)
- [Lean source](../GD/Module0984.lean)

<a id="result-0018"></a>

### Full-summary reduction, purification, and the exact risk cost

For every ordinary design, raw Borel rules, Borel functions of the full summary, and arbitrary randomized Markov action kernels have the same feasible extended risk budgets whenever the budget is finite at one reference parameter. This also holds for arbitrarily indexed simultaneous budgets with one finite reference bound. At a target with finite risk at every parameter, the corresponding admissibility and terminality predicates agree; a randomized weak dominator of a terminal rule must be its Dirac kernel under every physical law.

More precisely, let \(K(X,da)\) have finite squared risk at every parameter, let \(m(X)\) be its Borel-repaired barycenter, and let \(h(S)\) be its common full-summary conditional projection. Then
\[
R_\theta(K)=R_\theta(h)
 +\mathbb E_\theta[(m-h)^2]
 +\mathbb E_\theta[\operatorname{Var}(a\mid X)].
\]
Thus both unused nonsummary information and action dispersion have explicit nonnegative costs. Strict improvement is preserved by the reductions. Covariance transport holds at the stated common-null/class scope under the kernel covariance and moment hypotheses.

The general mechanism is a risk-preserving embedding with a risk-improving left-inverse projection. It preserves all pointwise budget feasibility, infima of every monotone risk-profile objective, and existence of their minimizers. Terminality additionally requires rigidity of the weak-dominator fiber; a faithful nonnegative additive risk cost at a finite reference risk supplies it. Such reductions compose and their costs add. The theorem transports existing minimizers through those reductions.

[Supporting result](../GD/Module1646.lean), [Supporting result](../GD/Module1638.lean), [Supporting result](../GD/Module0553.lean), [Supporting result](../GD/Module0160.lean).

**Evidence sources**

- [Lean source](../GD/Module1646.lean)
- [Lean source](../GD/Module1640.lean)
- [Lean source](../GD/Module1641.lean)
- [Lean source](../GD/Module1892.lean)
- [Lean source](../GD/Module1638.lean)
- [Lean source](../GD/Module1639.lean)
- [Lean source](../GD/Module1644.lean)
- [Lean source](../GD/Module1647.lean)
- [Lean source](../GD/Module1648.lean)
- [Lean source](../GD/Module0553.lean)
- [Lean source](../GD/Module1645.lean)
- [Lean source](../GD/Module0160.lean)
- [Lean source](../GD/Module0939.lean)
- [Lean source](../GD/Module0815.lean)

<a id="result-0012"></a>

### Exact conditions for transporting a comparison to another experiment

Preserving every squared-risk ordering at one fixed target identifies a probability law. Under matching observation laws, terminality of a lifted rule is equivalent to terminality in the smaller experiment **and** the following descent condition: every weak dominator in the larger experiment has a single Borel representative in the smaller experiment, valid under every parameter law.

Correct marginalization alone therefore does not transfer a GD comparison. In the specified deletion from a native \((3,3)\) sample to \((2,2)\), two raw datasets have identical retained observations but original GD values \(0\) and \(1/5\). These two datasets establish pointwise nonfactorization. Matching the baseline and descending all dominators remain separate conditions.

[Supporting result](../GD/Module1414.lean).

**Evidence sources**

- [Lean source](../GD/Module1414.lean)
- [Lean source](../GD/Module1415.lean)
- [Lean source](../GD/Module0357.lean)
- [Lean source](../GD/Module1448.lean)
- [Lean source](../GD/Module1648.lean)

<a id="result-0025"></a>

### Residual admissibility, coefficient rigidity, and the exact restricted cap

At every native pair \(m,n\ge2\), GD is admissible among all measurable normalized residual-only linear rules, including signed competitors without an assumed finite-risk bound.

For a general nonempty design, put \(d_i=n_i-1\) and \(D=\sum_i d_i\). On the legal degree cone
\[
D>2(k-1),\qquad (k-1)d_i<D\quad\text{for every }i,
\]
GD has the same residual-class admissibility. These inequalities are equivalent to existence of the legal positive critical prior used in the proof. The cone is hereditary under nonempty coordinate selection. It includes balanced designs of size at least three and \((2,m,\ldots,m)\) for \(m\ge3\).

On this cone, weak domination of GD forces equality of the residual coefficients almost everywhere; if the coefficients are continuous on the positive residual orthant, equality holds there pointwise. The coefficient-rigidity conclusion applies on the displayed cone.

For every native pair, and for every many-group design on this cone, a normalized residual rule with uniform GD-relative coefficient \(c\in[0,\infty]\) exists exactly when \(c\ge1\). GD attains \(c=1\). Thus residual rules cannot achieve a positive uniform percentage improvement, even at native designs where full-summary rules can.

[Supporting result](../GD/Module1712.lean), [Supporting result](../GD/Module1697.lean), [Supporting result](../GD/Module1701.lean), [Supporting result](../GD/Module1706.lean), [Supporting result](../GD/Module1713.lean).

**Evidence sources**

- [Lean source](../GD/Module1711.lean)
- [Lean source](../GD/Module1712.lean)
- [Lean source](../GD/Module1697.lean)
- [Lean source](../GD/Module1698.lean)
- [Lean source](../GD/Module1699.lean)
- [Lean source](../GD/Module1702.lean)
- [Lean source](../GD/Module1713.lean)
- [Lean source](../GD/Module1701.lean)
- [Lean source](../GD/Module1706.lean)
- [Lean source](../GD/Module1705.lean)
- [Lean source](../GD/Module1482.lean)
- [Lean source](../GD/Module1704.lean)
- [Lean source](../GD/Module1878.lean)

<a id="result-0001"></a>

### A class-preserving repair and a distinct residual-admissible family

For any measurable residual weights satisfying \(\sum_iw_i=1\), set
\[
w_i^+=\frac{\max(w_i,0)}{\sum_j\max(w_j,0)}.
\]
The denominator is positive. The repaired rule has finite risk everywhere and no larger risk than the original rule, even if an original risk is infinite. If a negative-weight event has positive probability at one physical parameter, the improvement is strict at every parameter. Arbitrary parameterwise cap feasibility, domination with a strict witness, and everywhere-strict cap domination can consequently be tested within simplex weights.

There are also residual-admissible rules different from GD. Choose two physical variance profiles with equal prior masses. Given the residuals, let \(q_i(T)\) be the posterior mean of the true mean variance \(v_i\), and choose weights proportional to \(q_i(T)^{-1}\). The resulting rule has interior-simplex weights and finite risk. The two selected physical risk inequalities already force equality of its weights almost everywhere among all normalized residual competitors. An explicit pair of profiles makes the weights nonconstant whenever \(k\ge2\). This is residual-class admissibility, not all-Borel admissibility or GD domination.

[Supporting result](../GD/Module0499.lean), [Supporting result](../GD/Module1494.lean).

**Evidence sources**

- [Lean source](../GD/Module0499.lean)
- [Lean source](../GD/Module1484.lean)
- [Lean source](../GD/Module1498.lean)
- [Lean source](../GD/Module1499.lean)
- [Lean source](../GD/Module1494.lean)
- [Lean source](../GD/Module1495.lean)
- [Lean source](../GD/Module1485.lean)

<a id="result-0007"></a>

### Clipping, automatic finite risk, and a quantitative coefficient obstruction

If a raw Borel rule is translation equivariant, clipping it to
\([\min_i\bar X_i,\max_i\bar X_i]\) weakly reduces every physical risk and produces finite risk without an original moment assumption. Positive probability of actual clipping gives strict improvement. For normalized linear weights depending on the full centered within-group residual array, a negative-weight event at one parameter yields an everywhere-strict clipped improvement. The clipped rule need not remain residual-linear. A translation-equivariant unrestricted terminal rule is therefore finite-risk and lies in the observed mean range almost surely.

A separate obstruction concerns any finite-risk Borel rule that has an almost-sure convex barycentric representation. If one group coefficient is always at most a fixed \(c<1\), its risk along the designated collapse ray has a positive floor \(b(1-c)^2\), where \(b>0\) is the Gaussian mass of the specified raw box. It must violate the GD cap somewhere. A representation is a hypothesis here; the theorem neither constructs it for an arbitrary rule nor requires a measurable selection of representing weights.

[Supporting result](../GD/Module1496.lean), [Supporting result](../GD/Module0712.lean).

**Evidence sources**

- [Lean source](../GD/Module1496.lean)
- [Lean source](../GD/Module1497.lean)
- [Lean source](../GD/Module1452.lean)
- [Lean source](../GD/Module1512.lean)
- [Lean source](../GD/Module1730.lean)
- [Lean source](../GD/Module0712.lean)

<a id="result-0028"></a>

### Strict seeds and their tunable correction rays

Every ordinary native pair has a finite-risk Borel positive-affine rule, built from a finite rational-tent correction, that strictly improves GD at every physical parameter. Every ordinary \(k\ge3\) design has an analogous full-summary strict improvement with simultaneous design-relabel covariance.

For the permutation-capacity-normalized many-group correction \(h\), put \(d_\alpha=d_0+\alpha h\). Its literal risk satisfies
\[
R_\theta(d_\alpha)-R_\theta(d_0)
=2\alpha C_\theta+\alpha^2B_\theta,
\qquad C_\theta<0,\quad 0\le B_\theta\le-C_\theta.
\]
Consequently the difference is at most \(\alpha(2-\alpha)C_\theta<0\) for \(0<\alpha<2\). Every real amplitude preserves the stated affine and relabel covariance. The factor \(\alpha(2-\alpha)\) is maximized uniquely at \(1\); this optimizes the certificate, not every individual risk. Separately, the selected-triangle reciprocal-capacity seed strictly improves both GD and its earlier safe-step seed. That capacity is mathematically specified, and no executable capacity evaluator or relabel covariance is asserted for this separate seed.

For each native emitted rational-tent ray, write \(R_\theta(d_a)=R_\theta(d_0)+2aC_\theta+a^2B_\theta\), with \(B_\theta>0\). Its finite Pareto boundary is
\[
a_* =\inf_\theta\frac{-C_\theta}{B_\theta}\ge\frac54.
\]
The rule \(d_{a_*}\) strictly improves every lower **real** amplitude at every parameter; every higher amplitude is worse at some parameter. The explicit step \(5/4\) already strictly improves every original step \(0\le a\le1\). Against the unit step its gain is at least \(G_\theta/16\), with the positive physical-ray certificate \(G_\theta\) from the construction. This is a frontier on one ray, not terminality against off-ray rules.

[Supporting result](../GD/Module0911.lean), [Supporting result](../GD/Module0750.lean), [Supporting result](../GD/Module0751.lean), [Supporting result](../GD/Module0745.lean), [Supporting result](../GD/Module0037.lean), [Supporting result](../GD/Module0972.lean).

**Evidence sources**

- [Lean source](../GD/Module0911.lean)
- [Lean source](../GD/Module0750.lean)
- [Lean source](../GD/Module0751.lean)
- [Lean source](../GD/Module0745.lean)
- [Lean source](../GD/Module0037.lean)
- [Lean source](../GD/Module0991.lean)
- [Lean source](../GD/Module1134.lean)
- [Lean source](../GD/Module0972.lean)
- [Lean source](../GD/Module1120.lean)

<a id="result-0026"></a>

### Retained explicit examples and finite-dimensional construction limits

Three more specialized construction results supply concrete examples and checks on overly narrow search spaces.

1. In the reduced two-shape Gamma experiment, **every fixed** real shape pair \(\alpha,\beta>0\) admits a strict trace profile formed from at most eight normalized product tents and one positive step, valid on the whole nuisance-fraction interval. The coefficient, support widths, resolution and margin may depend on the shapes. A six-jet identity removes the former diagonal pole, and shape exchange gives exact antisymmetry. The balanced four-channel system has rank three while adjoining the constant target gives rank four. The real-power differentiation and tent-integral assembly have paper-proof authority; their algebraic compilers have separately scoped checks. The shape parameters describe the reduced Gamma experiment; the construction is selected separately for each fixed shape pair.
2. At native \((2,2)\), the explicit historical eight-tent rule of half-width \(\eta=10^{-5}\), with step \(a=1/250\), has risk improvement exceeding
\[
\frac{351\eta^2}{500000\pi}
\frac{\sigma^4\tau^4}{(\sigma^2+\tau^2)^3}.
\]
Doubling that step does not dominate it. A specified disjoint two-bump correction nevertheless strictly improves it everywhere, and its anchored finite-packet Bayes deficiency has the positive floor recorded in the source. These constructions provide explicit nonterminal seeds for comparison with the terminal-completion results.
3. At the balanced \((11,11)\) design, the double scale-Haar posterior-mean rule strictly improves plug-in GD for every positive variance ratio. Yet no nonzero correction in the displayed ten-dimensional degree-six polynomial class weakly improves that posterior rule: a positive ten-atom charge balance cancels the linear risk terms and leaves a positive quadratic form. The obstruction holds for the displayed ten-dimensional polynomial class.

The second and third examples combine complete written analytic arguments with exact computational certificates. The prerequisite and proof-family tables identify the written, computational and Lean contributions to those proofs.

[Supporting result](../proofs/Proof0001.md), [Supporting result](../proofs/Proof0002.md), [Supporting result](../proofs/Proof0003.md), [Supporting result](../proofs/Proof0003.md).

**Evidence sources**

- [Supporting argument](../proofs/Proof0001.md)
- [Lean source](../GD/Module0190.lean)
- [Supporting argument](../proofs/Proof0002.md)
- [Supporting argument](../proofs/Proof0003.md)
- [Supporting argument](../certificates/Certificate0003/Data0008.json)
- [Supporting argument](../certificates/Certificate0003/Data0009.json)
- [Lean source](../GD/Module0179.lean)
- [Lean source](../GD/Module0181.lean)
- [Lean source](../GD/Module0186.lean)
- [Lean source](../GD/Module0187.lean)
- [Lean source](../GD/Module0189.lean)
- [Lean source](../GD/Module0188.lean)
- [Supporting argument](../certificates/Certificate0003/Data0006.json)
- [Lean source](../GD/Module0240.lean)
- [Lean source](../GD/Module0185.lean)
- [Lean source](../GD/Module0184.lean)
- [Lean source](../GD/Module0180.lean)
- [Lean source](../GD/Module0182.lean)

<a id="result-0029"></a>

### Strict terminal completion and the symmetry that can be retained

Every ordinary design with \(k\ge2\) admits a finite-risk Borel rule that strictly improves GD at every parameter and is terminal against all raw Borel competitors. Native and many-group canonical constructions obtain such a rule from a complete lower-risk cone.

For ordinary \(k\ge3\), a stronger all-seed statement holds: a finite-risk raw Borel seed is nonterminal if and only if it has a finite-risk terminal successor with strictly smaller risk at every parameter. A successor inherits a GD or oracle cap when the seed has that cap; arbitrary seeds need not be GD dominators.

No ordinary design admits one rule that is simultaneously positive-affine, an everywhere-strict GD improvement, and terminal against all Borel competitors. For \(k\ge3\), a strict terminal GD improvement has no affine Borel representative even modulo any physical law. The native selected relative optimum has the corresponding common-null nonaffinity and positive two-generator defect.

Finite permutation symmetry is still attainable with a separately selected witness. At balanced native pairs the representative is exactly block-swap invariant. For many groups, one chosen family is invariant under all size-preserving permutations and natural under simultaneous relabeling of data and design, including exceptional raw datasets. These finite-symmetry witnesses are not identified with every separately selected minimax completion.

[Supporting result](../GD/Module0912.lean), [Supporting result](../GD/Module0763.lean), [Supporting result](../GD/Module1748.lean), [Supporting result](../GD/Module1447.lean), [Supporting result](../GD/Module1410.lean), [Supporting result](../GD/Module1733.lean), [Supporting result](../GD/Module1749.lean).

**Evidence sources**

- [Lean source](../GD/Module0912.lean)
- [Lean source](../GD/Module0763.lean)
- [Lean source](../GD/Module1276.lean)
- [Lean source](../GD/Module1748.lean)
- [Lean source](../GD/Module1447.lean)
- [Lean source](../GD/Module1410.lean)
- [Lean source](../GD/Module1733.lean)
- [Lean source](../GD/Module1460.lean)
- [Lean source](../GD/Module1738.lean)
- [Lean source](../GD/Module1749.lean)
- [Lean source](../GD/Module1751.lean)

<a id="result-0010"></a>

### Conditional partial-symmetry characterization

For an ordinary \(k\ge3\) design, **if** a translation-covariant strict terminal GD improvement exists, its statistical log-dilation stabilizer is either \(\{0\}\) or \(a\mathbb Z\) for some \(a>0\). A dilation-covariant strict terminal improvement has trivial translation stabilizer.

Translation-only existence is equivalent to existence of an already strict terminal Borel GD improvement satisfying two reference-law almost-everywhere shift identities at generators with irrational ratio. Dilation-only existence has the corresponding equivalence using two incommensurable log-scale identities. The resulting class has an everywhere-covariant representative with the same physical risks and terminality. These characterization theorems take the existence of the specified strict terminal improvement as a hypothesis.

[Supporting result](../GD/Module1657.lean), [Supporting result](../GD/Module1661.lean), [Supporting result](../GD/Module1753.lean).

**Evidence sources**

- [Lean source](../GD/Module1657.lean)
- [Lean source](../GD/Module1658.lean)
- [Lean source](../GD/Module1659.lean)
- [Lean source](../GD/Module1660.lean)
- [Lean source](../GD/Module1661.lean)
- [Lean source](../GD/Module1750.lean)
- [Lean source](../GD/Module1753.lean)
- [Lean source](../GD/Module1752.lean)

<a id="result-0022"></a>

### One strict terminal rule attains the relative optimum, with singular limiting priors

At every ordinary design with \(k\ge2\), one finite-risk Borel strict terminal GD improvement \(d_B\) attains \(B=B_{\mathbf n}\) and hence \(\Gamma_{\mathbf n}\). Put \(r(\theta)=R_\theta(d_B)/R_\theta(d_0)\). Then
\[
r(\theta)<B\quad\text{for every }\theta,\qquad
\sup_\theta r(\theta)=B,\qquad
\int r\,d\nu<B
\]
for every countably additive probability prior \(\nu\). The two-sample and many-group results supply the following stronger bundle for the same selected rule.

There is a sequence of Dirac probability priors whose averages tend to \(B\). For **every** prior sequence \(\Pi_j\) with \(\int r\,d\Pi_j\to B\), every fixed probability reference \(\nu\), and every \(\varepsilon>0\), there is one measurable event \(A\), independent of \(j\), such that
\[
\nu(A)<\varepsilon,\qquad \Pi_j(A)\longrightarrow1.
\]
No such sequence has a setwise probability limit. On an appropriate fixed event its probability difference from each fixed reference eventually exceeds \(1-\varepsilon\). Also, \(\Pi_j\{B-r\ge\delta\}\to0\) for every \(\delta>0\). The event may depend on \(\nu\) and \(\varepsilon\).

These averages concern the one selected risk profile. The native proper-prior exclusion is included in this stronger bundle.

[Supporting result](../GD/Module1865.lean), [Supporting result](../GD/Module1735.lean), [Supporting result](../GD/Module1876.lean), [Supporting result](../GD/Module0441.lean), [Supporting result](../GD/Module1875.lean).

**Evidence sources**

- [Lean source](../GD/Module1865.lean)
- [Lean source](../GD/Module1879.lean)
- [Lean source](../GD/Module1735.lean)
- [Lean source](../GD/Module1734.lean)
- [Lean source](../GD/Module1876.lean)
- [Lean source](../GD/Module0441.lean)
- [Lean source](../GD/Module1736.lean)
- [Lean source](../GD/Module1875.lean)
- [Lean source](../GD/Module1877.lean)

<a id="result-0008"></a>

### Complete native gain classification and the surviving many-group bounds

In both finite Borel and finite affine classes,
\[
\Gamma_{m,n}>0\quad\Longleftrightarrow\quad
(m,n)\in\{(2,3),(3,2),(3,3)\}.
\]
At every other ordinary native pair the optimum is zero, despite the everywhere-strict improvements already constructed.

For \(k\ge3\), all but one sample sizes at least four force \(\Gamma_{\mathbf n}=0\). More generally, retain a pair \(i,j\) and suppose every deleted size is at least four. Every finite proportional GD cap transfers to the actual native experiment, without assuming a finite oracle cap or any boundary limit for the input rule. Hence
\[
B_{n_i,n_j}\le B_{\mathbf n},\qquad
\Gamma_{\mathbf n}\le\Gamma_{n_i,n_j}.
\]
In particular two size-two groups with all other sizes at least four have zero gain.

There is additional quantitative information when all groups complementary to a distinguished group \(h\) have size at least three. Let \(c\) count the complementary size-three groups. Along the physical ray \(v_h=e\downarrow0\), \(v_i=1\) otherwise,
\[
R_\theta(d_0)/e\to1+c,\qquad
\tau_\theta/R_\theta(d_0)\to\frac1{1+c},\qquad
\Gamma_{\mathbf n}\le\frac{c}{1+c}\quad(k\ge3).
\]
If all sizes are at least three, \(V_{\mathbf n}\le kB_{\mathbf n}\) and \(\Gamma_{\mathbf n}<1-1/k\). Applicable count and deletion bounds should be intersected; none alone classifies every many-group design.

[Supporting result](../GD/Module1896.lean), [Supporting result](../GD/Module1281.lean), [Supporting result](../GD/Module1880.lean), [Supporting result](../GD/Module1915.lean), [Supporting result](../GD/Module1881.lean), [Supporting result](../GD/Module1664.lean), [Supporting result](../GD/Module1717.lean).

**Evidence sources**

- [Lean source](../GD/Module0434.lean)
- [Lean source](../GD/Module0436.lean)
- [Lean source](../GD/Module1872.lean)
- [Lean source](../GD/Module1337.lean)
- [Lean source](../GD/Module1873.lean)
- [Lean source](../GD/Module1874.lean)
- [Lean source](../GD/Module1896.lean)
- [Lean source](../GD/Module1871.lean)
- [Lean source](../GD/Module1281.lean)
- [Lean source](../GD/Module1418.lean)
- [Lean source](../GD/Module1419.lean)
- [Lean source](../GD/Module1880.lean)
- [Lean source](../GD/Module1915.lean)
- [Lean source](../GD/Module1881.lean)
- [Lean source](../GD/Module1664.lean)
- [Lean source](../GD/Module1672.lean)
- [Lean source](../GD/Module1759.lean)
- [Lean source](../GD/Module1674.lean)
- [Lean source](../GD/Module1714.lean)
- [Lean source](../GD/Module1717.lean)

<a id="result-0031"></a>

### The complete oracle-finiteness boundary and its residual restriction

For every ordinary \(k\ge2\) design,
\[
V_{\mathbf n}<\infty
\quad\Longleftrightarrow\quad
(n_i-1)(n_j-1)\ge4\quad\text{for every }i\ne j.
\]
Equivalently, either all sizes are at least three, or exactly one size is two and every companion is at least five. Infinite-value designs still possess a finite-at-each-parameter strict terminal GD improvement attaining that infinite objective; this gives no finite uniform oracle guarantee.

Within normalized residual-only linear rules, finite worst oracle risk is possible exactly when **every** size is at least three. Thus on the legal residual-admissibility cone with one size two and companions at least five, residual GD admissibility coexists with infinite oracle risk for every residual rule and finite unrestricted oracle minimax. The family \((2,m,\ldots,m)\), \(m\ge5\), is an explicit instance. The residual-admissibility statement uses the displayed legal cone.

[Supporting result](../GD/Module1543.lean), [Supporting result](../GD/Module1693.lean), [Supporting result](../GD/Module1702.lean).

**Evidence sources**

- [Lean source](../GD/Module1462.lean)
- [Lean source](../GD/Module1543.lean)
- [Lean source](../GD/Module1693.lean)
- [Lean source](../GD/Module1694.lean)
- [Lean source](../GD/Module1695.lean)
- [Lean source](../GD/Module1702.lean)

<a id="result-0014"></a>

### Explicit finite-cap pair selectors, including the critical designs

For a native pair put \(a=(m-1)/2\), \(b=(n-1)/2\). If \(ab>1\), choose \(u,v>0\) with \(u/v<a\) and \(v/u<b\). For means \(x,y\), estimated mean variances \(s=S_X^2/m,t=S_Y^2/n\), and \(D=x-y\), choose
\[
d_{u,v}=\begin{cases}
x,&[s/(s+D^2)]^u\le[t/(t+D^2)]^v,\\
y,&\text{otherwise}.
\end{cases}
\]
To define the finite bound, let \(Z_1,Z_2\) be independent standard normals, \(Y_b\sim\operatorname{Gamma}(b,\text{rate }b)\), and put
\[
G(r)=\mathbb E\!\left[(2(Z_1^2+Z_2^2))^r\right],\quad
C(b,r)=2+2\cdot2^r\{1+G(r)\mathbb E Y_b^{-r}\},
\quad C_{a,b,u,v}=\max\{C(b,v/u),C(a,u/v)\}.
\]
With the specified Borel repair, this rule has
\(R_\theta(d_{u,v})\le2C_{a,b,u,v}\tau_\theta\). Its oracle-normalized excess tends to zero as \(p=v_Y/(v_X+v_Y)\to0\). This is the stated one-sided endpoint, with no GD dominance, admissibility or minimaxity assertion.

At the separate critical boundary \(ab=1\), the same mean-gap recipe with powers \((u,v)=(a,1)\) has
\[
R_\theta(d_{a,1})\le
\operatorname{criticalPairCap}(a,b,a,1)\min(v_X,v_Y).
\]
Here the finite source constant is
\[
\operatorname{criticalPairCap}(a,b,u,v)
=\max\{C_*(b,u/v),C_*(a,v/u)\},\qquad
C_*(b,r)=4+2\frac{b^b}{b\Gamma(b)}(1-2^{-r})^{-b}G(b).
\]
It supplies explicit finite-cap rules at \((2,5),(3,3),(5,2)\). The standardized \((a,b)=(1/2,2)\) construction also certifies powers \((1,2)\). No boundary-efficiency claim is added at \(ab=1\). The physical construction and complete finiteness classification have their distinct supporting sources.

[Supporting result](../GD/Module1546.lean), [Supporting result](../GD/Module1427.lean), [Supporting result](../GD/Module1540.lean).

**Evidence sources**

- [Lean source](../GD/Module1546.lean)
- [Lean source](../GD/Module0440.lean)
- [Lean source](../GD/Module1427.lean)
- [Lean source](../GD/Module1430.lean)
- [Lean source](../GD/Module1532.lean)
- [Lean source](../GD/Module1537.lean)
- [Lean source](../GD/Module1540.lean)
- [Lean source](../GD/Module1541.lean)
- [Lean source](../GD/Module1539.lean)
- [Lean source](../GD/Module1538.lean)

<a id="result-0030"></a>

### The actual symmetric pair aggregator and its oracle bound

Given symmetric Borel pair rules \(d_{ij}=d_{ji}\), lifted to the full data, define
\[
d=\max_i\min_{j\ne i}d_{ij}.
\]
For every incident star \(i\), this value lies between \(\min_{j\ne i}d_{ij}\) and \(\max_{j\ne i}d_{ij}\), so
\[
(d-\mu)^2\le\sum_{j\ne i}(d_{ij}-\mu)^2.
\]
No independence between pair-rule errors is needed. If each pair rule has risk at most \(C\) times its pair oracle variance, the assembled rule has risk at most \(\binom{k}{2}C\tau_\theta\). Consequently
\[
\max_{i<j}V_{n_i,n_j}\le V_{\mathbf n}
\le\binom{k}{2}\max_{i<j}V_{n_i,n_j}.
\]
The estimator uses only finite minima and maxima of available pair rules; unknown precision shares occur in the proof. The assembly theorem supplies the displayed oracle upper bound for the pair aggregator.

[Supporting result](../GD/Module1804.lean).

**Evidence sources**

- [Lean source](../GD/Module1804.lean)
- [Lean source](../GD/Module1805.lean)

<a id="result-0013"></a>

### Exact unrestricted value at (3,3), attained by a displayed rule

At the native \((3,3)\) design,
\[
V_{3,3}=1+\frac\pi4,
\qquad
d_*=\frac{(S_Y^2)^2\bar X+(S_X^2)^2\bar Y}
{(S_X^2)^2+(S_Y^2)^2}.
\]
The value agrees over all Borel, finite-risk Borel and affine finite-risk competitors. The displayed affine residual-share rule has oracle-normalized risk strictly below this value at every physical parameter and approaches the supremum at the variance boundaries. It is ordinarily inadmissible; minimaxity alone does not confer admissibility.

In reduced coordinates, finite rational logarithmic packets \(\widehat P_N\), \(N\ge16\), give Bayes lower bounds \(\mathfrak B_N\) with
\[
0<\frac\pi4-\mathfrak B_N<\frac{14}{N},\qquad
\limsup_{N\to\infty}N(\pi/4-\mathfrak B_N)\le\pi/2+2.
\]
No finite interior packet attains the dual supremum. If \(M_j=\sum_i p_i t_i^jK_{t_i}\), its posterior coefficient is \(g_P=M_1/M_0\), and exact square completion gives
\[
\sum_i p_iL_{t_i}(g)
=\int\left(M_2-\frac{M_1^2}{M_0}\right)
 +\int M_0(g-g_P)^2.
\]
For the corresponding packet measures \(\mu_N\), every minimax coefficient satisfies \(\|g-g_{P_N}\|_{L^2(\mu_N)}^2<14/N\), and any two satisfy \(\|g-h\|_{L^2(\mu_N)}^2<56/N\). The estimates use the changing packet measures \(\mu_N\), which lose mass on fixed interior compact sets.

Every containing ordinary design with two size-three groups inherits \(V\ge1+\pi/4\). At \((3,3)\), no Borel rule has risk at most both individual sample-mean variances at every parameter, and
\(\Gamma_{3,3}\le1/2-\pi/8\). Within the smaller residual-share profile class, GD domination forces worst oracle risk at least \(2\). That class-specific floor is not transferred to general contrast-dependent coefficients.

The packet and exact physical endpoint are established by the audited **written proof**. Lean verifies the conditional window-bound algebra and the endpoint, mesh and mass support modules under their stated hypotheses. The written proof supplies the statistical integral bounds used in the packet argument.

[Supporting result](../proofs/Proof0004.md), [Supporting result](../proofs/Proof0004.md), [Supporting result](../proofs/Proof0004.md), [Supporting result](../GD/Module0337.lean).

**Evidence sources**

- [Supporting argument](../proofs/Proof0004.md)
- [Lean source](../GD/Module0337.lean)
- [Lean source](../GD/Module0558.lean)
- [Lean source](../GD/Module0560.lean)
- [Lean source](../GD/Module1898.lean)
- [Lean source](../GD/Module1902.lean)
- [Lean source](../GD/Module1903.lean)
- [Lean source](../GD/Module1904.lean)

<a id="result-0019"></a>

### GD domination and unrestricted oracle minimaxity are incompatible exactly at finite native values

At every ordinary native pair,
\[
V^{\mathrm{GD}}_{m,n}>V_{m,n}
\quad\Longleftrightarrow\quad V_{m,n}<\infty.
\]
A finite-risk strict terminal GD improvement attains unrestricted oracle minimax exactly on the infinite-value native designs: one size is two and the other is at most four. At \((3,3)\), the stronger quantitative conclusion is
\[
V^{\mathrm{GD}}_{3,3}>1+\pi/4+10^{-3}.
\]
Every raw weak GD dominator has worst oracle risk strictly above this threshold. The incompatibility certificate uses the full two-coordinate reduced problem, not a residual-profile restriction.

For ordinary \(k\ge3\), the constrained value \(V^{\mathrm{GD}}\), finite or infinite, is attained by a separately selected strict terminal GD improvement. Equality \(V^{\mathrm{GD}}=V\) is exactly the remaining compatibility condition. Every many-group design containing a \((2,5)\) pair has \(V^{\mathrm{GD}}=\infty\), with no restriction on deleted sizes. If all companions of the size-two group are at least five, \(V<\infty\). Thus \((2,5,5)\), and its heterogeneous extensions, require sacrificing GD domination to obtain finite oracle control. General constrained pair transfer separately requires deleted sizes at least four.

[Supporting result](../GD/Module1908.lean), [Supporting result](../GD/Module1737.lean), [Supporting result](../GD/Module1858.lean), [Supporting result](../GD/Module1835.lean).

**Evidence sources**

- [Lean source](../GD/Module1907.lean)
- [Lean source](../GD/Module1908.lean)
- [Lean source](../GD/Module1909.lean)
- [Lean source](../GD/Module1737.lean)
- [Lean source](../GD/Module1857.lean)
- [Lean source](../GD/Module1858.lean)
- [Lean source](../GD/Module1715.lean)
- [Lean source](../GD/Module1835.lean)
- [Lean source](../GD/Module1856.lean)

<a id="result-0004"></a>

### Affine admissibility and minimaxity have different attaining rules

For a native pair, an affine Borel rule ordinarily admissible against all Borel competitors has worst oracle ratio strictly above \(2\); if \(\min(m,n)\le3\), that ratio is infinite. Hence no finite-value native design admits a single affine, ordinarily admissible, oracle-minimax rule. Such an affine admissible rule also cannot lie below both individual sample-mean risks. There is no GD-domination premise.

For every ordinary \(k\ge3\), every affine ordinarily admissible rule has infinite worst oracle ratio. Nevertheless there are a finite-physical-risk affine nonadmissible minimax rule \(d_A\) and a finite-physical-risk nonaffine admissible minimax rule \(d_T\), with
\[
R_\theta(d_T)<R_\theta(d_A)\quad\forall\theta,\qquad
\sup_\theta R_\theta(d_T)/\tau_\theta
=\sup_\theta R_\theta(d_A)/\tau_\theta=V_{\mathbf n}.
\]
This includes infinite values. This ordered pair is not in general a pair of GD dominators, and the selected \(d_T\) is not asserted to be the relative or constrained optimizer.

[Supporting result](../GD/Module1884.lean), [Supporting result](../GD/Module1733.lean).

**Evidence sources**

- [Lean source](../GD/Module1322.lean)
- [Lean source](../GD/Module1882.lean)
- [Lean source](../GD/Module1507.lean)
- [Lean source](../GD/Module1409.lean)
- [Lean source](../GD/Module1883.lean)
- [Lean source](../GD/Module1884.lean)
- [Lean source](../GD/Module1862.lean)
- [Lean source](../GD/Module1417.lean)
- [Lean source](../GD/Module1863.lean)
- [Lean source](../GD/Module1508.lean)
- [Lean source](../GD/Module1509.lean)
- [Lean source](../GD/Module1506.lean)
- [Lean source](../GD/Module1864.lean)
- [Lean source](../GD/Module1733.lean)
- [Lean source](../GD/Module1460.lean)
- [Lean source](../GD/Module1738.lean)

<a id="result-0027"></a>

### Sharp GD envelopes, exact small-sample risks, and nonuniform integrability

When every \(n_i\ge3\), the GD worst oracle ratio is at most \(k\). This constant is the sharp envelope over such designs. More strongly, if all groups complementary to one retained group have size three and the retained group has any size at least three, the fixed-design worst ratio is exactly \(k\). Increasing only that retained size does not reduce it.

For \(k\ge3\), GD has finite worst oracle ratio exactly when every sample size is at least three. A collapse ray is oracle-saturating exactly when every complementary size is at least four; the retained size can be any size at least two. A complementary size-two group gives divergence instead.

When every \(n_i=2\), the literal risk has the closed form
\[
R_\theta(d_0)=\frac14\left[
\frac{\sum_i\sigma_i}{\sum_i\sigma_i^{-1}}
+\frac{k}{(\sum_i\sigma_i^{-1})^2}\right].
\]
The squared normalized precision moments are \((p_i^2+p_i)/2\), for normalized reciprocal-standard-deviation shares \(p_i\). In the three-group standard-deviation family \((1,1,r)\), risks diverge as \(r\to\infty\), although under the fixed Gaussian coupling the estimators converge almost surely to the two-group GD rule of risk \(3/8\). Almost-sure deletion convergence therefore need not justify risk convergence. This last physical calculation retains paper-proof authority.

[Supporting result](../GD/Module1676.lean), [Supporting result](../GD/Module1720.lean), [Supporting result](../GD/Module1664.lean), [Supporting result](../proofs/Proof0005.md).

**Evidence sources**

- [Lean source](../GD/Module1676.lean)
- [Lean source](../GD/Module1677.lean)
- [Lean source](../GD/Module1720.lean)
- [Lean source](../GD/Module1721.lean)
- [Lean source](../GD/Module1664.lean)
- [Lean source](../GD/Module1672.lean)
- [Lean source](../GD/Module1759.lean)
- [Lean source](../GD/Module1674.lean)
- [Lean source](../GD/Module1714.lean)
- [Supporting argument](../proofs/Proof0005.md)

<a id="result-0005"></a>

### All native boundary rates, with exact leading constants

For \(m,n\ge2\), put \(a=(m-1)/2\), \(b=(n-1)/2\), \(\Sigma=v_X+v_Y\), \(p=v_Y/\Sigma\), and \(E=R_\theta(d_0)-\tau_\theta\). As \(p\downarrow0\),
\[
\frac E\Sigma\sim
\begin{cases}
\displaystyle (a/b)^a\frac{\Gamma(a+b)\Gamma(2-a)}{\Gamma(b)}p^a,&0<a<2,\\[3pt]
\displaystyle \frac{4(b+1)}b\,p^2\log(1/p),&a=2,\\[3pt]
\displaystyle \frac{a^2+ab+2b}{b(a-1)(a-2)}p^2,&a>2.
\end{cases}
\]
Thus the left boundary has powers \(p^{1/2},p,p^{3/2}\) at \(m=2,3,4\), the logarithmic transition at \(m=5\), and a quadratic law at \(m\ge6\). The right boundary exchanges \(a,b\) and \(p,1-p\). These laws hold along arbitrary positive physical-scale sequences and arbitrary common-location sequences: normalization uses the exact termwise \(\Sigma\), which need not converge.

As a full-curve example, at \(m=n=2\), standard deviations \((1,\rho)\),
\[
R_\theta(d_0)=\frac{\rho(\rho^2+4\rho+1)}{4(\rho+1)^2}.
\]
Here \(\rho\) is a standard-deviation ratio, not \(p\). None of these baseline formulas gives a new corrected-estimator or minimax endpoint.

[Supporting result](../GD/Module0901.lean), [Supporting result](../GD/Module0902.lean), [Supporting result](../GD/Module0925.lean).

**Evidence sources**

- [Lean source](../GD/Module0901.lean)
- [Lean source](../GD/Module0902.lean)
- [Lean source](../GD/Module0925.lean)
- [Lean source](../GD/Module1177.lean)

<a id="result-0015"></a>

### Explicit near-oracle strict terminal caps and a positive adaptation cost

If every \(n_i\ge4\),
\[
\sup_\theta\frac{R_\theta(d_0)}{\tau_\theta}
\le1+\frac{k-1}{2}\sum_i\frac1{n_i-3}.
\]
For \(k\ge3\), one finite-risk strict terminal GD improvement preserves this exact bound. If every \(n_i\ge N\ge4\), the bound is at most \(1+k(k-1)/(2(N-3))\). In particular, for every \(\varepsilon>0\),
\[
n_i\ge4+\left\lceil\frac{k(k-1)}{2\varepsilon}\right\rceil
\quad\forall i
\quad\Longrightarrow\quad
\sup_\theta R_\theta(d)/\tau_\theta<1+\varepsilon.
\]
For three groups of size at least \(34\), it is at most \(34/31<1.10\). The same selected rule has zero uniform GD-relative gain, by the all-but-one-large theorem. Near-oracle performance and a positive uniform percentage improvement over GD are different requirements.

There remains a positive finite-design adaptation cost. For each native pair let \(\omega\) be the overlap integral of the literal reduced probability densities at variance shares \(1/4\) and \(3/4\). Then \(0<\omega\le1\),
\[
V_{m,n}\ge1+\omega/3>1,
\]
and containing designs inherit this bound. The source supplies an explicit positive likelihood-floor formula below \(\omega\), and finite physical posterior packets witness a ratio above \(1+\omega/6\). These are lower bounds, not exact values.

For interpretation, a finite-risk translation-equivariant rule meeting one variance-profile oracle cap must equal that profile's oracle almost surely. Two profile oracles agree under a positive Gaussian law exactly when their variance vectors are proportional. The restriction to translation equivariance is essential to this two-profile argument.

[Supporting result](../GD/Module1550.lean), [Supporting result](../GD/Module1802.lean), [Supporting result](../GD/Module1281.lean), [Supporting result](../GD/Module1341.lean).

**Evidence sources**

- [Lean source](../GD/Module1493.lean)
- [Lean source](../GD/Module1550.lean)
- [Lean source](../GD/Module1802.lean)
- [Lean source](../GD/Module1803.lean)
- [Lean source](../GD/Module1801.lean)
- [Lean source](../GD/Module1800.lean)
- [Lean source](../GD/Module1799.lean)
- [Lean source](../GD/Module1281.lean)
- [Lean source](../GD/Module1418.lean)
- [Lean source](../GD/Module1419.lean)
- [Lean source](../GD/Module1341.lean)
- [Lean source](../GD/Module1435.lean)
- [Lean source](../GD/Module1436.lean)

<a id="result-0023"></a>

### Positive affine-character gauges and separately selected cap-preserving endpoints

For ordinary \(k\ge3\), let \(\gamma(\theta)>0\) obey
\(\gamma(a\theta+b)=a^2\gamma(\theta)\), with positive scales transformed in the usual way. The minimax values of \(R_\theta/\gamma(\theta)\) agree over all Borel, finite-risk Borel and affine finite-risk rules; an affine finite-physical-risk attainer exists, even if the value is infinite. The compact-cap and finite-posterior duality statements apply to this gauge.

If \(C>0\) and the joint cap
\[
R_\theta(d)\le\min\{R_\theta(d_0),C\gamma(\theta)\}\quad\forall\theta
\]
is feasible, it contains a finite-risk strict terminal GD improvement preserving the same cap. This strict terminal rule is selected separately from the affine gauge minimizer. The result supplies neither automatic finite value nor a common optimizer for distinct gauges.

[Supporting result](../GD/Module0805.lean), [Supporting result](../GD/Module0808.lean), [Supporting result](../GD/Module1737.lean).

**Evidence sources**

- [Lean source](../GD/Module0805.lean)
- [Lean source](../GD/Module0805.lean)
- [Lean source](../GD/Module0806.lean)
- [Lean source](../GD/Module0806.lean)
- [Lean source](../GD/Module0811.lean)
- [Lean source](../GD/Module0811.lean)
- [Lean source](../GD/Module0808.lean)
- [Lean source](../GD/Module0808.lean)
- [Lean source](../GD/Module0807.lean)
- [Lean source](../GD/Module0807.lean)
- [Lean source](../GD/Module0812.lean)
- [Lean source](../GD/Module0812.lean)
- [Lean source](../GD/Module1737.lean)

<a id="result-0016"></a>

### Finite physical posterior duality and robust infeasibility certificates

Fix the Gaussian reference parameter \(\theta_0=(0,1,\ldots,1)\), its law \(P_0\), and a finite parameter packet \((\theta_i,w_i)\), \(w_i\ge0\). Write \(\ell_i=dP_{\theta_i}/dP_0\), \(\mu_i=\mu(\theta_i)\), and
\[
M_0=1+\sum_iw_i\ell_i,\quad M_1=\sum_iw_i\ell_i\mu_i,
\quad M_2=\sum_iw_i\ell_i\mu_i^2,\quad p_w=M_1/M_0.
\]
The unit reference atom is retained. For finite-risk \(d\), square completion gives
\[
\|d\|_{L^2(P_0)}^2+\sum_iw_iR_{\theta_i}(d)
=\mathcal B(w)+\int M_0(d-p_w)^2\,dP_0,
\qquad
\mathcal B(w)=\int(M_2-M_1^2/M_0)\,dP_0.
\]
The bounded finite-posterior rule \(p_w\) attains this inner minimum and has finite risk everywhere. With oracle budget \(\mathcal T(w)=\tau_{\theta_0}+\sum_iw_i\tau_{\theta_i}\), every ordinary \(k\ge2\) design satisfies
\[
V_{\mathbf n}=\sup_{\text{finite packets}}\frac{\mathcal B(w)}{\mathcal T(w)}.
\]
Every upper cut is equivalent to all packet inequalities; every strict lower cut has a finite violating packet. The many-group version replaces \(\tau\) by any positive affine-character gauge.

For native nonnegative finite risk budgets \(c_\theta\), infeasibility has a robust finite physical witness: some finite set \(F\) and \(\varepsilon>0\) satisfy
\[
\forall d\ \exists\theta\in F:\quad
R_\theta(d)>c_\theta+\varepsilon\tau_\theta.
\]
Equivalently, the unnormalized anchored packet gaps
\(\mathcal B(w)-c_{\theta_0}-\sum_iw_ic_{\theta_i}\)
are unbounded above. Feasibility is equivalent to every such gap being nonpositive, and also to their being bounded above. For the particular joint GD/oracle-minimax budget, feasibility strengthens to a uniformly negative gap bound; otherwise gaps are unbounded above. This special strict alternative is not asserted for arbitrary budgets. These reference-anchored gaps are different from the normalized native33 packets and do not restore their refuted uniform-gap assertion.

[Supporting result](../GD/Module1081.lean), [Supporting result](../GD/Module0808.lean), [Supporting result](../GD/Module1849.lean), [Supporting result](../GD/Module1853.lean).

**Evidence sources**

- [Lean source](../GD/Module1081.lean)
- [Lean source](../GD/Module1081.lean)
- [Lean source](../GD/Module0808.lean)
- [Lean source](../GD/Module0808.lean)
- [Lean source](../GD/Module0807.lean)
- [Lean source](../GD/Module0807.lean)
- [Lean source](../GD/Module0812.lean)
- [Lean source](../GD/Module0812.lean)
- [Lean source](../GD/Module1849.lean)
- [Lean source](../GD/Module1850.lean)
- [Lean source](../GD/Module1853.lean)

<a id="result-0003"></a>

### Admissible posterior examples, deficiency criteria, and distance bounds

The native finite physical posterior completion retaining a positive reference atom is pinned by finitely many physical risk inequalities. It is admissible against all Borel competitors and has no affine risk character. This provides concrete admissible examples, without asserting that they improve GD or minimize one of the global objectives.

For an everywhere-finite-risk reference-\(L^2\) decision \(s\), define its complete lower cone \(C(s)=\{d:R_\theta(d)\le R_\theta(s)\ \forall\theta\}\), its minimum-reference-norm projection \(P_s\), and reference gap \(\|s\|_0^2-\|P_s\|_0^2\). Native anchored finite physical Bayes deficiencies have infimum exactly this gap. The gap vanishes exactly at strong unbeatability in the stated common-reference \(L^2\) domain. In the finite many-normal experiment, admissibility on the entire finite-physical-risk reference-\(L^2\) domain is equivalent to arbitrarily small **actual** unit-reference-anchored Bayes deficiencies.

The quantitative form retains a positive reference coefficient \(\rho\). Under the source's convexity and integrability assumptions, if \(D\) is the anchored deficiency, \(p\) an objective minimizer and \(d\) a weak dominator of \(s\), then
\[
\rho\|s-p\|^2\le D,\qquad
\rho\|d-s\|^2\le4(D+\eta),
\]
where \(\eta\ge0\) is a certified optimization error. Dividing by \(\rho\), or drawing convergence conclusions, requires \(\rho>0\).

The two-group simplex posterior also has an exact one-dimensional interval-prior representation: every positive-residual posterior mean is the corresponding scalar mixture, its contrast energy has the factor \(1/2\), and equality of posterior coordinates is identifiable away from equal means. This gives an exact coordinate reduction of the two-group simplex posterior.

[Supporting result](../GD/Module1077.lean), [Supporting result](../GD/Module1556.lean), [Supporting result](../GD/Module0814.lean).

**Evidence sources**

- [Lean source](../GD/Module1077.lean)
- [Lean source](../GD/Module1556.lean)
- [Lean source](../GD/Module0572.lean)
- [Lean source](../GD/Module1554.lean)
- [Lean source](../GD/Module1555.lean)
- [Lean source](../GD/Module0814.lean)

<a id="result-0017"></a>

### Finite-stage nonattainment and a convergent posterior sequence for one selected completion

For a native affine-finite seed, every finite positive physical posterior candidate admits a strict one-atom increase of its dual reserve. Every finite reserve is strictly below the complete terminal-projection energy, and every finite active-posterior KKT residual for a legal complete-cone comparison is positive. There is no uniform positive residual bound.

More precisely, the infimum of the seed's unnormalized anchored Bayes deficiencies equals its reference projection gap. For an affine seed strictly improving GD, that gap is positive, giving one positive floor uniform over packet sizes, parameters and nonnegative weights. This prevents an anchored Bayes-null row from terminalizing that **seed itself**; it does not prevent approximation of its separate terminal completion.

For the selected strict-improvement seed \(s\) and its canonical complete-lower-cone projection \(P\), finite physical packets \(\pi_j\) and nonnegative weights can be chosen so their dual reserves \(r_j\) are nondecreasing and
\[
0\le\|P\|_0^2-r_j\downarrow0,\qquad
\|p_{\pi_j}-P\|_{L^2(P_0)}\longrightarrow0.
\]
The same \(P\) has a Borel representative strictly improving GD everywhere and terminal against every measurable raw competitor modulo common physical almost-everywhere equality. No effective clock, rate, nested support, stagewise monotonicity of physical risks, or convergence under every physical law is asserted. This named completion is not identified with the separately chosen relative or constrained minimizer.

[Supporting result](../GD/Module1162.lean), [Supporting result](../GD/Module1277.lean), [Supporting result](../GD/Module1147.lean).

**Evidence sources**

- [Lean source](../GD/Module1162.lean)
- [Lean source](../GD/Module1277.lean)
- [Lean source](../GD/Module1147.lean)

<a id="result-0033"></a>

### What a finite primal–dual gap and a multiplier error certify

For a native affine-finite seed, a finite physical packet, nonnegative multipliers and a feasible rule in its relaxed packet cap, the exact quadratic identities bound projection and posterior squared distances by the primal–dual gap. In particular, if \(q\) is the relaxed-cap projection and \(p_w\) its packet posterior completion, the stated feasible primal value \(U\) and dual value \(L\) give
\(\|q-p_w\|_0^2\le U-L\), with a stronger twofold self-primal specialization and the corresponding square-root bound. Feasibility, multipliers and a vanishing gap are premises, not outputs.

For a **fixed** native packet, nonnegative weight rows \(w,v\), and any physical parameter \(\theta\), put \(\ell_\theta=dP_\theta/dP_0\) and
\(\operatorname{tail}_\theta(K)=\int_{\{\ell_\theta>K\}}\ell_\theta\,dP_0\).
If \(B\) is the packet-completion bound, then for \(K\ge0\),
\[
\mathbb E_\theta(p_w-p_v)^2
\le4B^2\left[K\|w-v\|_1+\operatorname{tail}_\theta(K)\right],
\qquad \operatorname{tail}_\theta(K)\to0.
\]
This transfers multiplier accuracy to squared distance under each named law. It gives neither a uniform nuisance tail nor control of arbitrary moving packets; numerical certification still needs a certified tail bound.

[Supporting result](../GD/Module1078.lean), [Supporting result](../GD/Module1048.lean).

**Evidence sources**

- [Lean source](../GD/Module1078.lean)
- [Lean source](../GD/Module1048.lean)

<a id="result-0009"></a>

### Conditional effective stopping from energy certificates

Suppose computable rational approximations to the finite projections and a convergent rational upper/lower bracket for their limiting projection energy are supplied, with the stated projection inequalities. An executable rational search returns an approximation with reference-norm error at most \(2^{-j}\). Qualitative convergence proves that the search terminates; an explicit convergence modulus and full-feasible approximating rules are unnecessary.

Conversely, a norm name with certified rational norm estimates yields convergent rational upper endpoint energies, with excess at most \(8\|P\|\delta+16\delta^2\). The native relaxed finite-cap projections instantiate the geometric inequality, and the named limit retains its existing strictness and terminality. This effective-stopping theorem assumes computable simple-function approximations and certified energies.

[Supporting result](../GD/Module0393.lean).

**Evidence sources**

- [Lean source](../GD/Module0393.lean)
- [Lean source](../GD/Module1434.lean)

<a id="result-0002"></a>

### A sharp three-rule disagreement-to-gain identity

For three real decisions \(f,g,h\), put
\[
u=\frac f2+\frac{2g}{13}+\frac{9h}{26},\qquad
E_*=4(g-f)^2+9(h-f)^2.
\]
Pointwise, for every target \(\mu\),
\[
(u-\mu)^2+\frac{E_*}{52}+\frac9{169}(g-h)^2
=\frac12(f-\mu)^2+\frac2{13}(g-\mu)^2+\frac9{26}(h-\mu)^2.
\]
If the three squared losses and three pairwise squared differences are integrable, this integrates to the risk identity. In particular, if all three risks are at most \(b\), then
\(R(u)+\frac1{52}\mathbb E E_*\le b\).
The coefficient \(1/52\) is sharp for the universal scalar common-cap inequality. This is the sharp coefficient for the stated scalar common-cap convexity inequality.

[Supporting result](../GD/Module1839.lean).

**Evidence sources**

- [Lean source](../GD/Module1839.lean)
- [Lean source](../GD/Module1844.lean)
- [Lean source](../GD/Module1842.lean)
- [Lean source](../GD/Module1841.lean)
- [Lean source](../GD/Module1861.lean)
- [Lean source](../GD/Module0355.lean)
- [Lean source](../GD/Module1832.lean)
- [Lean source](../GD/Module1362.lean)
- [Lean source](../GD/Module1837.lean)
- [Lean source](../GD/Module1432.lean)
- [Lean source](../GD/Module1433.lean)
- [Lean source](../GD/Module0510.lean)
- [Lean source](../GD/Module1860.lean)

<a id="result-0021"></a>

### Native variable envelopes retain their exact bounds under projective reduction

Let \(c_\theta\ge0\) be a native risk envelope with \(c_\theta\le C\tau_\theta\) for one finite \(C\ge0\), common positive-affine squared-risk character, and reflection invariance. If a raw Borel estimator satisfies \(R_\theta(d)\le c_\theta\) everywhere, then so does a rule obtained from a measurable projective coefficient \(g\in[0,1]\). The coefficient may depend on both residual-share and normalized mean-contrast coordinates. Summary projection, affine selection, reflection, representative repair and clipping preserve the **same** parameterwise envelope.

In particular, the envelope \(\min(v_X,v_Y)\) survives this reduction, giving the reduced excess constraint
\[
L_t(g)\le\frac{\min(t,1-t)}{\max(t,1-t)},\qquad0<t<1,
\]
in the specified normalization. No input covariance, admissibility, GD domination or minimaxity is assumed. The theorem transports feasibility under the displayed hypotheses.

[Supporting result](../GD/Module1557.lean).

**Evidence sources**

- [Lean source](../GD/Module1557.lean)

<a id="result-0024"></a>

### Radial moment constraints on native terminal projections

For an affine-finite native seed and its complete terminal projection \(P\), let \(N=m+n\), \(S=\|X\|^2\) under the standard Gaussian reference law, and \(E=\|P\|_0^2\). Then
\[
\int SP^2\,dP_0=(N+2)E,\qquad
\int S^2P^2\,dP_0\ge(N+2)(N+4)E.
\]
For \(E>0\), the energy-weighted probability \(P^2dP_0/E\) consequently has mean \(N+2\) and variance at least \(2(N+2)\) for \(S\). Finite physical risk supplies the radial-tilt integrability needed in these derivative identities. These moments concern the energy-weighted law, not the original observation law.

The separate transform statement is conditional: all dilation defects vanish exactly when
\((1-2t)^{(N+2)/2}\int e^{tS}P^2\,dP_0=E\) for every \(t<1/2\). No projection with vanishing defects is constructed by this characterization, and no unconditional chi-square-law claim is attached to the moment inequalities.

[Supporting result](../GD/Module1175.lean), [Supporting result](../GD/Module1196.lean).

**Evidence sources**

- [Lean source](../GD/Module1175.lean)
- [Lean source](../GD/Module1196.lean)

<a id="result-0011"></a>

### Cone values, transported optimizers, and exact symmetry regret

For an affine-finite native seed \(s\), let \(C(s)\) be its complete lower-risk cone and \(V_s(\theta)=\inf_{d\in C(s)}R_\theta(d)\). If \(g\) has scale factor \(a_g>0\),
\[
V_s(g\theta)=a_g^2V_s(\theta),\qquad
V_s(\mu,\sigma,\tau)=\sigma^2V_s(0,1,\tau/\sigma).
\]
On the equal-scale orbit \(g\theta_0=(b,a,a)\), the value is \(a^2\|P_s\|_0^2\) and the unique cone attainer, in the common almost-everywhere class, is the transported rule \(T_gP_s\). The untransported projection has exact regret
\[
R_{g\theta_0}(P_s)-V_s(g\theta_0)
=a^2\delta_{g^{-1}}(s),
\]
where \(\delta\) is the specified nonnegative orbit defect. These are parameterwise optimizers; they need not be distinct or one simultaneous attainer. The identity supplies no positive affine-terminal construction.

[Supporting result](../GD/Module1173.lean).

**Evidence sources**

- [Lean source](../GD/Module1173.lean)

<a id="result-0020"></a>

### Identical collar profiles do not identify a rule inside the canonical cap

For \(k\ge3\) and every \(n_i\ge4\), let
\(c_\theta=R_\theta(d_0)+\operatorname{canonicalStep}\operatorname{literalCross}(\theta)>0\)
be the canonical strict cap, and \(K=\{d:R_\theta(d)\le c_\theta\ \forall\theta\}\). A face-depth collar is defined by
\[
\frac{\sum_{i\notin A}\sigma_i^{-2}}{\sum_i\sigma_i^{-2}}
\le\frac1{j+1}.
\]
Every \(d\in K\) has supremum \(R_\theta(d)/c_\theta=1\) on every inhabited collar (zero on an empty collar). For every \(p,q\in K\), every inhabited collar and \(\varepsilon>0\), one **common** collar parameter satisfies
\[
\frac{\mathbb E_\theta(p-q)^2}{4c_\theta}<\varepsilon,
\qquad 1-\frac{R_\theta(p)}{c_\theta}<2\varepsilon,
\qquad 1-\frac{R_\theta(q)}{c_\theta}<2\varepsilon.
\]
Thus this entire cap has the same collar risk profiles, with simultaneous pairwise collapse. The denominator is this specific strict cap, not GD risk or oracle variance. This stronger whole-cap/every-pair statement retains the all-sizes-at-least-four gate.

[Supporting result](../GD/Module1650.lean).

**Evidence sources**

- [Lean source](../GD/Module1650.lean)

<a id="result-0006"></a>

### An exact covariant interval that essentially uses every group

For a nonempty ordinary design and \(0<\alpha<1\), put
\(\beta=1-(1-\alpha)^{1/k}\). Let \(q_i^-<q_i^+\) be the equal-tail Student cutoffs with \(n_i-1\) degrees of freedom and component rejection \(\beta\). Intersect the intervals
\[
I_i=[\bar X_i-q_i^+\sqrt{T_i},\ \bar X_i-q_i^-\sqrt{T_i}].
\]
If the intersection is empty, replace it by the singleton at \(\min_i\bar X_i\). The resulting interval has finite ordered Borel endpoints and exact coverage \(1-\alpha\) at every common mean and positive scale vector. It commutes with simultaneous design/data relabeling and common positive-affine transformations.

Put \(a_i=q_i^+-q_i^-\). Its width \(W\) is integrable and satisfies
\[
W\le a_i\sqrt{T_i}\quad\text{for every }i,\qquad
\frac{\mathbb E_\theta W}{\sqrt{\tau_\theta}}
\le\sqrt{\sum_i a_i^2}.
\]
For \(k\ge2\), it essentially depends on every group: for any omitted group and any Borel endpoint pair based only on the remaining summaries, agreement with these endpoints has probability strictly less than one under every physical law, even if the proposed factor is defined only on the positive-variance chamber.

Together, exact coverage, essential use of every group, and the finite oracle-relative width bound give a common-mean confidence procedure for the stated experiment.

[Supporting result](../GD/Module0717.lean), [Supporting result](../GD/Module0718.lean), [Supporting result](../GD/Module1360.lean).

**Evidence sources**

- [Lean source](../GD/Module0717.lean)
- [Lean source](../GD/Module0718.lean)
- [Lean source](../GD/Module1360.lean)

<a id="result-0032"></a>

### The positive-scatter common-mean likelihood has at most two maximizers

Let \(m,n>0\) be sample weights, \(a,b>0\) the positive scatters in the profile parametrization, and \(x,y\) the observed group centers. Define

\[
A(u)=a+(u-x)^2,\qquad B(u)=b+(u-y)^2,
\qquad
\ell(u)=-\frac12\{m\log A(u)+n\log B(u)\}.
\]

The global maximum set of \(\ell\) is nonempty, has at most two elements, and is contained in \([\min(x,y),\max(x,y)]\). All joint mean/positive-variance maximizers are exactly its injective profile lift

\[
u\longmapsto (u,A(u),B(u)),
\]

so the full joint likelihood also has at most two global maximizers.

The stationary equation is the nonzero cubic

\[
Q(u)=m(u-x)\{b+(u-y)^2\}
     +n(u-y)\{a+(u-x)^2\}=0.
\]

All its real roots lie between \(x\) and \(y\), and there are at most three. For positive integer weights, global maximization is exactly minimization of the positive algebraic objective \(A(u)^mB(u)^n\) on this complete finite root set. Equal observed means give the unique maximizer at that common center.

The two-maximizer bound is attained. For equal positive weights, equal scatter \(a>0\), and centers \(-d,d\), the maximizers are

\[
\begin{cases}
\{-\sqrt{d^2-a},\sqrt{d^2-a}\},&d^2>a,\\
\{0\},&d^2\le a.
\end{cases}
\]

Write the full log likelihood, omitting its data-only additive constant, as

\[
\ell_{\mathrm{full}}(u,v,w)
=-\tfrac12\{m\log v+n\log w+mA(u)/v+nB(u)/w\}.
\]

There is also an exact likelihood decomposition. For positive variances \(v,w\), put \(D(A,v)=A/v-1-\log(A/v)\). Then \(D(A,v)\ge0\), with equality exactly at \(v=A\), and

\[
\ell_{\mathrm{full}}(u,v,w)
=\ell(u)-\frac{m+n}{2}
 -\frac12\{mD(A(u),v)+nD(B(u),w)\}.
\]

This identifies the variance-profile lift and places the squared profile likelihood ratio in \((0,1]\). The finite candidate characterization supplies no certified root-isolation, tie-decision or likelihood-ratio algorithm.

[Complete profile maximum set](../GD/Module1815.lean), [joint lift](../GD/Module1820.lean), [cubic and symmetric cases](../GD/Module1816.lean), [divergence identity](../GD/Module1822.lean).

**Evidence sources**

- [Lean source](../GD/Module0505.lean)
- [Lean source](../GD/Module1820.lean)
- [Lean source](../GD/Module1815.lean)
- [Lean source](../GD/Module1822.lean)
- [Lean source](../GD/Module1814.lean)
- [Lean source](../GD/Module1816.lean)
- [Lean source](../GD/Module1827.lean)

## Combined evidence

| Evidence component | Evidence used |
|---|---|
| Integral evaluator bounds | Written formulas (75)–(76) and (87)–(90) and directed numerical evaluation supply finite-sum brackets, accumulated inner-ratio and rounding errors, and evaluator tolerances. Lean components prove tail estimates, posterior-division bounds, positive denominator floors and tolerance implications. |
| Risk-node enclosures | [the directed certificate](../certificates/README.md) supplies all 392 directed-rounded risk-node enclosures with the written error and transport arguments. [the physical node transport](../GD/Module1793.lean) proves the first-node evaluator and error-budget implication under containment of the exact finite sum in its specified interval. |
| Continuum interpolation | [the written proof](../proofs/Proof0003.md)/[the directed certificate](../certificates/README.md) supply the 28-block cardinal/Bernstein interpolation certificate and printed continuum margin, using the retained node balls, basis and radius errors, and block cover. Lean verifies conditional interpolation arithmetic; [the exact cosine enclosures (1)](../GD/Module0001.lean) and [the exact cosine enclosures (2)](../GD/Module0447.lean) verifies the separate exact cosine table. |
| Compact-wall enclosure | [the written proof](../proofs/Proof0003.md)/[the directed certificate](../certificates/README.md) supply the 225-cell wall certificate and exact positive minimum. Written analytic error bounds and directed arithmetic establish the physical integral enclosures. Lean verifies the rational cell data and the cover implication under those enclosures. |
| Normalized charge columns | [the written charge argument](../proofs/Proof0003.md)/[the directed certificate](../certificates/README.md) supply the five directed-rounded normalized odd-charge columns, including finite charge evaluations, inner errors and positive normalization. Lean components prove charge quadrature and truncation bounds; the downstream implications assume membership in the specified rational columns. |
| Positive normalized solution | [the exact inverse ledger](../GD/Module0369.lean) verifies the inverse/error ledger. [the positive-solution implication](../GD/Module0370.lean) proves invertibility and the unique positive normalized solution, the printed weight bound and undoing normalization, assuming actual columns in the certified box and positive normalization. [the charge-column enclosures](../certificates/Certificate0003/Data0006.json) supplies these premises through written arguments and directed numerical certificates. |
| Reciprocal-pair balance | [the positive-solution implication](../GD/Module0370.lean) proves positive reciprocal-pair balance under normalized odd-charge box membership and positive column normalization, supported by [the charge-column enclosures](../certificates/Certificate0003/Data0006.json). [the physical degree-six implication](../GD/Module1438.lean) supplies physical charge reciprocity and the centered/pure basis connection. |
| [Physical double-Haar domination](#named-0014) | [the physical global-margin implication](../GD/Module1437.lean) proves strict physical Haar domination at every positive variance ratio from the actual lower bounds J ≥ a and K ≥ b. The written proof and continuum/wall certificates in [the continuum certificate](../certificates/Certificate0003/Data0008.json)/[the wall certificate](../certificates/Certificate0003/Data0009.json) supply those bounds. [the physical endpoint theorem](../GD/Module1437.lean) also proves domination near both endpoints with existential cutoffs. |
| [Degree-six weak-improvement exclusion](#named-0005) | [the physical degree-six implication](../GD/Module1438.lean) proves the physical degree-six risk obstruction assuming actual charge-box membership and positive normalization, supported by [the charge-column enclosures](../certificates/Certificate0003/Data0006.json). It derives the risk identity, energy properties, positive Gram forms, reciprocity and basis conversion. The printed milestone uses the original box; the theorem also provides an enlarged-box route. |


## Proof-family evidence

The [written-proof guide](Proofs.md) links the five full analytic arguments and their inputs. Their support is divided as follows:

| Result and family | Written and computational evidence | Lean evidence |
|---|---|---|
| real-shape eight-tent construction | The written proof identifies real-power Gamma derivatives, uniform derivative/finite-difference estimates, normalized tent integrals, finite energy and the reduced-risk identity for each fixed positive shape pair. The exact symbolic audit checks the algebra. | The six-jet identity, node/denominator conditions, eight-node expansion, exchange covariance, uniform-approximation/smearing implications and strict quadratic step. |
| historical two-stage descent | The written proof supplies the physical-to-projective risk identity, tent averaging and error estimates, Borel legality, finite risk, the full variance-range argument, ray-turn witness and finite-prior square completion. The two-stage rational certificate checks the 50,000-cell nuisance cover and transverse two-bump cover. | The two-stage-descent source guide links proofs of the projective kernel measure identity, exact tent moments, rational interval arithmetic, continuum-cover statements and physical strict-margin implications. |
| double-Haar domination and degree-six obstruction | The written proof supplies the Dirichlet/Feynman risk and charge representations, integrability, actual Gram-matrix positivity and analytic interval-error bounds. Directed certificates cover five charge columns, 392 interpolation nodes and 225 wall cells; exact rational checks establish the positive simplex. | Exact margins, conditional interpolation, finite wall-cover and reciprocal-pair/finite-mixture algebra, together with the physical implications and premises described in the component descriptions above. |
| native (3,3) minimax | The audited written proof establishes the finite rational packets, logarithmic integrals, posterior moments, common-window bound for N ≥ 16 and the physical endpoint value 1 + π/4 with its displayed attaining rule. It also gives the refined packet/posterior consequences. | The conditional window-bound algebra, endpoint primitive, finite-window/tail bounds, mesh inequalities, exact mass and integrated single-bin comparisons, with the linked reduced-cap, density and minimax bridge modules at their stated hypotheses. |
| two-observation physical risk | The written proof identifies the Gaussian inverse-square Laplace transform and weighted second moment through Tonelli, transports the result to the physical GD estimator, and proves deletion-limit nonuniform integrability in the specified coupling. | The transformed moment integral, finite weighted sum, sharp normalized inequality, and equal-scale/three-group algebra. |

The [result entries](#result-0034) give the mathematical statements, sample-size domains, competitor classes and individual source links. The [reproduction guide](Reproducing.md) provides source replay and certificate-checking commands.



## Named final results

<a id="named-0016"></a>

### Real-shape reduced-risk improvement

For every fixed $\alpha,\beta>0$, at most eight normalized product tents and one positive step strictly reduce the reduced risk for every $e\in(0,1)$.

For every fixed alpha,beta>0 there is a bounded continuous at-most-eight normalized-product-tent profile with disjoint compact interior supports and one positive step that strictly reduces the literal reduced risk for every e in (0,1), with coherent exchange antisymmetry. No shape-uniform margin or noninteger Gaussian experiment is asserted.

[Written proof](../proofs/Proof0001.md). [Lean source 1](../GD/Module1725.lean). [Lean source 2](../GD/Module1728.lean). [Lean source 3](../GD/Module1562.lean). [Lean source 4](../GD/Module1724.lean). [Lean source 5](../GD/Module1727.lean).

<a id="named-0013"></a>

### Physical Gaussian strict improvement

For every $m,n\ge2$, the coherent correction gives a finite-risk Borel rule that strictly improves GD at every common mean and pair of positive scales.

For natural m,n>=2, positive population scales and arbitrary common mean, the half-integer residual shapes are (m-1)/2,(n-1)/2. The actual Gaussian squared-risk increment of the coherent correction equals the total mean-variance scale times the displayed positive Gamma prefactor times the reduced quadratic increment; the resulting finite-risk Borel rule strictly improves GD at every parameter.

[Written proof](../proofs/Proof0001.md). [Lean source 1](../GD/Module0524.lean). [Lean source 2](../GD/Module1725.lean). [Lean source 3](../GD/Module1728.lean). [Lean source 4](../GD/Module1726.lean). [Lean source 5](../GD/Module1727.lean). [Lean source 6](../GD/Module0523.lean). [Lean source 7](../GD/Module0190.lean).

<a id="named-0003"></a>

### Balanced rank obstruction

For every $\gamma>0$, the specified balanced four-channel system has rank three; adjoining the constant target raises the rank to four, so that target is outside its span.

For gamma>0 the four specified normalized actual channels have rank three; their odd channels are nonzero, span exactly the two-dimensional space generated by X and X^3, and only channel 10 is even. Vanishing quadratic coefficient forces that channel coefficient and the constant coefficient to vanish. Thus one is not in the four-jet span and the augmented rank is four. This is not an eight-tent minimality assertion.

[Written proof](../proofs/Proof0001.md). [Lean source 1](../GD/Module0339.lean). [Lean source 2](../GD/Module0340.lean). [Lean source 3](../GD/Module0341.lean). [Lean source 4](../GD/Module1563.lean). [Lean source 5](../GD/Module0518.lean).

<a id="named-0009"></a>

### First physical strict margin

At every physical parameter, $R_\theta(GD)-R_\theta(d_a)>\frac{351\eta^2\sigma^4\tau^4}{500000\pi(\sigma^2+\tau^2)^3}>0$.

R(d_a)-R(d0)<-351eta^2 sigma^4 zeta^4/(500000pi(sigma^2+zeta^2)^3)<0 at every physical parameter.

**Hypotheses:** Independent Gaussian samples of sizes (2,2), common mean mu in R, positive population scales sigma,zeta; printed eta=10^-5, a=1/250, rho=10^-12, t=10^-4 and exact coefficient table.

**Scope:** Remaining sign and physical composition must retain a=1/250. Existing historical small-amplitude domination does not apply.

[Written proof](../proofs/Proof0002.md). [Lean source 1](../GD/Module1581.lean). [Lean source 2](../GD/Module1582.lean). [Lean source 3](../GD/Module1583.lean). [Lean source 4](../GD/Module1584.lean). [Lean source 5](../GD/Module1585.lean). [Lean source 6](../GD/Module1586.lean). [Lean source 7](../GD/Module1587.lean). [Lean source 8](../GD/Module1588.lean). [Lean source 9](../GD/Module1589.lean). [Lean source 10](../GD/Module1590.lean). [Lean source 11](../GD/Module1591.lean). [Lean source 12](../GD/Module1592.lean). [Lean source 13](../GD/Module1593.lean). [Lean source 14](../GD/Module1594.lean). [Lean source 15](../GD/Module1595.lean). [Lean source 16](../GD/Module1596.lean). [Lean source 17](../GD/Module1597.lean). [Lean source 18](../GD/Module1598.lean). [Lean source 19](../GD/Module1599.lean). [Lean source 20](../GD/Module1600.lean). [Lean source 21](../GD/Module1601.lean). [Lean source 22](../GD/Module1602.lean). [Lean source 23](../GD/Module1603.lean). [Lean source 24](../GD/Module1604.lean). [Lean source 25](../GD/Module1628.lean).

<a id="named-0007"></a>

### Doubled-step counterexample

At population scales $(19,1)$, doubling the seed step worsens risk: $R_\theta(d_{2a})>R_\theta(d_a)$.

At q=1/362 the multiplier-three tent bracket exceeds 739/1000, hence R(d_2a)>R(d_a) at scales (19,1).

**Hypotheses:** Independent Gaussian samples of sizes (2,2), common mean mu in R, positive population scales sigma,zeta; printed eta=10^-5, a=1/250, rho=10^-12, t=10^-4 and exact coefficient table.

**Scope:** The actual center enclosure and multiplier-three remainder remain necessary; a rational arithmetic implication alone cannot supply them.

[Written proof](../proofs/Proof0002.md). [Lean source 1](../GD/Module1627.lean). [Lean source 2](../GD/Module1606.lean).

<a id="named-0018"></a>

### Second physical strict descent

The specified two-bump correction satisfies $R_\theta(\widetilde d)<R_\theta(d_a)$ at every physical parameter.

Multiplying the pointwise transverse gap by the common tent, using 0<=H<=1, H^2<=H and a positive-area core, then reflection and QJ=0, gives R(d_tilde)<R(d_a) for every physical parameter.

**Hypotheses:** Independent Gaussian samples of sizes (2,2), common mean mu in R, positive population scales sigma,zeta; printed eta=10^-5, a=1/250, rho=10^-12, t=10^-4 and exact coefficient table.

[Written proof](../proofs/Proof0002.md). [Lean source 1](../GD/Module1624.lean). [Lean source 2](../GD/Module1625.lean).

<a id="named-0015"></a>

### Positive finite-packet floor

For this fixed seed, every finite nonnegative weighted packet with weight-one reference atom $(\mu,\sigma,\tau)=(0,1,1)$ has posterior error $B_a>27t^2\rho^2/131072>10^{-36}$.

On the A core J^2>=9/16 and W_(1/2)>1/16 with area rho^2; hence every finite packet satisfies B_a>27t^2rho^2/131072>10^-36.

**Hypotheses:** Independent Gaussian samples of sizes (2,2), common mean mu in R, positive population scales sigma,zeta; printed eta=10^-5, a=1/250, rho=10^-12, t=10^-4 and exact coefficient table.

**Scope:** This fixed-seed anchored excess is not a universal seed floor or a terminal-projection defect.

[Written proof](../proofs/Proof0002.md). [Lean source 1](../GD/Module1630.lean). [Lean source 2](../GD/Module1607.lean).

<a id="named-0014"></a>

### Physical double-Haar domination

The finite-risk Borel double scale-Haar posterior mean strictly improves GD for every positive variance ratio.

For every eta>0 in the actual (11,11) common-normal-mean experiment, the Borel finite-risk double scale-Haar posterior mean has strictly smaller squared risk than GD. Compose actual continuum and wall margins with log(50)<4, the exact positive normalization and physical sample-swap law.

[Written proof](../proofs/Proof0003.md). [Lean source 1](../GD/Module0188.lean).

<a id="named-0005"></a>

### Degree-six weak-improvement exclusion

Every nonzero correction in the specified ten-dimensional degree-six correction class increases the Haar rule's physical risk at some positive variance ratio.

For every nonzero correction Delta*(A(WH)*Fstar-B(WH)) with A,B in h*(1-h)*R[h]_(<=4), at least one positive variance ratio has strictly greater physical squared risk than the Haar rule. Compose the actual quadratic risk identity, positive definite Gram matrices and strictly positive ten-atom zero-charge balance. No unrestricted admissibility or higher-degree exclusion follows.

[Written proof](../proofs/Proof0003.md). [Lean source 1](../GD/Module0240.lean). [Lean source 2](../GD/Module0185.lean).

<a id="named-0017"></a>

### Reduced minimax and dual nonattainment

The reduced minimax value is $\pi/4$, attained by the squared-precision coefficient; no finite interior mixture attains the dual supremum.

Using actual numerical packet convergence and weak duality, sup_(P finite rational)B(P)=inf_(g Borel Ω→[0,1])sup_(0<t<1)L_t(g)=π/4, the coefficient minimum is attained by g_sq and no finite interior mixture attains the dual supremum.

[Written proof](../proofs/Proof0004.md). [Lean source 1](../GD/Module1405.lean).

<a id="named-0008"></a>

### Exact unrestricted native minimax

At $(3,3)$, the minimax values over all Borel, finite-risk Borel and affine finite-risk rules equal $1+\pi/4$, attained by the squared-precision rule with midpoint fallback.

At (3,3), treat infinite worst risk separately and conclude inf over all Borel rules = inf over every-parameter finite-risk Borel rules = inf over their positive-affine members =1+π/4, attained by the printed squared-precision rule.

[Written proof](../proofs/Proof0004.md). [Lean source 1](../GD/Module1399.lean). [Lean source 2](../GD/Module1379.lean). [Lean source 3](../GD/Module1910.lean). [Lean source 4](../GD/Module1463.lean). [Lean source 5](../GD/Module1913.lean). [Lean source 6](../GD/Module1900.lean). [Lean source 7](../GD/Module0980.lean).

<a id="named-0020"></a>

### Size-three-pair lower bound

Every ordinary many-group design containing two distinct groups of size three has oracle minimax value at least $1+\pi/4$.

For every ordinary many-group design containing two distinct groups of size three, use exact all-Borel pair deletion to prove V_design≥1+π/4, including infinite values and arbitrary ordinary companion sample sizes.

[Written proof](../proofs/Proof0004.md). [Lean source 1](../GD/Module1911.lean). [Lean source 2](../GD/Module1910.lean). [Lean source 3](../GD/Module1443.lean). [Lean source 4](../GD/Module1442.lean).

<a id="named-0004"></a>

### Both-sample-means impossibility

At $(3,3)$, no Borel estimator has risk at most $\min(\sigma^2/3,\tau^2/3)$ at every physical parameter.

At native (3,3), no Borel estimator d has Rθ(d)≤min(σ_X²/3,σ_Y²/3) for every physical θ; apply the literal nineteen-packet contradiction to the single full-coordinate coefficient furnished by the fine-cap reduction.

[Written proof](../proofs/Proof0004.md). [Lean source 1](../GD/Module1558.lean).

<a id="named-0010"></a>

### GD-relative gain ceiling

At $(3,3)$, the all-Borel uniform relative gain over GD obeys $\Gamma_{3,3}\le1/2-\pi/8$.

If c=supθRθ(d)/Rθ(GD)<∞ then d has oracle cap 2c, so c≥(1+π/4)/2. Treat infinite worst relative risk under the printed extended convention, take the supremum over Borel d, and conclude Γ_(3,3)≤1/2−π/8 without an equality claim.

[Written proof](../proofs/Proof0004.md). [Lean source 1](../GD/Module1558.lean). [Lean source 2](../GD/Module1911.lean). [Lean source 3](../GD/Module1910.lean). [Lean source 4](../GD/Module1912.lean). [Lean source 5](../GD/Module1049.lean).

<a id="named-0001"></a>

### All-two physical exact risk

At every common mean and positive scale vector, $R_\theta(GD)=\frac14\left[\frac{\sum_i\sigma_i}{\sum_i\sigma_i^{-1}}+\frac{k}{(\sum_i\sigma_i^{-1})^2}\right]$.

Actual GD risk at arbitrary mu and positive scales equals {sum sigma/sum sigma^-1 + k/(sum sigma^-1)^2}/4.

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.

**Scope:** Uses the specified actual baseline conditional-risk theorem and finite-risk Gaussian prerequisites; does not assume a fictitious independent weight/mean model.

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module0569.lean). [Lean source 2](../GD/Module1345.lean).

<a id="named-0019"></a>

### Sharp oracle ratio and equal-scale risk

The oracle-normalized GD risk is at least $(k+1)/2$, with equality at equal scales; there GD risk is $\sigma^2(k+1)/(4k)$ and oracle risk is $\sigma^2/(2k)$.

Actual oracle ratio is (sum p_i^2)(sum p_i^-1+k)/2 >=(k+1)/2, with equality at equal scales; equal-scale GD and oracle risks are sigma^2(k+1)/(4k) and sigma^2/(2k).

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module1348.lean).

<a id="named-0012"></a>

### Nonvanishing equal-scale risk

For fixed $\sigma>0$, the equal-scale GD risk stays above $\sigma^2/4$ as the number of groups grows.

For fixed sigma>0, the equal-scale risks do not tend to zero as k grows; the positive lower bound sigma^2/4 is independent of k.

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.; sigma fixed and k tends to infinity.

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module1349.lean).

<a id="named-0006"></a>

### Divergent three-group risk

Along the positive scale curve $(1,1,r)$, GD risk exceeds $r/8$ and diverges as $r\to\infty$.

For scales (1,1,r), r>0, actual risk equals r/8+3r(4r+1)/(8(2r+1)^2)>r/8 and is unbounded as r increases.

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.; k=3 and sigma=(1,1,r).

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module1348.lean). [Lean source 2](../GD/Module1351.lean).

<a id="named-0002"></a>

### Almost-sure deletion and finite limiting risk

Along that curve under the fixed Gaussian coupling, GD converges almost surely to the first-two-group GD rule, whose risk is $3/8$.

Along real r tending to infinity, coupled GD errors and squared errors converge almost surely to the first-two-group GD rule; its squared error is integrable and expectation is 3/8.

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.; k=3, scales (1,1,r), first-two restriction of the fixed Gaussian coupling.

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module1352.lean).

<a id="named-0011"></a>

### Nonuniform integrability

The squared losses along that curve are not uniformly integrable; their expectations diverge although the almost-sure limiting loss has expectation $3/8$.

The coupled squared errors are not uniformly integrable on positive scale tails or any scale sequence tending to infinity. Uniform integrability together with almost-sure convergence would imply convergence of expectations, contradicting divergent risk and limiting risk 3/8.

**Hypotheses:** Finite k>=1, two observations per group, independent common-mean Gaussian samples, arbitrary mu, all sigma_i>0; literal stabilized inverse estimated-mean-variance GD baseline.; r tends to infinity under one fixed Gaussian probability law.

[Written proof](../proofs/Proof0005.md). [Lean source 1](../GD/Module1351.lean).
