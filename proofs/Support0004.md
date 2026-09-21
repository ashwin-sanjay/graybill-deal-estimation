# Normalization, packet estimates and variable-envelope transfer

## Checks performed

1. **Physical Gaussian normalization.** With the author's convention
   `t = vY/(vX+vY)`, the oracle coefficient on `Xbar-Ybar` is t. The oracle
   error is independent of the difference and the residual variances. Weighting
   the independent chi-square-one contrast law by its value gives the normalized
   chi-square-three law. The Jacobian of `(a,b,w)=(r*(1-u),r*u,r*s)` is `r^2`.
   The resulting radial Gamma ratio is `Gamma(7/2)/Gamma(3/2)=15/4`, and the
   powers of two supply the stated factor 15. Thus the genuine reduced density
   is `f_t=t*(1-t)*K_t`, consistent with the exact maintained
   `GD.N0062.d022145`. Consequently
   `R/tau=1+Lt`, with no missing oracle factor.

2. **Upper bound and finite quadratic completion.** The two rational identities
   in Section 2 simplify exactly; both residuals are zero. Their positivity conditions are the stated
   `0<=q<1` and `3<pi<4`. Finite mixture completion has nonnegative remainder,
   and all terms are integrable because each interior kernel has total mass
   `1/(t*(1-t))`. Every finite mixture is strictly below pi/4 by evaluating at
   g0; it is not necessary to identify the finite-mixture minimizer with g0.

3. **Endpoint kernel and tails.** The primitive and integral
   `integral k_u = u^(-2)` have the correct normalization. The small-x bound is
   `(5/(4*sqrt(2)))*(a/u)^(3/2)`, and the large-x bound is
   `15*u^2/(2*b^2) <= 8/b^2`. For the specified cutoffs,
   `(a/eta)^(3/2)=N^(-3)`, giving the stated theta_N and truncation error.

4. **Continuum window.** Section 5 applies for arbitrary
   Borel g in [0,1]. After `s=x*exp(r)`, the shared log-observation interval has
   length `T-log(b/a)`. One must restrict the original nonnegative square to
   that interval before replacing the square by `g^2-2*d` or
   `(1-g)^2-2*d`; those replacements can be negative. The maintained manuscript
   explicitly uses this correct order. The remaining integral is
   `(rho/(2*T))*|W|*integral[alpha*g^2+gamma*(1-g)^2-2*d*(alpha+gamma)]`,
   whose pointwise quadratic minimum yields precisely
   `rho*(1-log(b/a)/T)*(J-d*M)`. No boundary limit of g is assumed.

5. **Discrete mesh.** In a bin, `q*t0 <= t <= t0 <= d`. Each positive term in
   D satisfies `D_t >= (1-d)*D_t0`, and
   `(t/t0)^2 >= q^2`, while `(1-t)/(1-t0) >= 1`. This proves the stated kernel
   factor `c=q^2*(1-d)^(7/2)`. Kernel comparison is applied to the nonnegative
   square first. The loss perturbation is at most `2*(t0-t)`, and its integrated
   error is bounded by `2*c*(q^(-1)-1)/(1-d)`. Bin averaging gives the exact
   claimed inequality for B_N.

6. **Constants, packet mass and quantifiers.** Bernoulli's inequality and the
   displayed induction give `d_N <= N^(-4)` for N>=16. All three window
   requirements hold at these choices. The polynomial remainder coefficient
   `5735/8192` is correct, as are the sharper Section 11 coefficients. The
   packet has `2*(N^3-N^2)` atoms with reciprocal common mass, and the n-indexed
   normalization is `1/(512*n^2*(16*n-1))`. Every estimate precedes the
   infimum over the same arbitrary bounded Borel coefficient class. Weak duality
   alone suffices for beta=pi/4.

7. **Unrestricted sharpness.** The cited
   `GD.N0045.d023068` really takes
   an arbitrary raw Borel estimator and a uniform constant oracle cap C, with
   no terminality or equivariance assumption on that input. If its worst
   normalized risk is finite, use that very supremum as C; otherwise the lower
   bound is automatic. The theorem yields `Lt <= C-1`, and the packet limit
   forces `C>=1+pi/4`. The squared-precision upper attainer is therefore
   unrestricted minimax. Values assigned on the common null set do not affect
   this risk conclusion. Ordinary admissibility and general designs remain
   separate.

8. **Scope of the N=19 obstruction.** The reduced cap is exactly
   `b(t)=min(t,1-t)/max(t,1-t)`, since total-variance-normalized risk is
   `t*(1-t)*(1+Lt)`. The atom count is 12996, and
   `B19 > pi/4-14/19 > 1/76 > 1/130320 >= integral b dP19`.
   This proves the bounded projective-coefficient obstruction. Applying the
   existing constant-cap theorem with C=2 would yield only `Lt<=1`, which is
   too weak. The initial Section 10 expressly preserved that boundary. A raw
   transfer can restrict the existing weak compact cap 2 to the weakly closed
   convex minimum-variance envelope, checking its affine transport, summary
   purification, reflection and clipping preservation. The later Section 10.1
   now carries out that extension, reviewed next.

## Review of the later fine-cap and relative-gain additions

Section 10.1 uses precisely the invariant weakly compact set required for the
unrestricted conclusion. The minimum of the mean variances is at most twice
the oracle variance, so this set lies inside the existing finite cap 2. Its
reference constraint bounds the L2 norm; risk-cone closedness and convexity
give weak compactness. Its affine squared-scale covariance and reflection
invariance are the same as squared loss. Consequently the existing weak action
on cap 2 restricts to it with its continuity, affine-combination and group-law
properties intact. The cited log-scale fixed-point theorem applies on that
restricted set. Exact Borel representative repair preserves every physical
risk because all physical laws share the same null sets.

The exact declaration
`GD.N0024.N0271.d028029`
in
[Supporting evidence](../GD/Module1643.lean).
It requires an ordinary design, an everywhere-affine finite-risk Borel input,
a finite extended-real budget, reflection invariance of that budget, and the
pointwise risk bound. Section 10.1's repaired fixed class satisfies all of
these conditions. The conclusion preserves the precise budget through summary
reduction and clipping. Thus the newly written argument does complete the
**paper-level unrestricted no-Borel-below-both-means result at (3,3)**, even
without ordinary admissibility or any strictness requirement. This is the special-design obstruction at (3,3).

Section 10.2 is also consistent: for the GD coefficient u, the pointwise
integrand is strictly below one because the denominator squared minus
`(u-t)^2` is `4*t*(1-t)*u*(1-u)>0`. Hence GD's oracle-normalized risk is below
2. A finite relative-risk cap c supplies oracle cap 2c, so sharp V33 forces
`c >= (1+pi/4)/2` and therefore `Gamma33 <= 1/2-pi/8`. This is an upper bound,
not an assertion of the sharp positive gain value.

The variable-envelope theorem supplies the stated reduction; current verification records identify its checked source.

The moving-measure regret bounds do not establish uniqueness in a fixed
L2 space, a specified generalized-Bayes representation, or ordinary
admissibility. Section 11 correctly says so and identifies loss of mass on
every fixed interior compact set.
