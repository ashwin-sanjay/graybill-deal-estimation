# Exact risk at the smallest allowed sample sizes

This calculation addresses the literal design `n_i=2`, for any `k≥1`, and
uses the Graybill–Deal baseline and squared loss.
No literature is used.

## Exact physical risk (mathematical derivation)

Write `Z_i=(X_i1-X_i2)/(sqrt(2) sigma_i)` and
`Y_i=(X_i1+X_i2)/2`. Orthogonal change of variables in the Gaussian density
shows that the Z_i are independent standard normals, independent of all
Y_i, and that Y_i has mean mu and variance sigma_i²/2. Thus

    v_i = sigma_i² Z_i²/2,
    A_i = 2/(sigma_i² Z_i²),
    W_i = A_i / sum_j A_j.

The exceptional zero-residual sets are null. Conditional on Z, the squared
error expectation is `sum_i sigma_i² W_i²/2`.

Here is a direct derivation of the needed transform. For b>0, set

    J(b) = integral_0^infinity exp(-(x²+b²/x²)/2) dx.

Differentiation under the integral gives
`J'(b)=-b integral x^-2 exp(-(x²+b²/x²)/2) dx`.
The substitution `x=b/y` makes this `-J(b)`. The differentiations on each
compact b-interval inside (0,infinity) are dominated: at zero the factor
`exp(-b_min²/(2x²))` absorbs inverse powers, and at infinity the Gaussian
absorbs positive powers. Dominated convergence at b=0 gives
`J(0)=sqrt(pi/2)`. Therefore `J(b)=sqrt(pi/2) exp(-b)`, and

    E exp(-t A_i) = exp(-c_i sqrt(t)),   c_i = 2/sigma_i,   t>0.

Let `C=sum_i c_i`, `p_i=c_i/C`, and `A=sum_i A_i`. Positivity permits
Tonelli in `A^-2=integral_0^infinity t exp(-t A) dt`. Differentiating the
individual transform twice is valid for t>0 because `x² exp(-t x)` is
bounded uniformly on every compact positive t-interval. Independence gives

    E[W_i²]
      = integral_0^infinity t (d²/dt² exp(-c_i sqrt(t)))
          exp(-(C-c_i) sqrt(t)) dt
      = integral_0^infinity ((c_i² u+c_i)/2) exp(-C u) du
      = (p_i²+p_i)/2.

The second line substitutes `t=u²`. There are no unbounded-moment
assumptions on A_i: the nonnegative Tonelli identity proves finiteness
through the evaluated integral. The same first-derivative argument gives
`E W_i=p_i`, hence `Var(W_i)=p_i(1-p_i)/2` and
`E W_i W_j=p_i p_j/2` for distinct i,j (by the mixed first derivatives).
Consequently the entire normalized weight covariance matrix is
`(diag(p)-p p^T)/2`.

Combining the conditional risk and squared-weight moments yields

    R_(mu,sigma)(b)
      = (1/4) [(sum_i sigma_i)/(sum_i sigma_i^-1)
               + k/(sum_i sigma_i^-1)²].                         (1)

In particular, every finite positive variance vector has finite risk.

## Sharp comparison and an explicit three-group boundary

The known-variance oracle risk is
`O(sigma)=1/(2 sum_i sigma_i^-2)`. Formula (1) gives

    R(b)/O = (sum_i p_i²)(sum_i p_i^-1 + k)/2 >= (k+1)/2.        (2)

Indeed `sum p_i²>=1/k` and `sum p_i^-1>=k²` by two applications of
Cauchy-Schwarz. Equality holds at equal scales. At equal scales (1) is
`sigma²(k+1)/(4k)`: adding groups does not drive this baseline risk to zero.
This is a comparison to an oracle depending on unknown parameters, not a
constructible dominance witness.

For three groups with scales `(1,1,r)`, exact algebra gives

    R(b) = r/8 + 3r(4r+1)/(8(2r+1)²) > r/8.                   (3)

Thus the risk is unbounded as the third standard deviation grows, although
ignoring the third group and averaging the first four observations has risk
1/4 on this submodel. That averaging rule is not asserted to dominate on
the full parameter space. Equation (3) exposes the rare-small-residual
contribution that is lost by a pointwise argument that the noisy group's
weight tends to zero.

Under the common coupling `Y_3=mu+r V_3/sqrt(2)` and fixed nonzero
`Z_3`, the third precision is O(r^-2) and its weighted mean numerator is
O(r^-1). Thus the three-group estimator converges almost surely to the
two-group baseline using the first two groups. That limit has risk 3/8,
whereas the approximating risks diverge. In particular their squared errors
are not uniformly integrable. This supplies a concrete physical failure of
passing risk through an almost-sure group-deletion limit.

## Exact Lean coverage

`GD/Module0161.lean`
checks the actual improper integral in the transformed second-moment
calculation (`GD.N0232.N0719.N1023.d001843`), its finite weighted-sum evaluation
(`GD.N0232.N0719.N1023.d001845`), the sharp normalized inequality and its attained
uniform case, equal-scale algebra, and the explicit three-group lower bound
and unboundedness for `GD.N0232.N0719.N1023.d001844`.

The Gaussian-to-inverse-square Laplace transform, the probabilistic Tonelli
identification, and the identification of `GD.N0232.N0719.N1023.d001844` with literal
`GD.N0232.N0719.d009176` risk are proved above in ordinary mathematical prose,
not by that Lean module. These mathematical identifications supply the statistical interpretation of the Lean identities.

## Scope of the calculation

The two-sample negative endpoint does not transfer merely by restricting a
many-group variance vector. A dominator on an equal-variance submodel need
not dominate at other variance vectors. Likewise (2) and (3) alone do not
supply a single full-model dominator or exclude an affine admissible strict
improvement. The mathematical contribution is the exact baseline risk and
weight covariance at all two-observation designs, rather than an additional
conditional route to terminality.
