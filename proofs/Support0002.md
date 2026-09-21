# Raw transport needed for the both-means consequence

**Continuum proof order:** I independently rederived the window estimate. After
`s=x*exp(r)`, restrict the original nonnegative squared-loss integral to the
common log-observation interval
`[A+log(b), A+T+log(a)]` **before** replacing the loss by `g^2-2*d` and its
reflected counterpart by `(1-g)^2-2*d`. Those lower bounds can be negative, so
discarding the non-common part after that replacement is not justified. With
the restriction first, the asserted factor
`rho*(1-log(b/a)/T)*(J-d*M)` follows for arbitrary bounded Borel g.

The reduced comparison gives the reduced bound
`b(t) = min(t,1-t)/max(t,1-t)` and the N=19 arithmetic:
`12996 = 2*(19^3-19^2)`,
`B19 > pi/4 - 14/19 > 1/76 > 1/(19^4-1)`.

For a conclusion against **all raw Borel estimators**, explicitly include the
variable-envelope equivariantization step. The exact theorem
`GD.N0045.d023068` in
[Supporting evidence](../GD/Module1461.lean)
assumes a **constant** oracle cap C. Applying it with C=2 gives only `Lt <= 1`,
which is insufficient for this N=19 obstruction.

The variable-envelope extension uses the following construction: inside the existing compact oracle cap 2,
restrict to the weakly closed convex set
`risk(theta,p) <= ofReal(min(scale1^2/m,scale2^2/n))` for every physical theta,
and the sufficient-summary fixed subspace. The minimum-of-mean-variances
envelope scales by the same positive factor as squared risk under affine
transport and is unchanged by reflection. The current restricted-cap fixed
point theorem, summary purification, reflection averaging, exact Borel repair
and projective clipping therefore have the required preservation properties.
State/prove these properties at that envelope before transferring the packet
obstruction to raw rules.

At total variance one the exact risk decomposition is
`risk = t*(1-t)*(1 + Lt)`. Thus the preserved physical envelope
`risk <= min(t,1-t)` yields
`Lt <= min(t,1-t)/max(t,1-t)`.
