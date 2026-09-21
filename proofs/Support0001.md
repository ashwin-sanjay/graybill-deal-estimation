# Constant and variable envelopes

The existing `GD.N0045.d023068` in [Supporting evidence](../GD/Module1461.lean), has the constant physical hypothesis

\[
R_\theta(d)\le C\tau_\theta\quad\hbox{for every }\theta,
\]

and returns one bounded Borel coefficient with

\[
\int(g-t)^2\,dQ_t\le(C-1)t(1-t)\quad\hbox{for every }t.
\]

Therefore the written lower bound `inf_g sup_t L_t(g) >= pi/4`, together with the existing squared-precision upper bound, gives the intended unrestricted `(3,3)` value conclusion. The concrete integral lower bound is supplied by the written proof; the Lean implications use the stated window bounds.

For the stronger two-individual-means consequence, the packet bound

\[
L_t(g)\le b(t):=\frac{\min(t,1-t)}{\max(t,1-t)}
\]

uses a **parameter-dependent** envelope. The constant-cap theorem alone does not retain that envelope. A written proof or checked adapter preserving the physical cap `R_theta(d) <= min(sigma_X^2/m,sigma_Y^2/n)` through the affine/summary/clipping reduction would supply the missing implication for the unrestricted both-means obstruction. Without this extra argument, the `N=19` comparison certifies the reduced-class obstruction only. This note does not claim that such an adapter is absent from the larger project.

No ordinary-admissibility or uniqueness conclusion follows from the moving `L2(mu_N)` regret bounds alone.
