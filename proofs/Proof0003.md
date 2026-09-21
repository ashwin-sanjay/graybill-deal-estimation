# Compact Dirichlet--Feynman reduction for the balanced two-sample certificate

Date: 2026-08-22

**Evidence:** Written integral arguments, directed enclosure inputs, exact
finite certificate checks, and Lean algebra under the specified premises.

This note isolates the two finite analytic tasks needed for the balanced
two-sample certificate at sample sizes `(11,11)`.  It does not use a literature
claim and it does not promote floating-point quadrature to proof.

## 1. Model and risk identity

Let the two independent samples have common mean `mu`, sizes

\[
n_1=n_2=11,
\qquad m_1=m_2=10
\]

residual degrees of freedom, and variances
`sigma_1^2=1`, `sigma_2^2=eta`.  Write

\[
\Delta=\bar X_2-\bar X_1,
\quad S_1\sim\chi^2_{10},
\quad S_2/\eta\sim\chi^2_{10},
\quad V=\operatorname {Var}(\Delta)=\frac{1+\eta}{11}.
\]

These three variables are independent.  A rule with even weight `W` has the
form

\[
\delta_W=\bar X_1+\Delta W(\Delta,S_1,S_2).
\]

Conditioning `\bar X_1` on `Delta` gives the oracle weight

\[
W_o=\frac1{1+\eta}
\]

and, for any two such weights,

\[
R_\eta(\delta_{W_1})-R_\eta(\delta_{W_2})
=E_\eta\!\left[\Delta^2
 \{(W_1-W_o)^2-(W_2-W_o)^2\}\right].                 \tag{1}
\]

The plug-in precision weight is

\[
W_G=\frac{S_1}{S_1+S_2}.                              \tag{2}
\]

We denote the double scale-Haar posterior-mean weight by `W_H` and put

\[
D(\eta)=R_\eta(\delta_{W_G})-R_\eta(\delta_{W_H}).     \tag{3}
\]

## 2. Feynman parameter for the posterior mean

After the two precisions are integrated out, the marginal posterior density
of `mu`, up to a positive data-dependent constant, is

\[
\{S_1+11(\mu-\bar X_1)^2\}^{-11/2}
\{S_2+11(\mu-\bar X_2)^2\}^{-11/2}.                  \tag{4}
\]

For positive `A,B`,

\[
A^{-11/2}B^{-11/2}
=c\int_0^1 [\lambda(1-\lambda)]^{9/2}
 \{(1-\lambda)A+\lambda B\}^{-11}\,d\lambda,        \tag{5}
\]

where the constant `c` cancels from every ratio below.  Completing the square
in `mu` and then integrating `mu` shows that `W_H` is exactly the mean of
`lambda` under the probability density proportional to

\[
[\lambda(1-\lambda)]^{9/2}
\left\{(1-\lambda)S_1+\lambda S_2
      +11\lambda(1-\lambda)\Delta^2\right\}^{-21/2}.
                                                               \tag{6}
\]

Thus a ratio of two compact one-dimensional integrals replaces the original
posterior integration.

## 3. The size-biased Dirichlet identity

For every scale-invariant measurable `f` for which the expectation exists,

\[
E_\eta[\Delta^2 f]=V E^\sharp_\eta[f],                \tag{7}
\]

where size bias changes `Delta^2/V` from `chi^2_1` to `chi^2_3` and leaves
`S_1` and `S_2/eta` unchanged.  Three independent Gamma variables with a
common scale have independent total and proportions.  Consequently, under
`E^sharp`,

\[
(u,v,w):=
\frac{(\Delta^2/V,S_1,S_2/\eta)}
     {\Delta^2/V+S_1+S_2/\eta}
\sim\operatorname {Dirichlet}\!\left(\frac32,5,5\right).       \tag{8}
\]

Its exact density on `u+v+w=1` is

\[
\frac{1527701175}{65536}\,u^{1/2}v^4w^4.             \tag{9}
\]

In these coordinates define

\[
C_\eta(\lambda;u,v,w)
=v(1-\lambda)+\eta w\lambda
 +(1+\eta)u\lambda(1-\lambda),                      \tag{10}
\]

and

\[
H_\eta(u,v,w)
=\frac{\int_0^1 \lambda[\lambda(1-\lambda)]^{9/2}
                    C_\eta(\lambda)^{-21/2}\,d\lambda}
       {\int_0^1 [\lambda(1-\lambda)]^{9/2}
                    C_\eta(\lambda)^{-21/2}\,d\lambda}.       \tag{11}
\]

Equations (6)--(8) give `W_H=H_eta`, while

\[
W_G=\frac{v}{v+\eta w},\qquad W_o=\frac1{1+\eta}.     \tag{12}
\]

Substitution in (1) proves the central compact formula

\[
\boxed{
D(\eta)=\frac{1+\eta}{11}
E_{\operatorname {Dir}(3/2,5,5)}
\left[
 \left(\frac{v}{v+\eta w}-\frac1{1+\eta}\right)^2
 -\left(H_\eta-\frac1{1+\eta}\right)^2
\right].}                                             \tag{13}
\]

There are no location, radial, or scale tails in (13).

A rectangular form follows from

\[
u=t,\qquad v=(1-t)s,\qquad w=(1-t)(1-s),              \tag{14}
\]

where independently

\[
t\sim\operatorname {Beta}(3/2,10),\qquad
s\sim\operatorname {Beta}(5,5).                      \tag{15}
\]

The exact inverse beta normalizations are

\[
B(3/2,10)^{-1}=\frac{4849845}{131072},
\qquad B(5,5)^{-1}=630.                              \tag{16}
\]

Putting `t=y^2` turns the first density into the polynomial density

\[
\frac{4849845}{65536}\,y^2(1-y^2)^9\,dy.             \tag{17}
\]

## 4. Algebraic compact form of the inner ratio

Put

\[
\lambda=\frac{z^2}{z^2+(1-z)^2},
\qquad d=z^2+(1-z)^2,\qquad 0\le z\le1,              \tag{18}
\]

and

\[
P=d\{v(1-z)^2+\eta wz^2\}
  +(1+\eta)uz^2(1-z)^2.                              \tag{19}
\]

Since

\[
d\lambda=\frac{2z(1-z)}{d^2}\,dz,
\qquad C_\eta(\lambda)=\frac{P}{d^2},               \tag{20}
\]

the posterior weight is the entirely algebraic ratio

\[
\boxed{
H_\eta=
\frac{\int_0^1 2z^{12}(1-z)^{10}d^9P^{-21/2}\,dz}
     {\int_0^1 2z^{10}(1-z)^{10}d^{10}P^{-21/2}\,dz}.}          \tag{21}
\]

Only rational operations and square roots occur in the integrands of
(13), (17), and (21).  This is suitable for directed-rounded subdivision.
The apparent singularities occur only on outer boundary strata.  On those
strata `0<=H_eta<=1` supplies a crude bound, while their beta masses (or the
corresponding first moments below) are elementary.  On every trimmed box

\[
y\le1-\epsilon_y,qquad
\epsilon_s\le s\le1-\epsilon_s,qquad
1\le\eta\le50,                                       \tag{22}
\]

`P` has a positive explicit lower bound and direct interval evaluation is
nonsingular.

## 5. A compact wall chart

The far wall can also be made compact rather than controlled by a heuristic
cutoff.  Put

\[
e=\eta^{-1},\qquad
\lambda=\frac{ey}{1+ey},\qquad y\in(0,\infty),        \tag{23}
\]

and

\[
P_e(y)=(v+yw)(1+ey)+(1+e)uy.                         \tag{24}
\]

Direct substitution in (11) gives

\[
\boxed{
\eta H_\eta=
\frac{\int_0^\infty y^{11/2}(1+ey)^9P_e(y)^{-21/2}\,dy}
     {\int_0^\infty y^{9/2}(1+ey)^{10}P_e(y)^{-21/2}\,dy}.}     \tag{25}
\]

At `e=0`, the beta integral is elementary:

\[
(\eta H_\eta)\big|_{e=0}=\frac{11}{8}\frac{v}{1-v}.             \tag{26}
\]

Moreover

\[
\eta W_G=\frac{v}{ev+w},qquad
\eta W_o=\frac1{1+e},                                \tag{27}
\]

so (13) is exactly equivalent to

\[
\boxed{
\eta D(\eta)=\frac{1+e}{11}E_{\rm Dir}
\left[
 \left(\frac{v}{ev+w}-\frac1{1+e}\right)^2
 -\left(\eta H_\eta-\frac1{1+e}\right)^2
\right].}                                             \tag{28}
\]

The right-hand side extends to `e=0`.  For example,

\[
E\left[\left(\frac vw-1\right)^2\right]=1,
\qquad
E\left[\left(\frac{11}{8}\frac v{1-v}-1\right)^2\right]
=\frac{19}{24},                                      \tag{29}
\]

and hence

\[
(\eta D(\eta))\big|_{e=0}=\frac1{11}
\left(1-\frac{19}{24}\right)=\frac5{264}>0.         \tag{30}
\]

The required domination envelope can be written in Dirichlet coordinates as

\[
\eta H_\eta\le
(1+K_a)\frac{v}{1-v}
+K_b^{1/5}\left(\frac vw\right)^{21/10}
             \left(\frac{1-v}{v}\right)^{11/10},     \tag{31}
\]

where

\[
K_a=2^{33/2}3^{11}B(4,13/2),
\qquad K_b=2^7 3^9.                                  \tag{32}
\]

The square of (31) is Dirichlet-integrable: its worst inverse `w` power is
`21/5<5`.  Thus dominated convergence justifies (26)--(30).  For a numerical
certificate, `y=r^2/(1-r)^2` makes (25) an algebraic integral on `0<r<1`.
Consequently the whole wall `eta>=50` is the compact interval
`0<=e<=1/50`; no finite variance-ratio cutoff is logically required.

The exact sample-swap identity

\[
D(\eta)=\eta D(1/\eta)                               \tag{33}
\]

then transfers the same enclosure to the other wall.

### A uniform pointwise wall envelope

The preceding integrable envelope can be sharpened to a simple pointwise
inequality.  This sharpening is useful independently of the numerical wall
replay, so we give the complete argument.

**Pointwise wall-envelope theorem.**  At every interior Dirichlet point and
for every \(\eta>0\),

\[
 \boxed{H_\eta\le\frac32W_G,
 \qquad \eta H_\eta\le\frac32\frac{v}{ev+w}.}       \tag{33a}
\]

Put

\[
 h(\lambda)=\lambda(1-\lambda),\quad
 S=v+\eta w,\quad r=\frac vS,\quad
 L=\frac{(1+\eta)u}{S},\quad
 c_r(\lambda)=r+(1-2r)\lambda .                    \tag{33b}
\]

After the harmless factor \(S^{-21/2}\) is removed, the posterior law in
(11) is

\[
 d\mu_{r,L}(\lambda)
 \ \propto\ h(\lambda)^{9/2}
       \{c_r(\lambda)+Lh(\lambda)\}^{-21/2}\,d\lambda .       \tag{33c}
\]

Let \(T=h/c_r\), and first use the law \(\mu_{r,0}\).  For an interior
value \(t\) of \(T\), its two inverse images \(x<y\) obey

\[
 x+y=1-t(1-2r),\qquad xy=tr,qquad
 c_r(x)c_r(y)=r(1-r).                               \tag{33d}
\]

The quadratic equation
\(\lambda-\lambda^2=t\{r+(1-2r)\lambda\}\) also gives

\[
 |T'(x)|=\frac{y-x}{c_r(x)},\qquad
 |T'(y)|=\frac{y-x}{c_r(y)}.
\]

Consequently the two conditional weights given \(T=t\) are proportional to

\[
 \frac{h(x)^{9/2}c_r(x)^{-21/2}}{|T'(x)|}
 =\frac{t^{9/2}}{y-x}c_r(x)^{-5}
\]

and the analogous expression with \(y\).  The multiplier
\((1+Lt)^{-21/2}\) in (33c) is constant on this two-point fibre.  Thus the
conditional mean \(m_r(t)=E_{r,L}(\lambda\mid T=t)\) is independent of
\(L\).

This conditional mean has an exact monotonicity certificate.  Write

\[
 \tau=\sqrt{\frac r{1-r}},\qquad
 z=\frac{c_r(x)}{\sqrt{r(1-r)}}.
\]

As \(t\) runs from zero to its maximum, \(z\) runs from \(\tau\) to \(1\).
For \(\tau\ne1\), direct substitution in the two weighted atoms gives

\[
 m_\tau(z)=
 \frac{\tau\{\tau z^{10}+\tau-z^9-z\}}
 {(\tau^2-1)(z^2+1)(z^8-z^6+z^4-z^2+1)},           \tag{33e}
\]

and differentiation and collection of powers gives

\[
 \frac{dm_\tau}{dz}=
 \frac{\tau(z^2-1)
 (z^{16}+z^{14}+z^{12}+z^{10}+10z^8+z^6+z^4+z^2+1)}
 {(\tau^2-1)(z^2+1)^2(z^8-z^6+z^4-z^2+1)^2}\ge0.  \tag{33f}
\]

The sign is nonnegative because \(z\) lies between \(\tau\) and \(1\).
It follows that \(m_r(t)\) increases with \(t\) when \(r<1/2\), and
decreases with \(t\) when \(r>1/2\).  The case \(r=1/2\) is symmetric and
has conditional mean \(1/2\).

Increasing \(L\) tilts the pushforward law of \(T\) by
\((1+Lt)^{-21/2}\).  More explicitly, differentiation of the normalized
expectation gives

\[
 \frac{d}{dL}E_{r,L}\lambda
 =-\frac{21}{2}\operatorname {Cov}_{r,L}
 \left(m_r(T),\frac{T}{1+LT}\right).                \tag{33g}
\]

For two monotone real functions \(f,g\), the identity

\[
 2\operatorname {Cov}(f(T),g(T))
 =E[(f(T)-f(T'))(g(T)-g(T'))]
\]

with an independent copy \(T'\) determines the sign of the covariance.
Hence \(E_{r,L}\lambda\) decreases with \(L\) for \(r<1/2\), and increases
with \(L\) for \(r>1/2\).

For completeness, the limit as \(L\to\infty\) is the conditional mean on
the endpoint fibre.  Near zero, the \(T\)-pushforward density under
\(\mu_{r,0}\) is \(t^{9/2}\) times a positive continuous two-branch factor.
Its normalization after multiplication by \((1+Lt)^{-21/2}\) is therefore
of order \(L^{-11/2}\), while every region \(t\ge\delta>0\) contributes
only order \(L^{-21/2}\).  Bounded continuity of \(m_r\) then gives

\[
 \lim_{L\to\infty}E_{r,L}\lambda=m_r(0)
 =\frac{r^5}{r^5+(1-r)^5}.                          \tag{33h}
\]

It remains only to compare the two endpoint cases.  At \(L=0\), integration
of the derivative of
\(h(\lambda)c_r(\lambda)
 h(\lambda)^{9/2}c_r(\lambda)^{-21/2}\) has no boundary term and yields

\[
 (8+6r)E_{r,0}\lambda
 =11r+(6r-3)E_{r,0}\lambda^2.                      \tag{33i}
\]

If \(r\le1/2\), monotonicity and (33i) give
\(E_{r,L}\lambda/r\le11/(8+6r)\le11/8<3/2\).  If
\(1/2\le r\le2/3\), monotonicity and (33h), with
\(q=(1-r)/r\in[1/2,1]\), give

\[
 \frac{E_{r,L}\lambda}{r}
 \le\frac{1+q}{1+q^5}\le\frac32.
\]

The last inequality is equivalent to \(3q^5-2q+1>0\).  With
\(x=8q-4\ge0\), it has the exact positive factorization

\[
 3q^5-2q+1
 =\frac{(x+12)\{3x^4+24x^3+192(x-1)^2+64\}}{32768}>0.
\]

Finally, if \(r\ge2/3\), then
\(E_{r,L}\lambda\le1\le3r/2\).  These three cases prove (33a).

The theorem gives an immediate uniform square-integrability bound.  Since
\(v/(ev+w)\le v/w\) and the Dirichlet ratio moment is

\[
 E\left(\frac vw\right)^2
 =\frac{\Gamma(7)}{\Gamma(5)}
  \frac{\Gamma(3)}{\Gamma(5)}=\frac52,
\]

we have

\[
 \boxed{E(\eta H_\eta)^2\le\frac{45}{8}}.          \tag{33j}
\]

This envelope does not alter the already frozen version-two wall producer or
its hashes.  After that replay exposed excessive low-wall interval
dependency, it was stopped; a separate version-three producer uses the
theorem as its endpoint majorant.

There is also a fully explicit complex-shift version.  Compactify the wall
variable by \(y=\ell/m\), where \(m=1-\ell\), and use the outer logits
\(A=e^a\), \(B=e^b\).  After factors independent of \(\ell\) are removed
from the numerator and denominator of (25), the only outer-dependent
polynomial is

\[
 \widetilde P_e(\ell;a,b)
 =(Bm+\ell)(m+e\ell)+(1+e)A(1+B)\ell m.             \tag{33k}
\]

Under the shifts \(a\mapsto a+i\alpha\),
\(b\mapsto b+i\beta\), its four positive summands have phases
\(\beta,0,\alpha,\alpha+\beta\).  They lie in a common arc of width at most
\(s=|\alpha|+|\beta|\).  Therefore, for \(s<\pi\), rotation to the midpoint
of that arc gives

\[
 \cos(s/2)\widetilde P_e(\ell;a,b)
 \le |\widetilde P_e(\ell;a+i\alpha,b+i\beta)|
 \le \widetilde P_e(\ell;a,b).                     \tag{33l}
\]

Let \(p=21/2\).  If \(ps<\pi\), all denominator integrands with the power
\(\widetilde P_e^{-p}\) themselves lie in an arc of width at most \(ps\).
Consequently the modulus of their integral is at least
\(\cos(ps/2)\) times the integral of their moduli.  The numerator has the
same weight multiplied by the positive real factor
\(\ell/(m+e\ell)\).  Applying both sides of (33l) separately to the two
integrals proves

\[
 \boxed{
 |\overline H_e(a+i\alpha,b+i\beta)|
 \le \sec(s/2)^p\sec(ps/2)\overline H_e(a,b)
 \le\frac32\sec(s/2)^p\sec(ps/2)e^b,}               \tag{33m}
\]

where \(\overline H_e=\eta H_\eta\).  Thus the complex endpoint majorant
uses only the second beta-logit moment \(E(e^{2b})=5/2\).

## 6. Exact charge-vector formulas

For `a=0,...,4`, define

\[
p_a(h)=h^{a+1}(1-h),
\qquad
F^\star=\frac{110\Delta^2}{S_1+S_2}.
\]

Under the size-biased law,

\[
F^\star=\frac{10(1+\eta)u}{v+\eta w}.                \tag{34}
\]

Order the ten correction symbols by

\[
F_{a,1}=p_a(H_\eta)F^\star,
\qquad
F_{a,0}=-p_a(H_\eta),qquad a=0,\ldots,4.            \tag{35}
\]

Their first-order charge vector `G(eta) in R^10` is exactly

\[
\boxed{
\begin{aligned}
G_{a,1}(\eta)
 &=\frac{1+\eta}{11}E_{\rm Dir}
   [(H_\eta-W_o)p_a(H_\eta)F^\star],\\
G_{a,0}(\eta)
 &=-\frac{1+\eta}{11}E_{\rm Dir}
   [(H_\eta-W_o)p_a(H_\eta)].
\end{aligned}}                                       \tag{36}
\]

Thus the risk gap and all ten degree-six charge coordinates use the same
compact integration engine.

## 7. Why eleven exact vectors close the degree-six question

Let `M(eta)` be the Gram matrix

\[
M_{jk}(\eta)=E_\eta[\Delta^2F_jF_k].                 \tag{37}
\]

It is positive semidefinite.  For a coefficient vector `c`, the exact risk
increment is

\[
R_\eta(\delta_H+\Delta c\!\cdot\!F)-R_\eta(\delta_H)
=2c\cdot G(\eta)+c^TM(\eta)c.                        \tag{38}
\]

In fact `M(eta)` is positive definite in this ten-dimensional class.  To see
this, write a linear combination of (35) as

\[
A(H_\eta)F^\star-B(H_\eta),                          \tag{38a}
\]

where `A` and `B` are each `h(1-h)` times a polynomial of degree at most four.
Near the face `u=0`, use `u` and
`r=eta*w/v` as local coordinates.  On the face, `F^star=0` and `H_eta=q(r)`,
where `q(r)` is the mean of `lambda` under density proportional to

\[
[\lambda(1-\lambda)]^{9/2}[1+(r-1)\lambda]^{-21/2}.
\]

Differentiation gives

\[
q'(r)=-\frac{21}{2}\operatorname {Cov}_r
\left(\lambda,\frac{\lambda}{1+(r-1)\lambda}\right)<0,             \tag{38b}
\]

because both displayed functions are strictly increasing on `(0,1)`.  Also
`partial F^star/partial u>0` at `u=0`.  The map
`(u,r) -> (H_eta,F^star)` therefore has nonzero Jacobian at every such regular
face point and its interior image contains an open set.  If (38a) vanished
almost surely, it would vanish on that open set.  Varying `F^star` first gives
`A=0`, then `B=0`; linear independence of
`h(1-h),...,h^5(1-h)` gives `c=0`.  This proves positive definiteness.

Suppose there are positive numbers `alpha_i` and positive ratios `eta_i` such
that

\[
\sum_i\alpha_iG(\eta_i)=0.                           \tag{39}
\]

Multiplying (38) by `alpha_i` and summing gives

\[
\sum_i\alpha_i\{R_{\eta_i}(\delta_H+\Delta c\cdot F)
                     -R_{\eta_i}(\delta_H)\}
=c^T\left(\sum_i\alpha_iM(\eta_i)\right)c\ge0.       \tag{40}
\]

Therefore no correction in the ten-dimensional class can have a strictly
negative increment at every `eta_i`, hence not at every positive `eta`.
The positive definiteness just proved makes the right side of (40) strictly
positive for every `c!=0`.  Hence (39) also excludes weak domination with
strict improvement elsewhere: nonpositive increments at all positive `eta`
would in particular make the left side of (40) nonpositive, a contradiction.

For certification it is convenient to normalize

\[
h_i=G(\eta_i)/\|G(\eta_i)\|_2.                       \tag{41}
\]

Let `A` be the `11 by 11` matrix whose first ten rows are the columns `h_i`
and whose last row is all ones.  If

\[
Aw=(0,\ldots,0,1)^T,qquad w_i>0,                    \tag{42}
\]

then (39) holds with positive coefficients proportional to
`w_i/||G(eta_i)||_2`.

The following elementary perturbation test is sufficient for an interval
certificate.  Given a numerical center `A_0`, put

\[
w_0=A_0^{-1}e_{11},\qquad
q=\|A_0^{-1}\|_\infty\,\|A-A_0\|_\infty.
\]

If `q<1` and

\[
\frac{q}{1-q}\|w_0\|_\infty<\min_i(w_0)_i,          \tag{43}
\]

then `A` is invertible and the exact solution in (42) is componentwise
positive.  This is the Neumann-series bound applied to
`A=A_0(I+A_0^{-1}(A-A_0))`.

## 8. Exact swap-parity reduction from ten dimensions to four

The sample-swap symmetry reduces the finite certificate much further.  Replace
the pure tower by its rational parity basis

\[
q_k(h)=h(1-h)(h-\tfrac12)^k,\qquad k=0,\ldots,4.       \tag{44}
\]

This is an invertible triangular change of basis from
`p_0,...,p_4`.  For each `k`, use the two features `q_k(H_eta)F^star` and
`-q_k(H_eta)`, and denote either corresponding charge by `G_{k,j}(eta)`.
The exact identities

\[
H_{1/\eta}(u,w,v)=1-H_\eta(u,v,w),\qquad
F^\star_{1/\eta}(u,w,v)=F^\star_\eta(u,v,w)           \tag{45}
\]

follow from `lambda -> 1-lambda` in (11).  The Dirichlet law is invariant under
`v <-> w`, while the prefactor `(1+eta)/11` changes by `1/eta`.  Therefore

\[
\boxed{G_{k,j}(\eta)=-(-1)^k\eta G_{k,j}(1/\eta).}    \tag{46}
\]

Fix ratios `eta_i>1` and positive numbers `alpha_i`.  Give the atom at `eta_i`
mass `alpha_i` and its reciprocal atom mass `alpha_i eta_i`.  Equation (46)
shows that every even-`k` coordinate cancels exactly, while every odd-`k`
coordinate is twice its charge at `eta_i`.  Hence the full ten-dimensional
balance (39) is equivalent to only the four equations

\[
\sum_i\alpha_i
\begin{pmatrix}
G_{1,1}(\eta_i)\\G_{1,0}(\eta_i)\\
G_{3,1}(\eta_i)\\G_{3,0}(\eta_i)
\end{pmatrix}=0.                                    \tag{47}
\]

Thus five positive reduced vectors can produce a ten-atom full certificate.
The reduction itself is exact and does not depend on numerical quadrature.

## 9. The certified five-pair simplex and its exact trust chain

The discovery support has been replaced by the following frozen exact support:

\[
 \boxed{\left(\frac{11}{10},2,\frac{11}{2},18,145\right).}     \tag{48}
\]

Together with the reciprocal atoms and the reciprocal masses prescribed after
(46), these five ratios give ten atoms.  Write \(g_i\in\mathbb R^4\) for the
odd charge vector in (47), in the displayed coordinate order.  The certified
preconditioner is

\[
 R=\operatorname {diag}\left(\frac17,\frac47,\frac74,7\right),
 \qquad h_i=\frac{Rg_i}{\|Rg_i\|_2}.                 \tag{49}
\]

Both operations preserve positive balance: \(R\) is invertible, and a
positive balance of the \(h_i\) becomes one of the \(g_i\) after dividing the
\(i\)-th coefficient by \(\|Rg_i\|_2\).  The directed-rounded column balls and
the exact rational perturbation checker give center weights

\[
 w_0\approx
 (0.1931856086,0.2454834401,0.1752317233,
  0.1708813402,0.2152178879).                        \tag{50}
\]

For the \(5\) by \(5\) augmented matrix, the componentwise Neumann ledger is

\[
\begin{aligned}
 q&=\bigl\|\,|A_0^{-1}|\,R_A\bigr\|_\infty
       <1.597\mathbin{\cdot}10^{-4},\\
 \|A_0^{-1}\|_\infty&<89.455,
 &\|R_A\|_\infty&<2.132\mathbin{\cdot}10^{-6},\\
 \|w-w_0\|_\infty&<3.920\mathbin{\cdot}10^{-5},
 &\min_i w_i&>0.170842.                              \tag{51}
\end{aligned}
\]

Here \(R_A\) is the componentwise radius matrix, not the row preconditioner
\(R\).  The first line is the sharper componentwise version of (43): from
\(|A-A_0|\le R_A\), one has
\(\|A_0^{-1}(A-A_0)\|_\infty\le q\).  Thus every matrix in the interval box is
invertible and its augmented solution is strictly positive.  It follows
exactly that positive \(\alpha_i\) exist in (47), and then (46) gives the full
ten-coordinate balance (39).

The certificate has four deliberately separated layers.

1. `../certificates/Certificate0003/Script0002.py` evaluates the four raw charges at (48).
   Every sampled exponential and every transcendental error constant is
   enclosed by Arb; sampled algebra and finite sums use outward IEEE binary64
   intervals; (70), (74), (79), and (87)--(90) bound all infinite lattices.
   The five supplied enclosure files retain the accepted interval payloads
   and explicitly record that the renamed evaluator did not regenerate them.
   Newly generated outputs instead bind the evaluator that produced them.
2. `../certificates/Certificate0003/Script0003.py` verifies the current retained-input identities
   or, for freshly generated inputs, their actual producer hashes. It applies
   (49) with interval arithmetic and serializes every binary64 endpoint by its
   exact integer ratio.  Decimal text is never silently reinterpreted as a
   nearby exact rational.
3. `../certificates/Certificate0003/Script0004.py` parses those rational endpoints and
   performs inversion, the componentwise Neumann bound, and the positivity
   test using only exact `Fraction` arithmetic.  Its replay ends with
   `FINITE_INTERVAL_SIMPLEX_CERTIFIED`.
4. `GD/Module0185.lean` kernel-checks the swap parity, the lift from
   four odd equations to all ten equations, and the positive reciprocal-pair
   construction.  The analytic implication from positive charge balance to
   non-improvability is the positive-definite identity (38)--(40).

The [input manifest](../certificates/Certificate0003/Inputs.json) identifies
current retained datasets and checking sources. The [finite-suite record](../certificates/verification/result.json)
records fresh normalization and exact finite checks of those inputs. The
[numerical evidence guide](../certificates/README.md) describes the retained-input
and fresh-producer modes. These identity checks supplement the mathematical
bounds above; they do not claim regeneration of the directed enclosures.

## 10. Exact collar budget for a directed-rounded implementation

The compact chart permits a particularly simple fail-closed collar removal.
In (14), let

\[
E_{\tau,\delta}=\{t\le1-\tau,\ \delta\le s\le1-\delta\}.
\]

Since the two beta variables are independent,

\[
\begin{aligned}
P(s\notin[\delta,1-\delta])
 &\le252\delta^5,\\
P(t>1-\tau)
 &\le \frac{4849845}{1310720}\tau^{10},              \tag{52}\\
E\!\left[\frac{t}{1-t}\mathbf1_{\{t>1-\tau\}}\right]
 &\le \frac{4849845}{1179648}\tau^9,\\
E\!\left[\frac{t}{1-t}\right]&=\frac16.
\end{aligned}
\]

The first two lines and `|square-square|<=1` bound the discarded contribution
to (13) by

\[
\frac{1+\eta}{11}
\left(252\delta^5+\frac{4849845}{1310720}\tau^{10}\right).       \tag{53}
\]

For the charge coordinates, `|H_eta-W_o|<=1`, `p_a<=1/4`, and

\[
F^\star\le
\frac{10(1+\eta)}{\min(1,\eta)}\frac{t}{1-t}.         \tag{54}
\]

Thus (52) also gives explicit discarded-charge bounds, without evaluating
`H_eta` on a boundary stratum.  For example, `tau=1/50` and
`delta=1/1500` make the collar contribution to every `F^star` charge below
\(6.5\mathbin{\cdot}10^{-11}\) throughout the reciprocal-pair atom range
\(14/2685\le\eta\le2685/14\).

On the retained box, (19) satisfies

\[
P\ge \frac{\tau\delta\min(1,\eta)}4>0.                \tag{55}
\]

because \(d\ge1/2\), \(v\ge(1-t)\delta\), and
\(\eta w\ge\eta(1-t)\delta\).  Equations (52)--(55) reduce the remaining work to
ordinary directed-rounded integration on a nonsingular compact cube.  They
are proof bounds, but no claim is made here that the required subdivision has
already been run.

## 11. A uniform analytic strip and a finite interpolation theorem

The logit chart gives a second way to avoid interval propagation in the
variance-ratio direction.  Put

\[
x=\log\eta,\qquad
a=\log\frac{u}{v+w},\qquad b=\log\frac vw.             \tag{56}
\]

The variables \(a\) and \(b\) are independent, with probability densities

\[
\frac{e^{3a/2}}{B(3/2,10)(1+e^a)^{23/2}},
\qquad
\frac{e^{5b}}{B(5,5)(1+e^b)^{10}},                   \tag{57}
\]

respectively.  After a harmless positive factor is removed from (10), the
inner kernel is

\[
\widetilde C_x(\lambda)
=e^b(1-\lambda)+e^x\lambda
+e^a(1+e^b)(1+e^x)\lambda(1-\lambda).                \tag{58}
\]

Equivalently,

\[
\widetilde C_x(\lambda)=A(\lambda)+e^xB(\lambda),
\quad
A=(1-\lambda)(e^b+e^a(1+e^b)\lambda),
\quad
B=\lambda(1+e^a(1+e^b)(1-\lambda)),                  \tag{59}
\]

where \(A,B>0\) on \(0<\lambda<1\).

Let \(p=21/2\).  If \(z=x+iy\) and \(|y|<\pi\), the argument of
\(A+e^zB\) lies between \(0\) and \(y\) (with the order reversed when
\(y<0\)).  Consequently all values of

\[
[\lambda(1-\lambda)]^{9/2}(A+e^zB)^{-p}
\]

lie in a sector of angular width \(p|y|\).  When
\(|y|<\pi/p=2\pi/21\), their integral cannot vanish.  The quotient (11)
therefore has a holomorphic continuation to that strip, and the same sector
argument gives

\[
|H_z(a,b)|\le\sec\frac{p|y|}{2}.                     \tag{60}
\]

The elementary weights

\[
G_z=\frac{e^b}{e^b+e^z},\qquad O_z=\frac1{1+e^z}
\]

satisfy

\[
|G_z|,\ |O_z|\le\sec\frac{|y|}{2}.                   \tag{61}
\]

Define the risk gap with its positive scale factor removed:

\[
\mathcal J(x)=\frac{11D(e^x)}{1+e^x}
=E\{(G_x-O_x)^2-(H_x-O_x)^2\}.                       \tag{62}
\]

The bounds (60)--(61) are uniform in \(a,b\), so dominated holomorphic
integration proves that \(\mathcal J\) is holomorphic on
\(|\operatorname {Im}x|<2\pi/21\).  Moreover, on every closed disk
\(|z-x|\le1/7\) centered at a real \(x\),

\[
|\mathcal J(z)|<11.                                  \tag{63}
\]

Indeed, on that disk

\[
\sec(|\operatorname {Im}z|/2)<\frac{101}{100},
\qquad
\sec(p|\operatorname {Im}z|/2)<\frac32,
\]

using \(\cos r\ge1-r^2/2\); hence

\[
|\mathcal J(z)|
\le4(101/100)^2+(3/2+101/100)^2<11.
\]

Cauchy's estimate now gives the global, completely explicit derivative bound

\[
\boxed{
|\mathcal J^{(n)}(x)|\le 11\,n!\,7^n
\quad(x\in\mathbb R,\ n\ge0).}                       \tag{64}
\]

There are two additional exact structural facts.  Sample swap gives

\[
\mathcal J(-x)=\mathcal J(x),                         \tag{65}
\]

so only \(x\ge0\) needs certification.  Also \(H_x\) is strictly decreasing
in \(x\).  To prove the latter, under the posterior law in (11) put

\[
r_x(\lambda)=\frac{e^xB(\lambda)}
                   {A(\lambda)+e^xB(\lambda)}.
\]

Differentiation under the compact integral gives

\[
\frac{\partial H_x}{\partial x}
=-p\,\operatorname {Cov}_x(\lambda,r_x(\lambda)).    \tag{66}
\]

The ratio \(B/A\) is strictly increasing because it is unchanged by the
common logit normalization, and in the original simplex coordinates
\(A_0=(1-\lambda)(v+u\lambda)\),
\(B_0=\lambda(w+u(1-\lambda))\),

\[
B_0'A_0-B_0A_0'
=uv(1-\lambda)^2+uw\lambda^2+vw>0.                  \tag{67}
\]

Thus the covariance in (66) is strictly positive.

Finally, (64) supplies a finite pointwise-to-continuum compiler.  On an
interval \([c-h,c+h]\), let \(P_n\) interpolate \(\mathcal J\) at the
\(n+1\) Chebyshev roots.  The real interpolation remainder and the monic
Chebyshev identity imply

\[
\boxed{
\|\mathcal J-P_n\|_{\infty,[c-h,c+h]}
\le 22\left(\frac{7h}{2}\right)^{n+1}.}              \tag{68}
\]

For example, \(h=1/14\) and \(n=13\) give an absolute remainder below
\(8.20\mathbin{\cdot}10^{-8}\).  Twenty-eight such blocks cover
\(0\le x\le\log 50\).  Thus the continuum part can be certified by
directed-rounded point evaluations, followed by a rigorous polynomial-minimum
calculation, rather than by propagating one wide \(\eta\) interval through
the three nested integrals.

Equations (56)--(68) are analytic theorems, not numerical evidence.  They do
not alone prove positivity: the interpolating polynomials and their input
enclosures still have to be certified.  No zero-count or
variation-diminishing assertion is used.

## 12. A fail-closed sinc enclosure for every point evaluation

The compact algebraic formula is useful for interval subdivision, but there
is a substantially cheaper rigorous point evaluator.  The following
elementary strip estimate makes the infinite trapezoidal rule into a relative
enclosure whenever the real integrand is positive.

Let \(f\) be holomorphic on \(|\operatorname {Im}z|<d\), continuous on the
closed strip after an arbitrarily small inward displacement, integrable on
both boundary lines, and uniformly tending to zero at the two horizontal
ends.  If

\[
 I=\int_{-\infty}^{\infty}f(c)\,dc,
 \qquad T_h=h\sum_{k\in\mathbb Z}f(c_0+kh),           \tag{69}
\]

then direct integration around the two horizontal sides of a large
rectangle, using the kernels
\((1-e^{-2\pi i(z-c_0)/h})^{-1}\) and
\((1-e^{2\pi i(z-c_0)/h})^{-1}\), gives

\[
 |I-T_h|\le
 \frac{\int_{\mathbb R}|f(c+id)|\,dc
       +\int_{\mathbb R}|f(c-id)|\,dc}
      {e^{2\pi d/h}-1}.                              \tag{70}
\]

The vertical sides vanish by uniform decay.  An inward limit gives the result
when a bound was first proved only on narrower strips.  This is also a proof
of (70), rather than an appeal to a quadrature asymptotic.

For the inner posterior integral put
\(c=\log(\lambda/(1-\lambda))\), \(p=21/2\), and

\[
\begin{aligned}
 L&=e^b+e^x+e^a(1+e^b)(1+e^x),\\
 Q(c)&=e^b+Le^c+e^xe^{2c},\\
 f_0(c)&=e^{11c/2}(1+e^c)^{10}Q(c)^{-p},\\
 f_1(c)&=e^{13c/2}(1+e^c)^9Q(c)^{-p}.               \tag{71}
\end{aligned}
\]

Then \(H_{e^x}=I_1/I_0\), where \(I_j=\int f_j\).  If
\(z=c+i\theta\), multiplication of \(Q(z)\) by \(e^{-i\theta}\) gives

\[
 \operatorname {Re}\{e^{-i\theta}Q(c+i\theta)\}
 \ge \cos(\theta)Q(c).                              \tag{72}
\]

Thus \(Q\) has no zero in \(|\operatorname {Im}c|<\pi/2\), the indicated
branch of \(Q^{-p}\) is holomorphic there, and, for \(j=0,1\),

\[
 |f_j(c+i\theta)|\le \sec(\theta)^p f_j(c).          \tag{73}
\]

Notice that the numerator needs no additional secant factor: writing it as
the last line of (71), rather than as a complex logistic factor times
\(f_0\), retains the cancellation.  Equations (70)--(73) prove the relative
bound

\[
 |I_j-T_{j,h}|\le\epsilon(d,h)I_j,
 \qquad
 \epsilon(d,h)=
 \frac{2\sec(d)^{21/2}}{e^{2\pi d/h}-1}.             \tag{74}
\]

The finite-sum tails are geometric and require no numerical limit argument.
Suppose \(c_L\) is the largest omitted lattice point on the left and \(c_R\)
the smallest omitted lattice point on the right.  The omitted parts of the
positive trapezoidal sums are at most

\[
\begin{aligned}
 \tau_{0,L}&=
 \frac{h e^{-21b/2}(1+e^{c_L})^{10}e^{11c_L/2}}
      {1-e^{-11h/2}},\\
 \tau_{1,L}&=
 \frac{h e^{-21b/2}(1+e^{c_L})^9e^{13c_L/2}}
      {1-e^{-13h/2}},\\
 \tau_{0,R}&=
 \frac{h e^{-21x/2}(1+e^{-c_R})^{10}e^{-11c_R/2}}
      {1-e^{-11h/2}},\\
 \tau_{1,R}&=
 \frac{h e^{-21x/2}(1+e^{-c_R})^9e^{-11c_R/2}}
      {1-e^{-11h/2}}.                                \tag{75}
\end{aligned}
\]

For example, the first inequality follows from \(Q\ge e^b\), monotonicity
of \(1+e^c\) on the omitted left lattice, and summation of
\(e^{11c/2}\).  On the right use \(Q\ge e^xe^{2c}\) and
\(1+e^c\le(1+e^{-c_R})e^c\).  The other two lines are identical.

If directed rounding encloses a truncated sum by
\(S_j\in[S_j^-,S_j^+]\), (74)--(75) give

\[
 I_j\in
 \left[
 \frac{S_j^-}{1+\epsilon},
 \frac{S_j^++\tau_{j,L}+\tau_{j,R}}{1-\epsilon}
 \right],                                           \tag{76}
\]

and interval division, intersected with \(0\le H\le1\), encloses the inner
posterior mean.  With

\[
 d=\frac7{50},\qquad h=\frac1{40},                  \tag{77}
\]

the exact expression in (74) is less than
\(1.17\mathbin{\cdot}10^{-15}\).  This error is relative to each positive
inner integral; only the explicit tails in (75) need be driven below the
desired interval width.

There is a similarly cheap two-dimensional outer enclosure.  For a function
\(F(a,b)\), let \(T_h^{(2)}F\) be its infinite tensor trapezoidal sum with
arbitrary real lattice offsets.  Suppose \(F\) is holomorphic on the axis
strips of height \(d_0\) and on the four polystrips
\((\operatorname {Im}a,\operatorname {Im}b)=(\pm d_1,\pm d_1)\).  Define

\[
\begin{aligned}
 M_a&=\max_{\sigma=\pm1}\iint
       |F(a+i\sigma d_0,b)|\,da\,db,\\
 M_b&=\max_{\sigma=\pm1}\iint
       |F(a,b+i\sigma d_0)|\,da\,db,\\
 M_{ab}&=\max_{\sigma,\tau=\pm1}\iint
       |F(a+i\sigma d_1,b+i\tau d_1)|\,da\,db.
                                                               \tag{78}
\end{aligned}
\]

Expanding the periodized lattice sum into its Fourier modes and moving the
contour for each nonzero frequency in the decaying direction proves

\[
\boxed{
 \left|\iint F-T_h^{(2)}F\right|
 \le
 \frac{2M_a+2M_b}{e^{2\pi d_0/h}-1}
 +\frac{4M_{ab}}{(e^{2\pi d_1/h}-1)^2}.}             \tag{79}
\]

Indeed, the two axis families are geometric series in one nonzero Fourier
index, while the four mixed quadrants are products of two geometric series.
This derivation also proves (79) directly under the exponential tails below;
no unquantified use of a Poisson limit is required.

All constants in (78) are explicit here.  If \(a,b\) are displaced by
\(i\alpha,i\beta\), the four positive terms of (58) have phases

\[
 0,\quad\beta,\quad\alpha,\quad\alpha+\beta.
\]

Their phase width is at most \(s=|\alpha|+|\beta|\).  Hence, provided
\(ps<\pi\),

\[
 |H_x(a+i\alpha,b+i\beta)|
 \le K(s):=\sec\frac{ps}{2}.                        \tag{80}
\]

The density and elementary-factor bounds are

\[
\begin{aligned}
 |\rho_a(a+i\alpha)|
 &\le \sec(\alpha/2)^{23/2}\rho_a(a),\\
 |\rho_b(b+i\beta)|
 &\le \sec(\beta/2)^{10}\rho_b(b),\\
 |G_x(b+i\beta)|&\le\sec(\beta/2),\\
 |F^\star_x(a+i\alpha,b+i\beta)|
 &\le\sec(\beta/2)F^\star_x(a,b),                  \tag{81}
\end{aligned}
\]

where

\[
 F^\star_x(a,b)=
 10(1+e^x)e^a\frac{1+e^b}{e^b+e^x}.                \tag{82}
\]

Consequently, for the normalized-risk integrand in (62), a valid boundary
majorant is

\[
 \sec(\alpha/2)^{23/2}\sec(\beta/2)^{10}
 \left[
   \{\sec(\beta/2)+1\}^2+\{K(s)+1\}^2
 \right].                                           \tag{83}
\]

For an odd parity charge \(k\in\{1,3\}\), put

\[
 Q_k(K)=K(1+K)(K+\tfrac12)^k.                       \tag{84}
\]

When \(\eta=e^x\ge1\), valid majorants for the non-\(F^\star\) and
\(F^\star\) charge integrands, respectively, are

\[
\begin{aligned}
 M_{k,0}(\alpha,\beta)
 &=\frac{1+\eta}{11}(K(s)+1)Q_k(K(s))
   \sec(\alpha/2)^{23/2}\sec(\beta/2)^{10},\\
 M_{k,1}(\alpha,\beta)
 &=M_{k,0}(\alpha,\beta)\sec(\beta/2)
   \frac53(1+\eta).                                 \tag{85}
\end{aligned}
\]

For the second line use
\((1+e^b)/(e^b+\eta)\le1\) and the exact moment
\(\int e^a\rho_a(a)\,da=1/6\).

Take

\[
 d_0=\frac7{50},\qquad d_1=\frac7{100},
 \qquad h=\frac1{40}.                               \tag{86}
\]

The three values of (83) are below \(9.79\).  Thus replacing them by \(12\)
in (79) gives an absolute discretization error below
\(5.03\mathbin{\cdot}10^{-14}\) for every point value of
\(\mathcal J(x)\).  On \(1\le\eta\le2685/14\), all the values in (85) are
below \(2.72\mathbin{\cdot}10^5\).  Replacing them by
\(3\mathbin{\cdot}10^5\) gives an absolute discretization error below
\(1.26\mathbin{\cdot}10^{-9}\) for each of the four reduced raw charges.
The displayed decimal bounds are consequences of the explicit elementary
expressions (79), (83), and (85), and can themselves be outward-rounded.

For completeness, outer lattice truncation is also elementary.  Write
\(C_a=B(3/2,10)^{-1}\).  If \(A_L,A_R,B_L,B_R\) are the nearest omitted
outer lattice points, the marginal omitted masses are bounded by

\[
\begin{aligned}
 A_L^{(0)}&=\frac{hC_ae^{3A_L/2}}{1-e^{-3h/2}},&
 A_R^{(0)}&=\frac{hC_ae^{-10A_R}}{1-e^{-10h}},\\
 B_L^{(0)}&=\frac{630h e^{5B_L}}{1-e^{-5h}},&
 B_R^{(0)}&=\frac{630h e^{-5B_R}}{1-e^{-5h}},\\
 A_L^{(1)}&=\frac{hC_ae^{5A_L/2}}{1-e^{-5h/2}},&
 A_R^{(1)}&=\frac{hC_ae^{-9A_R}}{1-e^{-9h}}.         \tag{87}
\end{aligned}
\]

The superscript \(1\) denotes the density weighted by \(e^a\).  Let
\(A^{(r)}=A_L^{(r)}+A_R^{(r)}\) and
\(B^{(0)}=B_L^{(0)}+B_R^{(0)}\).  Applying (70) to the two marginal
densities bounds their full infinite lattice masses by \(1+\epsilon_a\) and
\(1+\epsilon_b\), and bounds the \(e^a\rho_a\) lattice mass by
\((1+\epsilon_a)/6\), with the corresponding secant factors in
\(\epsilon_a,\epsilon_b\).  Since the absolute real risk integrand is at most
one, its omitted rectangular-lattice contribution is at most

\[
 A^{(0)}(1+\epsilon_b)+(1+\epsilon_a)B^{(0)}.        \tag{88}
\]

For \(k=1,3\), set
\(\bar q_k=2^{-(k+2)}\).  The omitted non-\(F^\star\) charge is at most

\[
 \frac{1+\eta}{11}\bar q_k
 \{A^{(0)}(1+\epsilon_b)+(1+\epsilon_a)B^{(0)}\},   \tag{89}
\]

and the omitted \(F^\star\) charge is at most

\[
 \frac{10(1+\eta)^2}{11}\bar q_k
 \left\{A^{(1)}(1+\epsilon_b)
       +\frac{1+\epsilon_a}{6}B^{(0)}\right\}.       \tag{90}
\]

Equations (74)--(90) are a complete fail-closed point-evaluation compiler:
every infinite-grid discretization error, every lattice tail, and every inner
ratio is enclosed by an explicit formula.  Node values still have to be
evaluated with directed rounding, but no empirical convergence comparison is
used.  In particular, the analytic quadrature budget is far below both the
\(10^{-7}\) normalized-risk target suggested by (68) and the reduced-simplex
charge tolerance (51).

## 13. Exact wall tangent and a raw-moment curvature recurrence

The first two wall coefficients admit a short derivation entirely inside the
compact Dirichlet chart.  This both removes reliance on a formal asymptotic
expansion and gives stable quantities for a convexity certificate.

Retain \(e=\eta^{-1}\), and write
\(\overline H_e=\eta H_\eta\).  Conditional on \(u,v,w\), let
\(\mathbb E_e^\circ\) denote expectation under the probability density on
\(y>0\) proportional to

\[
 y^{9/2}(1+ey)^{10}P_e(y)^{-21/2},
 \qquad
 P_e(y)=(v+yw)(1+ey)+(1+e)uy.                       \tag{91}
\]

Thus

\[
 \overline H_e=\mathbb E_e^\circ
 \left[\frac{y}{1+ey}\right].                       \tag{92}
\]

At \(e=0\), put

\[
 a=\frac{v}{1-v},\qquad c=\frac{w}{1-v}.
\]

The variable \(t=y/a\) under \(\mathbb E_0^\circ\) has density

\[
 \frac{t^{11/2-1}(1+t)^{-21/2}}{B(11/2,5)}.
                                                               \tag{93}
\]

In particular,

\[
\begin{aligned}
 \mathbb E_0^\circ y&=\frac{11}{8}a,&
 \mathbb E_0^\circ y^2&=\frac{143}{48}a^2,&
 \operatorname {Var}_0^\circ(y)&=\frac{209}{192}a^2.            \tag{94}
\end{aligned}
\]

To differentiate (92), note that

\[
 \left.\frac{\partial}{\partial e}\frac{y}{1+ey}\right|_{e=0}
 =-y^2
\]

and that the uncentered logarithmic score of (91) at zero is

\[
 S_0(y)=10y-\frac{21}{2}r(y),\qquad
 r(y)=\frac{y\{1+a-c+cy\}}{a+y}.                    \tag{95}
\]

The useful division

\[
 r(y)=cy+(1+a)(1-c)\frac{y}{a+y}                    \tag{96}
\]

reduces every covariance to beta-prime moments.  Indeed,

\[
 \mathbb E_0^\circ\frac{y}{a+y}=\frac{11}{21},
 \qquad
 \operatorname {Cov}_0^\circ
 \left(y,\frac{y}{a+y}\right)=\frac{11}{84}a.       \tag{97}
\]

Differentiating a normalized expectation gives
\((\mathbb E_e^\circ f)'=\mathbb E_e^\circ f'
+\operatorname {Cov}_e^\circ(f,S_e)\).  Equations (94)--(97)
therefore give the exact pointwise derivative

\[
\boxed{
 \overline H'_0
 =-\frac{11}{128}a
 \{117ac-76a-16c+16\}.}                             \tag{98}
\]

Now average over the outer Dirichlet law.  The variables

\[
 v\sim\operatorname {Beta}(5,13/2),
 \qquad c=\frac{w}{u+w}\sim\operatorname {Beta}(5,3/2)
\]

are independent.  Hence

\[
 \mathbb E a=\frac{10}{11},\qquad
 \mathbb E a^2=\frac{40}{33},\qquad
 \mathbb E a^3=\frac{80}{33},\qquad
 \mathbb E c=\frac{10}{13}.                         \tag{99}
\]

Let

\[
\begin{aligned}
 G_e&=\frac{v}{ev+w},&
 O_e&=\frac1{1+e},\\
 \Phi(e)&=\mathbb E(G_e-O_e)^2,&
 \Theta(e)&=\mathbb E(\overline H_e-O_e)^2.
\end{aligned}                                       \tag{100}
\]

At zero, \(v/w\) has beta-prime parameters \((5,5)\), whose first
three moments are \(5/4,5/2,35/4\).  Therefore

\[
 \Phi(0)=1,\qquad \Phi'(0)
 =2\mathbb E\left[
 \left(\frac vw-1\right)
 \left\{1-\left(\frac vw\right)^2\right\}\right]
 =-12.                                               \tag{101}
\]

Equations (98)--(99), by direct rational substitution, give

\[
\begin{aligned}
 \Theta(0)
 &=\mathbb E\left(\frac{11}{8}a-1\right)^2
 =\frac{19}{24},\\
 \frac12\Theta'(0)
 &=\mathbb E\left[
 \left(\frac{11}{8}a-1\right)
 \{\overline H'_0+1\}\right]
 =-\frac{3173}{1248}.                               \tag{102}
\end{aligned}
\]

For audit purposes, the second expectation uses only the polynomial

\[
 \left(\frac{11}{8}a-1\right)\{\overline H'_0+1\}
 =-\frac{14157}{1024}a^3c+\frac{2299}{256}a^3
  +\frac{1529}{128}a^2c-\frac{539}{64}a^2
  -\frac{11}{8}ac+\frac{11}{4}a-1,
\]

followed by (99).

The wall-scaled risk gap is

\[
 K(e):=\eta D(\eta)
 =\frac{1+e}{11}\{\Phi(e)-\Theta(e)\}.               \tag{103}
\]

Consequently (101)--(102) prove, with no numerical quadrature,

\[
\boxed{
 K(0)=\frac5{264},\qquad
 K'(0)=-\frac{1395}{2288}.}                         \tag{104}
\]

The same beta-prime calculation gives the exact second derivative before
any interval work.  Pointwise in the outer variables,

\[
\begin{aligned}
 \overline H''_0={11a\over1024}\bigl(&
 42939a^2c^2-57408a^2c+17632a^2
 -5616ac^2+8048ac-2432a\\
 &{}+256c^2-512c+256\bigr).                         \tag{104a}
\end{aligned}
\]

Using the independent beta-prime/Beta moments of \(a,c\) in this
polynomial, and the inverse moments of \(c\) for \(G_e=a/(c+ea)\), yields

\[
\begin{array}{c|ccc}
 &F(0)&F'(0)&F''(0)\\ \hline
 F=\Phi-\Theta&\dfrac5{24}&-\dfrac{4315}{624}&\dfrac{12707}{39},
\end{array}                                         \tag{104b}
\]

and hence

\[
 \boxed{K''(0)=\frac{32447}{1144}>0.}              \tag{104c}
\]

For a short arithmetic audit of (104b), the two square terms separately
satisfy

\[
 (\Phi(0),\Phi'(0),\Phi''(0))=(1,-12,376),\qquad
 (\Theta(0),\Theta'(0),\Theta''(0))
 =\left(\frac{19}{24},-\frac{3173}{624},\frac{1957}{39}\right).
                                                               \tag{104d}
\]

There is also a compact exact recurrence for every curvature quantity needed
away from zero.  Under \(\mathbb E_e^\circ\), put

\[
 z=\frac{y}{1+ey},\qquad
 R=\frac{\partial_eP_e}{P_e}
   =\frac{y(1-w+wy)}{P_e},\qquad
 \mu_{ij}=\mathbb E_e^\circ[z^iR^j].
\]

Since \(z'=-z^2\), \(R'=-R^2\), and the uncentered score is
\(S=10z-(21/2)R\), normalized-expectation differentiation gives

\[
\boxed{
 \mu_{ij}'
 =(10-i)\mu_{i+1,j}
 -\left(\frac{21}{2}+j\right)\mu_{i,j+1}
 -\left(10\mu_{10}-\frac{21}{2}\mu_{01}\right)\mu_{ij}.}        \tag{105}
\]

In particular,

\[
\begin{aligned}
 \overline H_e'={}&
 9\mu_{20}-\frac{21}{2}\mu_{11}
 -10\mu_{10}^2+\frac{21}{2}\mu_{01}\mu_{10},\\
 \overline H_e''={}&
 \frac14\bigl(
 882\mu_{01}^2\mu_{10}-1680\mu_{01}\mu_{10}^2
 -882\mu_{01}\mu_{11}+756\mu_{01}\mu_{20}\\
 &\quad-483\mu_{02}\mu_{10}+800\mu_{10}^3
 +1680\mu_{10}\mu_{11}-1080\mu_{10}\mu_{20}\\
 &\quad+483\mu_{12}-756\mu_{21}+288\mu_{30}
 \bigr).                                             \tag{106}
\end{aligned}
\]

If \(A_e=G_e-O_e\) and \(B_e=\overline H_e-O_e\), then

\[
\begin{aligned}
 A_e'&=-G_e^2+O_e^2,&
 A_e''&=2G_e^3-2O_e^3,\\
 B_e'&=\overline H_e'+O_e^2,&
 B_e''&=\overline H_e''-2O_e^3,                     \tag{107}\\
 \Phi''&=2\mathbb E\{(A_e')^2+A_eA_e''\},&
 \Theta''&=2\mathbb E\{(B_e')^2+B_eB_e''\}.
\end{aligned}
\]

Thus convexity of the wall gap reduces exactly to the sign of

\[
 K''(e)=\frac1{11}
 \left[
 2\{\Phi'(e)-\Theta'(e)\}
 +(1+e)\{\Phi''(e)-\Theta''(e)\}
 \right].                                           \tag{108}
\]

Equations (105)--(108) involve only positive inner moments followed by
polynomial interval arithmetic.  They are a rigorous finite certification
route for wall convexity; no sign claim for (108) is promoted here until
those moment enclosures are replayed.

## 14. Replayed interior and compact-wall certificates

Define the normalized log-ratio gap

\[
 \mathcal J(x)=\frac{11}{1+e^x}D(e^x).
\]

The interior replay uses twenty-eight consecutive blocks

\[
 I_j=\left[\frac j7,\frac{j+1}{7}\right],
 \qquad j=0,\ldots,27,                               \tag{109}
\]

which cover \([0,4]\), hence in particular \([0,\log50]\).  On each block it
evaluates \(\mathcal J\) at the fourteen Chebyshev roots.  Arb encloses the
displacement between each exact root and the nearby exact rational
variance ratio used by the sinc engine; the derivative bound
\(|\mathcal J'|\le77\) from (64) transports the point ball back to the exact
root.  The degree-thirteen interpolation remainder is the exact rational

\[
 \frac{11}{134217728}<8.20\mathbin{\cdot}10^{-8}.    \tag{110}
\]

The checker forms the interval-valued cardinal interpolation maps before
combining them with the statistical node balls, converts each local
polynomial to Bernstein form, and subdivides eight times.  This order retains
the correlations lost by a naive interval DCT.  The replayed artifact
`../certificates/Certificate0003/Data0008.json` proves

\[
 \boxed{\mathcal J(x)>4.023548706990929
        \mathbin{\cdot}10^{-6}\quad(0\le x\le4).}    \tag{111}
\]

`GD/Module0181.lean` separately kernel-checks
the exact remainder arithmetic and the fail-closed implication from a
uniform polynomial margin to positivity.

The compact wall is closed by the separate three-halves producer.  Its
artifact `../certificates/Certificate0003/Data0009.json`, of format
`certificate0003-wall-three-halves-directed-sinc-v1`, contains exact rational cells whose
disjoint union is

\[
 [0,1/50].                                           \tag{112}
\]

Every cell uses the same central outer logit lattice, with step \(1/16\),
\(-14\le a\le7/2\), and \(-8\le b\le8\).  The complex comparison (33m)
reduces its outer Poisson and omitted-lattice ledgers to

\[
 X=e^b=\frac{s}{1-s},\qquad E X=\frac54,qquad
 E X^2=\frac52.                                     \tag{113}
\]

On the real lattice, the absolute field is bounded by
\(2+5X+13X^2/4\); the three weighted beta-logit tails have exact left/right
rates \((5,5)\), \((6,4)\), and \((7,3)\).  On the complex axis and mixed
contours, (33m) gives the corresponding secant-weighted quadratic field.
Equation (79) and positive geometric series therefore enclose every outer
Poisson mode and every omitted lattice point without a \(1/e\) constant.

The final replay accepted all 225 initial cells without bisection.  Its exact
global result is

\[
 \boxed{
 K(e)=e^{-1}D(e^{-1})
 \ge\frac{2502505592391819}{288230376151711744}
 >0.00868231039977067
 \quad(0\le e\le1/50).}                             \tag{113a}
\]

The minimum lower endpoint occurs on \([199/10000,1/50]\).  The current certificate manifest identifies the data and checking programs.

Fresh wall-generation batches bind their actual producer and checking sources
and the exact theorem-section bytes (33a)--(33m). The supplied wall cells use
the explicit retained-enclosure mode: the input manifest binds the current
data and checking sources, and the analytic section keeps its original byte
identity. The two finite checkers verify these identities, exact binary64
serialization, dyadic routing, every nonnegative external ledger entry,
strict positivity, and gap-free/nonoverlapping coverage of (112). The
separate checker imports no producer code. These finite checks retain the
supplied directed bounds; they do not rerun the enclosure producer.

**Uniform balanced domination theorem.**  For every \(\eta>0\),

\[
 \boxed{D(\eta)>0\qquad\text{for every }\eta>0.}     \tag{114}
\]

Indeed, (111) proves (114) for \(1\le\eta\le50\), (113a) proves it for
\(\eta\ge50\), and the exact swap identity (33) proves it for
\(0<\eta<1\).  Thus the double scale-Haar posterior mean strictly dominates
the plug-in precision rule at every variance ratio in the balanced
\((11,11)\) experiment.

To state the finite non-improvability conclusion, let

\[
 \mathscr C_6=
 \left\{\delta_H+\Delta\{A(H_\eta)F^\star-B(H_\eta)\}:
 A(h),B(h)\in h(1-h)\mathbb R[h]_{\le4}\right\}.     \tag{115}
\]

The accepted simplex certificate (48)--(51) and the positive-definite Gram
identity (38)--(40) prove that no nonzero member of \(\mathscr C_6\) weakly
dominates \(\delta_H\) at all variance ratios.  Together with (114), this
establishes both stated conclusions.

The scope is exact.  The result proves uniform domination by \(\delta_H\) and
degree-six non-improvability inside the displayed ten-dimensional correction
class at the balanced \((11,11)\) design.  It is not admissibility against
arbitrary measurable rules, does not contradict the separately
validated-numerical degree-seven improving direction, does not prove termination
of every correction ladder, and supplies no asymmetric-design architecture.
