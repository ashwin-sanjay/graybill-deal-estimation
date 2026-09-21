# Exact far-amplitude eight-tent strictness and a transverse second descent

## Authority and scope

This note proves a theorem for the ordinary balanced two-sample normal design
`(m,n)=(2,2)` under squared-error loss.  The analytic reductions and the
finite-packet consequences are paper proofs.  Two retained programs certify
the only large continuum sign inequalities with exact rational interval
arithmetic.  Nothing here is Lean-kernel evidence.

The result concerns one fully displayed historical tent direction at a new
amplitude and one fully displayed transverse direction.  It does not identify
either rule with the noncomputable selected certificate used in the general strict-completion result.
Its conclusions are strict descent and a seed-specific finite-packet floor.

## 1. Experiment, coordinates, and the two rules

Let

\[
 x_1,x_2\stackrel{\mathrm{iid}}\sim N(\mu,\sigma^2),\qquad
 y_1,y_2\stackrel{\mathrm{iid}}\sim N(\mu,\tau^2),
 \qquad \sigma,\tau>0,
\]

with the two samples independent.  Put

\[
 \bar x=\frac{x_1+x_2}{2},\quad
 \bar y=\frac{y_1+y_2}{2},\quad
 D=\bar x-\bar y,
\]

\[
 s_x^2=\sum_{i=1}^2(x_i-\bar x)^2,\qquad
 s_y^2=\sum_{j=1}^2(y_j-\bar y)^2,
\]

and, when `V=s_x^2+s_y^2>0`,

\[
 e=\frac{s_y^2}{V},\qquad F=\frac{2D^2}{V}.
\]

Set `(e,F)=(1/2,0)` when `V=0`.  This null-stratum totalization makes all
rules below literal Borel functions without changing any physical risk.  The
stable generalized Graybill--Deal rule is

\[
 \beta=\bar y+eD.
\]

For `c in R`, `eta>0`, write

\[
 H_{c,\eta}(z)=\max\{1-|z-c|/\eta,0\}.
\]

Fix `eta=1/100000` and define the antisymmetric eight-tent coefficient

\[
 Q(e,F)=\sum_{r=1}^4 c_r
 [H_{\ell_r,\eta}(e)-H_{1-\ell_r,\eta}(e)]H_{f_r,\eta}(F),
\]

where

\[
\begin{array}{c|c|c}
\ell_r&f_r&c_r\\ \hline
1/20&2&-46233/500000\\
3/20&1/50&294569/500000\\
1/50&1/50&131993/1000000\\
1/10&1/50&70711/1000000.
\end{array}
\]

The eight supports are pairwise disjoint.  At amplitude `a=1/250`, put

\[
 d_a=\bar y+D(e+aQ(e,F)).
\]

For the transverse correction fix `rho=10^{-12}` and `t=10^{-4}`, and put

\[
\begin{aligned}
J(e,F)={}&3[H_{1/500,\rho}(e)-H_{499/500,\rho}(e)]H_{1/1000,\rho}(F)\\
&-4[H_{1/120,\rho}(e)-H_{119/120,\rho}(e)]H_{20,\rho}(F),
\end{aligned}
\]

\[
 \widetilde d=d_a+tD J(e,F).
\]

The supports of `J` are pairwise disjoint and disjoint from those of `Q`, so

\[
 QJ=0
\tag{1}
\]

pointwise.

## 2. Exact projective risk reduction

Set

\[
 S=\sigma^2+\tau^2,\qquad q=\frac{\tau^2}{S}\in(0,1),
\]

and define

\[
 X=\frac{s_x^2}{\sigma^2},\qquad
 Y=\frac{s_y^2}{\tau^2},\qquad
 Z=\sqrt{\frac2S}\,D.
\]

Then `X`, `Y`, and `Z` are independent; `X`, `Y`, and `Z^2` have the
`chi-square-one` law.  The oracle linear combination

\[
 \widehat\mu=\bar y+qD
\]

is independent of `(D,X,Y)`, has mean `mu`, and has variance

\[
 \operatorname{Var}(\widehat\mu)=\frac{\sigma^2\tau^2}{2S}.
\]

Consequently, for every measurable coefficient `h` of finite displayed
expectation and `delta_h=bar y+D h(e,F)`, orthogonality gives

\[
 R_\theta(\delta_h)
 =\frac{\sigma^2\tau^2}{2S}
  +\frac S2\mathbb E[Z^2(h(e,F)-q)^2].
\tag{2}
\]

To eliminate the radial coordinate, put

\[
 \mathcal R=(1-q)X+qY,qquad
 e=\frac{qY}{\mathcal R},\qquad
 F=\frac{Z^2}{\mathcal R}.
\]

The inverse transformation, now explicitly using `W=Z^2` rather than signed
`Z`, is

\[
 X=\frac{\mathcal R(1-e)}{1-q},\quad
 Y=\frac{\mathcal R e}{q},\quad
 W=\mathcal R F,
\]

and its absolute Jacobian is `mathcal R^2/[q(1-q)]`.  Multiplying the three
chi-square-one densities and integrating `mathcal R` gives, for every
nonnegative or integrable `phi`,

\[
 \mathbb E[D^2\phi(e,F)]
 =\frac{3S}{4\pi}[q(1-q)]^2
 \int_0^1\!\int_0^\infty W_q(e,F)\phi(e,F)\,dF\,de,
\tag{3}
\]

where

\[
 N_q(e,F)=e+(1-2e+F)q-Fq^2,
\]

\[
 W_q(e,F)=\sqrt{\frac{F}{e(1-e)}}\,N_q(e,F)^{-5/2}>0.
\tag{4}
\]

Thus location vanishes, common scale becomes the positive outer factor `S`,
and all nuisance-shape dependence is carried by compact `q in [0,1]`.

## 3. The far-amplitude rule is still strictly better

From (2),

\[
 R_\theta(d_a)-R_\theta(\beta)
 =a\mathbb E[D^2\{2(e-q)Q+aQ^2\}].
\tag{5}
\]

Define the normalized bracket

\[
 T(q)=\eta^{-2}\int W_q(e,F)
 \{2(e-q)Q(e,F)+aQ(e,F)^2\}\,dF\,de.
\tag{6}
\]

Since `Q(1-e,F)=-Q(e,F)` and

\[
 N_{1-q}(1-e,F)=N_q(e,F),
\]

we have `T(1-q)=T(q)`.  It therefore suffices to certify `[0,1/2]`.

For each of the eight disjoint supports, replace the two normalized tent
averages by their centre value.  The resulting centre sum is

\[
 S_0(q)=\sum_{r=1}^4\sum_{\epsilon=\pm1}
 \left[2\epsilon c_r(e_{r,\epsilon}-q)+\frac{4ac_r^2}{9}\right]
 W_q(e_{r,\epsilon},f_r),
\tag{7}
\]

where `e_(r,+)=ell_r` and `e_(r,-)=1-ell_r`.  The factor `4/9` is exact:
the integral of the square of a unit triangular tent is `2/3`, once in each
coordinate.

The retained Part A checker covers `[0,1/2]` by the 50,000 closed rational
cells `[k/100000,(k+1)/100000]`.  On every cell it encloses every square root
by integer-square-root bounds whose defining squared inequalities are checked
in `Fraction` arithmetic.  It proves

\[
 S_0(q)<-\frac{47}{200}.
\tag{8}
\]

The normalized triangular tent has second moment `1/6`, and the normalized
squared triangular tent has second moment `1/10`.  Symmetric Taylor
integration, first in `e` and then in `F`, therefore needs only pure second
derivatives.  Exact rational bounds on the logarithmic derivatives of `W_q`
give

\[
 |T(q)-S_0(q)|<0.000716979<\frac1{1000}.
\tag{9}
\]

Combining (8), (9), and reflection proves

\[
 T(q)<-\frac{117}{500}\qquad(0\le q\le1).
\tag{10}
\]

Substitution into (3)--(6) yields the explicit continuum margin

\[
 \boxed{
 R_\theta(d_a)-R_\theta(\beta)
 <-\frac{351\eta^2}{500000\pi}
 \frac{\sigma^4\tau^4}{(\sigma^2+\tau^2)^3}<0.}
\tag{11}
\]

Both `d_a` and `widetilde d` are Borel.  Since `|Q|<1` and `J` is bounded,
each is bounded by a fixed linear combination of `|bar y|` and `|D|`, so both
have finite risk at every physical parameter.  Under a common transformation
`omega -> alpha omega+gamma`, `alpha>0`, the quantities `e,F,Q,J` are fixed,
while `bar y` and `D` transform affinely and linearly.  Hence both rules are
pointwise positive-affine equivariant and their risks have the exact
`alpha^2` character.

## 4. The old amplitude ray has already turned

At `q=1/362`, equivalently the physical scale pair `(sigma,tau)=(19,1)`, the
risk difference from `d_a` to `d_(2a)` has the same normalized expression as
(6) with the coefficient of `aQ^2` multiplied by three.  The exact centre and
remainder enclosure proves

\[
 T_{3a}(1/362)>\frac{739}{1000}>0.
\tag{12}
\]

Thus `d_(2a)` is worse than `d_a` at this physical parameter and cannot
dominate it.

There is a stronger local statement.  Differentiating risk with respect to
amplitude at `a` produces the multiplier-two bracket.  Invoking the same exact
checker routines with multiplier two gives

\[
 T_{2a}(1/362)>\frac{93}{500}>0.
\tag{13}
\]

So the pointwise quadratic risk along the original ray has its minimizer
strictly below `a` at this scale ratio.  Thus the
uniform ray threshold satisfies `m<a`.  This is precisely why the
below-threshold positive-current separator does not apply to `d_a`; it is not
a contradiction to that theorem.

## 5. A disjoint transverse direction still descends everywhere

By (1), the cross term involving `aQJ` vanishes.  Equations (2)--(4) give

\[
 R_\theta(\widetilde d)-R_\theta(d_a)
 =\frac{3S}{4\pi}[q(1-q)]^2\{2tG(q)+t^2H(q)\},
\tag{14}
\]

where

\[
 G(q)=\int(e-q)J(e,F)W_q(e,F)\,dF\,de,
 \qquad H(q)=\int J(e,F)^2W_q(e,F)\,dF\,de.
\]

For rational `z,f`, define

\[
 g_{z,f}(q)=(z-q)W_q(z,f)+(q+z-1)W_q(1-z,f),
\]

\[
 s_{z,f}(q)=W_q(z,f)+W_q(1-z,f).
\]

The Part B checker takes natural outward interval extensions simultaneously
over `q` and over every point of all four `rho`-wide tent rectangles.  On 28
contiguous dyadic leaves covering `[0,1/2]`, with maximum depth 13, it proves
the stronger pointwise inequality

\[
 4g_B-3g_A-\frac t2(9s_A+16s_B)-\frac1{1000}(s_A+s_B)>0.
\tag{15}
\]

If `h=(1-|u|)_+(1-|v|)_+`, then `0<=h<=1`.  Multiplying (15) by `h`, and
using `h^2<=h`, shows pointwise that the paired contribution to
`G+(t/2)H` is strictly negative; the final slack is negative on a set of
positive area.  Integration gives

\[
 2tG(q)+t^2H(q)<0\qquad(0\le q\le1/2).
\]

The identity `W_(1-q)(z,f)=W_q(1-z,f)` supplies the other half.  Therefore

\[
 \boxed{R_\theta(\widetilde d)<R_\theta(d_a)
 \quad\text{for every physical }\theta.}
\tag{16}
\]

In particular, `d_a` is inadmissible and nonterminal.  By transitivity and
(11), `widetilde d` is another explicit Borel, finite-risk,
positive-affine-equivariant rule strictly below the stable baseline.

## 6. The descendant forces a seed-specific finite-packet floor

Let `theta_0=(0,1,1)`, write `P_0=P_(theta_0)`, and let

\[
 L_\theta=\frac{dP_\theta}{dP_0}
 =\sigma^{-2}\tau^{-2}
 \exp\!\left\{\frac{\sum x_i^2+\sum y_j^2}{2}
 -\frac{\sum(x_i-\mu)^2}{2\sigma^2}
 -\frac{\sum(y_j-\mu)^2}{2\tau^2}\right\}.
\]

For a finite packet `Pi={(theta_i,w_i)}` with `w_i>=0`, define

\[
 M_\Pi=1+\sum_iw_iL_{\theta_i},\qquad
 A_\Pi=\sum_iw_i\mu_iL_{\theta_i},\qquad
 c_\Pi=\frac{A_\Pi}{M_\Pi},
\]

\[
 B_a(\Pi)=\int M_\Pi(d_a-c_\Pi)^2\,dP_0.
\tag{17}
\]

Put `h_*=widetilde d-d_a=tDJ`.  Sum the strict risk differences (16) over
the baseline atom `theta_0` with weight one and every packet atom.  With

\[
 X=\int M_\Pi h_*^2\,dP_0,
\]

the result is

\[
 X+2\int M_\Pi h_*(d_a-c_\Pi)\,dP_0<0.
\]

Cauchy--Schwarz yields `X<4B_a(Pi)`.  Since `M_Pi>=1`,

\[
 B_a(\Pi)>\frac14\|h_*\|_{L^2(P_0)}^2.
\tag{18}
\]

At `P_0`, `S=2` and `q=1/2`.  On the rectangle of half-width `rho/2` around
`(e,F)=(1/500,1/1000)`, one has `J^2>=9/16` and `W_(1/2)>1/16`.  Its area is
`rho^2`.  Using (3) and `pi<4` gives

\[
 \mathbb E_0[D^2J^2]>\frac{27\rho^2}{32768}.
\]

Together with (18),

\[
 \boxed{B_a(\Pi)>\frac{27t^2\rho^2}{131072}>10^{-36}}
\tag{19}
\]

for every finite nonnegative physical packet.  Hence the proposed anchored
`B_a(Pi_j)->0` terminalization of this fixed `d_a` is impossible.  This is a
floor for the anchored Bayes excess of `d_a`, not the four-term
terminal-projection residual of the complete seed-cone projection, and it is not a uniform floor over
all eligible seeds.

## 7. Square completion, atom prices, and the exact convex remainder

For completeness, set

\[
 C_\Pi=\sum_iw_i\mu_i^2L_{\theta_i},\qquad
 \mathcal S_\Pi(z)=R_0(z)+\sum_iw_iR_{\theta_i}(z).
\]

Direct expansion gives

\[
 \mathcal S_\Pi(z)=K_\Pi+\int M_\Pi(z-c_\Pi)^2\,dP_0,
\]

where

\[
 K_\Pi=\int(C_\Pi-A_\Pi^2/M_\Pi)\,dP_0\ge0.
\]

If a measurable `r` satisfies `R_theta(r)<=R_theta(d_a)` for every physical
`theta`, cancellation of `K_Pi` and the triangle inequality in
`L^2(M_Pi dP_0)` give

\[
 \|r-d_a\|_{L^2(P_0)}^2\le4B_a(\Pi).
\tag{20}
\]

Thus an anchored null sequence would indeed make `d_a` terminal modulo the
common physical null ideal.  The implication is correct; (16) and (19) show
that its premise is false here.

There is also an exact global convexity identity.  For two finite weight
vectors `w,w'`, let `delta M=M'-M`, `delta A=A'-A`, and `c=A/M`.  Then

\[
\begin{aligned}
B(w')-B(w)={}&\sum_i(w_i'-w_i)
 [R_{\theta_i}(d_a)-R_{\theta_i}(c)]\\
&+\int\frac{(\delta A-c\,\delta M)^2}{M'}\,dP_0.
\end{aligned}
\tag{21}
\]

This proves convexity and the atom-price formula without a boundary Hessian
interchange.  For one new atom `(theta,mu,L_theta)` at weight `s>=0`, it reads

\[
\begin{aligned}
B(w+s\delta_\theta)={}&B(w)
+s[R_\theta(d_a)-R_\theta(c_w)]\\
&+s^2\int\frac{L_\theta^2(\mu-c_w)^2}{M_w+sL_\theta}\,dP_0.
\end{aligned}
\tag{22}
\]

The remainder is nonnegative and finite for `s>0`, since
`L_theta^2/(M_w+sL_theta)<=L_theta/s`.  Formula (22), rather than a blanket
finite-`C^2` assertion on the closed weight orthant, is the safe atom-pricing
interface.

## 8. Exact logical force

The result supplies two concrete strict descents:

\[
 \beta\succ d_a\succ\widetilde d.
\]

It proves exactly where the original amplitude ray has turned at one physical
ratio and shows that a transverse direction can still descend.  It also
places `d_a` on the positive anchored-gap branch.  It does not decide whether
the lower-cone terminal projection of `d_a` is affine-fixed, whether
`widetilde d` has zero reference gap, or whether any infinite descending
energy chain exists.  

## 9. Reproducibility

The exact certificate lane is
[`../certificates/Certificate0002`](../certificates/README.md).
The wrapper independently invokes the multiplier-two derivative enclosure,
schema-validates the complete rational artifact, verifies source hashes, and
requires exact artifact equality on replay.  Current verification records identify the executed programs and inputs.
