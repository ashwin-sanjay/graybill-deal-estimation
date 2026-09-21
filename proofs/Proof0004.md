# Logarithmic finite mixtures give the exact native (3,3) oracle minimax value

This proof gives the logarithmic-mixture argument and explicit error bounds. The
analytic assertions below have **paper-proof evidence**. The accompanying Lean
file checks the final algebra from the window-bound hypotheses; it does not
formalize or discharge the integral estimates. The precise evidence boundary is
recorded in [Section 12](#12-proof-authority-and-exact-source-prerequisites).

The main result is

\[
\inf_{d:\mathbb R^6\to\mathbb R\ \mathrm{Borel}}
\sup_{\mu\in\mathbb R,\ \sigma_X,\sigma_Y>0}
\frac{\mathbb E_{\mu,\sigma_X,\sigma_Y}(d-\mu)^2}
{(3/\sigma_X^2+3/\sigma_Y^2)^{-1}}
=1+\frac\pi4.
\]

An explicit estimator attaining this value is given in Section 9. The lower
bound controls arbitrary Borel dependence on both projective coordinates,
including the standardized difference of sample means. Its certificate is a
sequence of finite, positive, rational mixtures with an explicit error smaller
than \(14/N\).

## 1. The reduced problem and its physical model map

Let \(X_1,X_2,X_3\) and \(Y_1,Y_2,Y_3\) be independent normal samples with
common mean \(\mu\) and respective positive variances \(\sigma_X^2,\sigma_Y^2\).
Use the unbiased sample variances

\[
S_X^2=\frac12\sum_{i=1}^3(X_i-\bar X)^2,
\qquad S_Y^2=\frac12\sum_{i=1}^3(Y_i-\bar Y)^2.
\]

Define

\[
v_X=\frac{\sigma_X^2}{3},\quad v_Y=\frac{\sigma_Y^2}{3},
\quad v=v_X+v_Y,\quad t=\frac{v_Y}{v}\in(0,1),
\quad \tau=vt(1-t),
\]
\[
D=\bar X-\bar Y,\quad A=\frac{S_X^2}{3},\quad B=\frac{S_Y^2}{3},
\quad u=\frac B{A+B},\quad s=\frac{D^2}{A+B}.
\]

The exceptional set where these coordinates are not in
\(\Omega=(0,1)\times(0,\infty)\) has probability zero at every parameter.
For \(g:\Omega\to[0,1]\) Borel, its physical lift is

\[
d_g=\bar Y+Dg(u,s).
\]

Set \(d_g=(\bar X+\bar Y)/2\) on the exceptional set. This specifies a finite
Borel estimator on the complete sample space.

The oracle estimator \(\bar Y+tD\) has risk \(\tau\), and its error is
independent of \(D,A,B\). Orthogonality therefore gives

\[
R_\theta(d_g)=\tau+\mathbb E_\theta[D^2(g(u,s)-t)^2]. \tag{1.1}
\]

To identify the latter expectation, normalize by \(v\). Then
\(A/v\) and \(B/v\) are independent exponentials of means \(1-t\) and \(t\),
and \(D^2/v\) is an independent chi-square variable with one degree of freedom.
Multiplication by \(D^2/v\), whose expectation is one, changes that last law to
chi-square with three degrees of freedom. In the resulting size-biased
probability law, put

\[
(A/v,B/v,D^2/v)=(r(1-u),ru,rs).
\]

The Jacobian is \(r^2\). Integrating the radial density gives

\[
f_t(u,s)=\frac{15\sqrt{s}}{t(1-t)
\left(s+\frac{2(1-u)}{1-t}+\frac{2u}{t}\right)^{7/2}}.
\]

Indeed, the radial integral is
\(\Gamma(7/2)\lambda^{-7/2}\), with
\(\lambda=(1-u)/(1-t)+u/t+s/2\); the ratio of Gamma constants is
\(\Gamma(7/2)/\Gamma(3/2)=15/4\). Define the loss kernel

\[
K_t(u,s)=\frac{f_t(u,s)}{t(1-t)}
=\frac{15\sqrt{s}}{t^2(1-t)^2
\left(s+\frac{2(1-u)}{1-t}+\frac{2u}{t}\right)^{7/2}},
\]
\[
\mathcal G=\{g:\Omega\to[0,1]:g\text{ is Borel}\},\qquad
L_t(g)=\int_\Omega K_t(u,s)(g(u,s)-t)^2\,du\,ds,
\qquad z=\frac\pi4.
\]

Equation (1.1) becomes the exact physical risk identity

\[
\frac{R_\theta(d_g)}{\tau}=1+L_t(g). \tag{1.2}
\]

For later use, direct integration in \(s\) yields

\[
\int_0^\infty K_t(u,s)\,ds
=\frac1{[t(1-u)+(1-t)u]^2},
\qquad \int_\Omega K_t=\frac1{t(1-t)}, \tag{1.3}
\]
\[
K_{1-t}(u,s)=K_t(1-u,s). \tag{1.4}
\]

In particular, \(L_t(g)\) is finite for every interior \(t\) and every
\(g\in\mathcal G\).

One existing completeness result is needed to pass from this coefficient
problem to all Borel estimators: **if a Borel estimator has a uniform oracle
risk cap \(C\ge0\), then some \(g\in\mathcal G\) satisfies
\(L_t(g)\le C-1\) for every \(t\in(0,1)\).** The exact source is
`GD.N0045.d023068`, in
`GD/Module1461.lean`.
Its literal hypotheses are ordinary sample sizes, Borel measurability of the
input estimator, and the complete finite oracle cap; it imposes no symmetry,
terminality, or domination hypothesis on that estimator. Section 12 records
its verification evidence. This proof uses the theorem only for constant oracle caps.

## 2. An explicit strict interior upper bound

Let

\[
g_0(u,s)=\frac{u^2}{u^2+(1-u)^2}.
\]

This section records a self-contained version of the existing upper-bound calculation.
By (1.3),

\[
L_t(g_0)=\int_0^1
\left(\frac{g_0(u,s)-t}{t(1-u)+(1-t)u}\right)^2du.
\]

Put \(r=2t-1\), \(q=r^2\in[0,1)\), and

\[
F(r,x)=\left(\frac{2x-r(1+x^2)}{(1+x^2)(1-rx)}\right)^2,
\qquad j(q)=\int_0^1\frac{dx}{1-qx^2}.
\]

The substitution \(u=(1+x)/2\), followed by averaging \(x\) and \(-x\), gives
\(L_t(g_0)=\int_0^1[F(r,x)+F(r,-x)]/2\,dx\). The elementary rational identity

\[
\begin{aligned}
\frac{F(r,x)+F(r,-x)}2={}&
\frac{q(1-q)^2}{(1+q)^2}\frac{1+qx^2}{(1-qx^2)^2}
+\frac{4q(1-q)^2}{(1+q)^3}\frac1{1-qx^2}\\
&-\frac{4(1-q)}{(1+q)^2}\frac1{(1+x^2)^2}
+\frac{4(2q^2-q+1)}{(1+q)^3}\frac1{1+x^2}
\end{aligned}
\]

can be checked by multiplying denominators. Integrate using

\[
\int_0^1\frac{1+qx^2}{(1-qx^2)^2}dx=\frac1{1-q},\quad
\int_0^1\frac{dx}{(1+x^2)^2}=\frac14+\frac\pi8,\quad
\int_0^1\frac{dx}{1+x^2}=\frac\pi4.
\]

It follows that

\[
L_t(g_0)=E(q,j(q)),\qquad
E(q,j)=-\frac{(1-q)^2}{(1+q)^2}
+\frac\pi2\frac{5q^2-2q+1}{(1+q)^3}
+\frac{4q(1-q)^2}{(1+q)^3}j.
\]

Since \((1-qx^2)^{-1}\le1+qx^2/(1-q)\),
\(j(q)\le1+q/[3(1-q)]\). The coefficient of \(j\) is nonnegative, and

\[
z-E\left(q,1+\frac q{3(1-q)}\right)
=\frac{1-q}{(1+q)^3}
\left[(1-z)+(3\pi/2-4)q+(5/3-z)q^2\right]>0.
\]

The last inequality uses \(0\le q<1\) and \(3<\pi<4\). Hence

\[
L_t(g_0)<z\quad(0<t<1),\qquad \sup_{0<t<1}L_t(g_0)\le z. \tag{2.1}
\]

This proof is the real-integral content of
`GD.N0016.d008320`.
The argument below proves equality in the supremum without needing a separate
endpoint-limit theorem.

## 3. Finite-mixture completion and weak duality

Let \(\mathcal P_{\mathbb Q}\) be the finite probability measures

\[
P=\sum_{i=1}^m p_i\delta_{t_i},\qquad
p_i\in\mathbb Q_{>0},\quad t_i\in\mathbb Q\cap(0,1),\quad\sum_i p_i=1.
\]

For \(j=0,1,2\), define

\[
M_j(P;u,s)=\sum_i p_it_i^jK_{t_i}(u,s),\qquad
g_P=\frac{M_1}{M_0},\qquad
\mathfrak B(P)=\int_\Omega\left(M_2-\frac{M_1^2}{M_0}\right)du\,ds.
\]

All kernels are positive. Thus \(M_0>0\), and \(g_P\) is a continuous
\([0,1]\)-valued function. Pointwise quadratic completion gives

\[
\sum_i p_iK_{t_i}(g-t_i)^2
=M_2-\frac{M_1^2}{M_0}+M_0(g-g_P)^2, \tag{3.1}
\]
\[
M_2-\frac{M_1^2}{M_0}
=\frac{\sum_{i<j}p_ip_jK_{t_i}K_{t_j}(t_i-t_j)^2}{\sum_i p_iK_{t_i}}
\ge0. \tag{3.2}
\]

Equivalently, the nonnegative term is the Schur complement of the upper-left
entry of \(\sum_i p_iK_{t_i}(1,t_i)^{\mathsf T}(1,t_i)\).
All integrals in (3.1) are finite by (1.3). Therefore

\[
\sum_i p_iL_{t_i}(g)=\mathfrak B(P)
+\int_\Omega M_0(g-g_P)^2,\qquad
\mathfrak B(P)=\min_{g\in\mathcal G}\sum_i p_iL_{t_i}(g). \tag{3.3}
\]

In particular, for
\(\beta=\inf_{g\in\mathcal G}\sup_tL_t(g)\),

\[
0\le\mathfrak B(P)\le\beta\le z. \tag{3.4}
\]

Moreover, (2.1) and the finite average at \(g_0\) show
\(\mathfrak B(P)<z\) for every \(P\in\mathcal P_{\mathbb Q}\). No infinite
dimensional minimax exchange or strong duality theorem is assumed here.

## 4. The endpoint kernel and its truncation

For \(x>0\), define

\[
k_u(x)=\frac{15\sqrt x}{(x+2u)^{7/2}}.
\]

The change \(y=\sqrt{x/(x+2u)}\) gives the explicit primitive

\[
\int_a^b k_u(x)\,dx
=\frac{F_0(\sqrt{b/(b+2u)})-F_0(\sqrt{a/(a+2u)})}{u^2},
\qquad F_0(y)=\frac{5y^3-3y^5}{2},
\]

and therefore \(\int_0^\infty k_u=u^{-2}\). For \(0<a<b\) and \(0<u<1\),

\[
u^2\int_0^a k_u(x)dx
\le\frac5{4\sqrt2}(a/u)^{3/2}\le(a/u)^{3/2},
\qquad
u^2\int_b^\infty k_u(x)dx\le\frac{15u^2}{2b^2}\le\frac8{b^2}. \tag{4.1}
\]

Let

\[
H(x,y)=\frac{xy}{x+y}\quad(x,y>0).
\]

Quadratic completion and differentiation give

\[
xv^2+y(1-v)^2=(x+y)\left(v-\frac y{x+y}\right)^2+H(x,y),
\]
\[
H(\lambda x,\lambda y)=\lambda H(x,y),\quad
\partial_xH=\frac{y^2}{(x+y)^2}\ge0,\quad
\partial_yH=\frac{x^2}{(x+y)^2}\ge0.
\]

In particular,

\[
H(u^{-2},(1-u)^{-2})=\frac1{u^2+(1-u)^2},\qquad
\frac12\int_0^1H(u^{-2},(1-u)^{-2})du=z. \tag{4.2}
\]

For \(0<\eta<1/2\), put

\[
\alpha(u)=\int_a^b k_u(x)dx,\quad\gamma(u)=\alpha(1-u),\quad
J_{\eta,a,b}=\frac12\int_\eta^{1-\eta}H(\alpha(u),\gamma(u))du,
\quad M_{\eta,a,b}=\int_\eta^{1-\eta}(\alpha(u)+\gamma(u))du.
\]

## 5. The common logarithmic-window lower bound

Let \(A>\log2\), \(d=e^{-A}\), \(T>\log(b/a)\), and define

\[
\mathcal C_{A,T}=\inf_{g\in\mathcal G}\frac1{2T}
\int_A^{A+T}\bigl[L_{e^{-r}}(g)+L_{1-e^{-r}}(g)\bigr]dr,
\qquad
\rho=\left(1+\frac{2d}{(1-d)(a+2\eta)}\right)^{-7/2}.
\]

The following bound holds uniformly over all Borel coefficients:

\[
\boxed{\mathcal C_{A,T}\ge
\rho\left(1-\frac{\log(b/a)}T\right)(J_{\eta,a,b}-dM_{\eta,a,b}).} \tag{5.1}
\]

For \(t=e^{-r}\le d\), the substitution \(s=x/t\) gives

\[
\frac1tK_t(u,x/t)
=\frac{15\sqrt x}{(1-t)^2
\left(x+2u+\frac{2t(1-u)}{1-t}\right)^{7/2}}.
\]

On \(u\in[\eta,1-\eta]\), \(x\in[a,b]\), the last expression is at least
\(\rho k_u(x)\). Reflection gives the lower bound \(\rho k_{1-u}(x)\) for
\(t^{-1}K_{1-t}(u,x/t)\).

After this change of variables, set \(y=r+\log x\). Every interval
\([A+\log x,A+T+\log x]\), for \(x\in[a,b]\), contains

\[
W=[A+\log b,A+T+\log a],\qquad |W|=T-\log(b/a).
\]

Restrict the original **nonnegative squared-loss integrals** to this common
window. Only after that restriction use, for \(v\in[0,1]\),

\[
(v-t)^2\ge v^2-2d,\qquad(v-1+t)^2\ge(1-v)^2-2d.
\]

The averaged loss of any \(g\) is consequently at least

\[
\frac{\rho}{2T}\int_W\int_\eta^{1-\eta}
\left[\alpha(u)g(u,e^y)^2+\gamma(u)(1-g(u,e^y))^2
-2d(\alpha(u)+\gamma(u))\right]du\,dy.
\]

Apply the quadratic minimum in Section 4 inside this integral to obtain
(5.1), and then take the infimum over \(g\). The argument is valid even when
\(J-dM<0\). Tonelli applies to the original nonnegative integrands; the
restricted error integrals are finite. No boundary convergence or regularity
of \(g\) is used, and no infimum is interchanged with a limit.

## 6. Comparison with finite rational logarithmic grids

For an integer \(N\ge2\), define

\[
q_N=1-\frac1N,\quad h_N=-\log q_N,\quad k_N=N^3-N^2,
\quad A_N=N^2h_N,\quad T_N=k_Nh_N,\quad d_N=q_N^{N^2},
\]
\[
\widehat P_N=\frac1{2k_N}\sum_{j=N^2}^{N^3-1}
\left(\delta_{q_N^j}+\delta_{1-q_N^j}\right),\quad
B_N=\mathfrak B(\widehat P_N),\quad
c_N=q_N^2(1-d_N)^{7/2},\quad C_N=\mathcal C_{A_N,T_N}.
\]

These are finite rational probability measures. The following inequality holds:

\[
\boxed{B_N\ge c_NC_N-E_N,\qquad
E_N=\frac{2c_N(q_N^{-1}-1)}{1-d_N}.} \tag{6.1}
\]

Write \(q=q_N\), \(d=d_N\), \(c=c_N\). In the logarithmic bin
\(r\in[jh_N,(j+1)h_N]\), put \(t_0=q^j\), \(t=e^{-r}\). Thus
\(qt_0\le t\le t_0\le d\). If

\[
D_t(u,s)=s+\frac{2(1-u)}{1-t}+\frac{2u}{t},
\]

each positive summand shows \(D_t\ge(1-d)D_{t_0}\). Therefore

\[
\frac{K_{t_0}}{K_t}
=\left(\frac t{t_0}\right)^2
\left(\frac{1-t}{1-t_0}\right)^2
\left(\frac{D_t}{D_{t_0}}\right)^{7/2}\ge c.
\]

For \(v\in[0,1]\), \((v-t_0)^2\ge(v-t)^2-2(t_0-t)\). Apply kernel
domination to the nonnegative square first, and then use (1.3), to obtain

\[
L_{t_0}(g)\ge cL_t(g)-\frac{2c(t_0-t)}{t(1-t)}
\ge cL_t(g)-\frac{2c(q^{-1}-1)}{1-d}.
\]

The reflected loss has the identical bound. Integrate these two inequalities
over each bin and average over all \(k_N\) bins. Since \(k_Nh_N=T_N\),
the discrete averaged loss of every \(g\) is at least the continuum averaged
loss multiplied by \(c_N\), minus \(E_N\). Taking the discrete minimum in
(3.3) yields (6.1).

<a id="packet-quantitative-theorem"></a>

## 7. Quantitative truncation and the rate 14/N

For the remainder of this section let \(N\ge16\), and choose

\[
\eta_N=N^{-2},\quad a_N=N^{-4},\quad b_N=N^2,\quad
\theta_N=N^{-3}+8N^{-4}\le3N^{-3}<1.
\]

Write \(J_N=J_{\eta_N,a_N,b_N}\), \(M_N=M_{\eta_N,a_N,b_N}\). By (4.1),
on \([\eta_N,1-\eta_N]\),

\[
(1-\theta_N)u^{-2}\le\alpha(u)\le u^{-2},\qquad
(1-\theta_N)(1-u)^{-2}\le\gamma(u)\le(1-u)^{-2}.
\]

Homogeneity and monotonicity of \(H\) now give

\[
(1-\theta_N)I_{\eta_N}\le J_N\le I_{\eta_N}\le z,
\quad I_\eta=\frac12\int_\eta^{1-\eta}\frac{du}{u^2+(1-u)^2}
=\arctan(1-2\eta).
\]

The omitted endpoint intervals give \(0\le z-I_\eta\le2\eta\). Consequently,

\[
0\le z-J_N\le2N^{-2}+z\theta_N\le2N^{-2}+3N^{-3},\qquad
0<M_N\le2\left(N^2-\frac1{1-N^{-2}}\right)\le2N^2. \tag{7.1}
\]

Bernoulli's inequality gives
\(q_N^{-N}=(1+1/(N-1))^N>2\), hence \(d_N<2^{-N}\).
The equality \(2^{16}=16^4\), together with
\(((N+1)/N)^4\le(17/16)^4<2\), proves inductively that

\[
0<d_N\le N^{-4}<\frac12. \tag{7.2}
\]

Also \(h_N\ge1/N\), so

\[
A_N\ge N>\log2,\qquad T_N\ge N(N-1),\qquad
\lambda_N:=\frac{\log(b_N/a_N)}{T_N}
\le\frac{6\log N}{N(N-1)}\le\frac6N<1. \tag{7.3}
\]

Set

\[
\rho_N=\left(1+\frac{2d_N}{(1-d_N)(a_N+2\eta_N)}\right)^{-7/2},
\qquad w_N=\rho_N(1-\lambda_N),\qquad D_N=d_NM_N.
\]

The elementary inequalities
\(1-(1+x)^{-7/2}\le(7/2)x\) for \(x\ge0\), and
\(1-(1-d)^{7/2}\le(7/2)d\) for \(0\le d<1\), imply

\[
0<\rho_N,w_N,c_N\le1,\quad
1-\rho_N\le7N^{-2},\quad1-w_N\le7N^{-2}+6N^{-1},
\]
\[
1-c_N\le2N^{-1}+\frac7{2N^4},\quad
0\le D_N\le2N^{-2},\quad
0\le E_N=\frac{2c_N}{(N-1)(1-d_N)}\le\frac4{N-1}\le\frac5N. \tag{7.4}
\]

For the bound on \(\rho_N\), use
\(2d_N/[(1-d_N)(a_N+2\eta_N)]\le d_NN^2/(1-d_N)\le2/N^2\).
Sections 2, 5, and 6 give

\[
0\le C_N\le z,\qquad C_N\ge w_N(J_N-D_N),\qquad B_N\ge c_NC_N-E_N.
\]

The following elementary error assembly is useful independently. If
\(J,C\le z\), \(D\ge0\), \(0\le w,c\le1\),
\(C\ge w(J-D)\), and \(B\ge cC-E\), then

\[
z-B\le(z-J)+(1-w)z+D+(1-c)z+E. \tag{7.5}
\]

Indeed, \(C\ge J-(1-w)z-D\) and \(B\ge C-(1-c)z-E\).
Combining (7.1)–(7.5), with \(z<1\), gives

\[
\Delta_N:=z-B_N\le\frac{13}{N}+\frac{11}{N^2}
+\frac3{N^3}+\frac7{2N^4}.
\]

Finally,

\[
\frac{11}{N}+\frac3{N^2}+\frac7{2N^3}
\le\frac{11}{16}+\frac3{256}+\frac7{8192}
=\frac{5735}{8192}<1.
\]

Section 3 supplies strict positivity of \(\Delta_N\), so the result is

\[
\boxed{N\ge16\quad\Longrightarrow\quad
0<z-B_N\le\frac1N\left(13+\frac{5735}{8192}\right)<\frac{14}{N}.} \tag{7.6}
\]

## 8. A certified counterexample sequence and sharp reduced value

For each positive integer \(n\), choose \(P_n=\widehat P_{16n}\). Explicitly,

\[
P_n=\frac1{512n^2(16n-1)}
\sum_{j=256n^2}^{4096n^3-1}
\left[\delta_{(1-1/(16n))^j}+\delta_{1-(1-1/(16n))^j}\right].
\]

Equation (7.6) gives

\[
0<z-\mathfrak B(P_n)<\frac7{8n}<\frac1n. \tag{8.1}
\]

Thus this explicit sequence refutes the assertion

\[
\exists\varepsilon>0\ \forall P\in\mathcal P_{\mathbb Q},\qquad
\mathfrak B(P)\le z-\varepsilon.
\]

Taking limits in the ordinary numerical sequence \(B_N\), and using only
the weak-duality inequalities (3.4), proves

\[
\boxed{\lim_{N\to\infty}B_N
=\sup_{P\in\mathcal P_{\mathbb Q}}\mathfrak B(P)
=\inf_{g\in\mathcal G}\sup_{0<t<1}L_t(g)
=\frac\pi4.} \tag{8.2}
\]

In particular \(g_0\) is a minimizer, while no finite rational mixture attains
the displayed dual supremum. No interchange of the limit with an integral,
supremum, or infimum is used to deduce (8.2).

<a id="physical-minimax-theorem"></a>

## 9. Exact unrestricted physical minimax value and explicit attainer

The explicit physical lift of \(g_0\) is

\[
\boxed{d_0=
\frac{(S_Y^2)^2\bar X+(S_X^2)^2\bar Y}
{(S_X^2)^2+(S_Y^2)^2}.} \tag{9.1}
\]

Define its value to be \((\bar X+\bar Y)/2\) if both sample variances vanish.
The formula is finite, Borel, and equivariant under every common affine
transformation, including reflection. It is squared-precision weighting:
on positive sample variances the respective weights are proportional to
\((S_X^2)^{-2}\) and \((S_Y^2)^{-2}\).

Equations (1.2), (2.1), and (8.2) show that its worst oracle-normalized risk is
\(1+\pi/4\), with strictly smaller risk at each individual physical parameter.

For the unrestricted lower bound, take any Borel estimator \(d\). If its worst
oracle-normalized risk is infinite, the lower bound is immediate. Otherwise
call that finite worst risk \(C\ge0\). The complete constant-cap reduction
stated in Section 1 supplies \(g\in\mathcal G\) with \(L_t(g)\le C-1\) at
every interior \(t\). Section 8 forces \(z\le C-1\). Thus

\[
\boxed{V_{3,3}=1+\frac\pi4,\qquad
\sup_\theta\frac{R_\theta(d_0)}{\tau_\theta}=V_{3,3}.} \tag{9.2}
\]

This proves unrestricted minimaxity of this explicit affine estimator. It
does not prove its admissibility against all Borel competitors, nor identify
every minimizer. The value and constructive/admissibility problems at other
designs retain their own obligations.

<a id="pair-inheritance-corollary"></a>

### 9.1. Inheritance by designs containing two size-three groups

Consider any finite collection of independent normal samples with common mean
\(\mu\), positive variances \(\sigma_i^2\), and sizes \(n_i\ge2\). Its oracle
variance is \(\tau=(\sum_i n_i/\sigma_i^2)^{-1}\). If two distinct groups have
sizes three, then its unrestricted all-Borel oracle-normalized minimax value
is at least \(1+\pi/4\), including when that value is infinite.

This is an exact consequence of (9.2) and the existing pair-deletion theorem
`GD.N0036.d022918`, in
`GD/Module1443.lean` (the exact pair-deletion result).
That theorem has precisely the hypotheses just listed and compares the actual
all-Borel minimax values, with no multiplicative loss. Applying it to the two
size-three groups gives \(V_{3,3}\le V_{n_1,\ldots,n_k}\), as required.
No equality or explicit many-sample minimizer follows from this implication.

<a id="finite-risk-envelope-obstruction"></a>

## 10. One finite reduced certificate against both sample-mean bounds

Finite mixtures can exclude a proposed reduced risk envelope without any
strong duality assumption. If \(L_t(g)\le b(t)\) at every \(t\), then (3.3)
forces \(\mathfrak B(P)\le\int b\,dP\) for every finite mixture \(P\).

Consider the envelope

\[
b(t)=\frac{\min(t,1-t)}{\max(t,1-t)}.
\]

For the physical projective lift, (1.2) shows that this is exactly the excess
envelope equivalent to
\(R_\theta(d_g)\le\min(v_X,v_Y)\) at every parameter: divide by
\(\tau=vt(1-t)\) and subtract one.

The single finite rational mixture \(\widehat P_{19}\) already violates the
necessary average-budget inequality. Every one of its atoms is either at most
\(d_{19}\) or at least \(1-d_{19}\); hence

\[
\int b(t)\,d\widehat P_{19}(t)
\le\frac{d_{19}}{1-d_{19}}\le\frac1{19^4-1}.
\]

On the other hand, (7.6) and \(\pi>3\) give

\[
\mathfrak B(\widehat P_{19})>\frac\pi4-\frac{14}{19}
>\frac34-\frac{14}{19}=\frac1{76}
>\frac1{19^4-1}. \tag{10.1}
\]

Thus no \(g\in\mathcal G\) can meet this reduced envelope. The finite
certificate is specified by \(q=18/19\), \(j=361,\ldots,6858\), and common
atom weight \(1/12996\); it uses 12996 distinct rational atoms.

The constant-cap completeness theorem used in Section 9 does not by itself
preserve this nonconstant envelope. The next subsection supplies the required
additional argument before drawing an unrestricted conclusion.

<a id="raw-both-means-exclusion"></a>

### 10.1. Preservation of the fine cap and unrestricted exclusion

The argument below proves that at design \((3,3)\) there is no Borel estimator \(d\) such that

\[
R_\theta(d)\le\min(\sigma_X^2/3,\sigma_Y^2/3)
\quad\text{for every }\theta. \tag{10.2}
\]

Here is the complete additional cap argument. It uses the existing physical
weak-cap action and its fixed-point theorem, while checking the new cap's
hypotheses explicitly. More generally let \(m,n\ge2\), and put
\(b_\theta=\min(\sigma_X^2/m,\sigma_Y^2/n)\). This positive finite budget is
independent of location, invariant under reflection, and satisfies

\[
b_{(b+a\mu,a\sigma_X,a\sigma_Y)}=a^2b_\theta\quad(a>0),
\qquad b_\theta\le2\tau_\theta. \tag{10.3}
\]

Suppose a Borel rule meets this budget. Work in the real Hilbert space
\(H=L^2(P_{\theta_*})\), where the reference normal law has mean zero and
positive variances. All physical normal laws are mutually absolutely
continuous, so their extended risks are well-defined on reference equivalence
classes. Define

\[
\mathcal K=\{p\in H:R_\theta(p)\le b_\theta\text{ for every }\theta\}.
\]

The assumed rule has finite reference risk and gives an element of
\(\mathcal K\). Squared-loss convexity makes \(\mathcal K\) convex. Each risk
sublevel is norm closed: from an \(L^2(P_{\theta_*})\)-convergent sequence,
take a subsequence converging reference-almost everywhere; the same set has
full measure for every physical law, and Fatou's lemma proves all the risk
inequalities for the limit. Thus \(\mathcal K\) is norm closed and convex,
hence weakly closed. The reference constraint bounds
\(\|p\|_H^2=R_{\theta_*}(p)\le b_{\theta_*}\). Hilbert-space reflexivity
therefore makes \(\mathcal K\) weakly compact. Finally, (10.3) embeds it in
the existing oracle cap of constant two; in particular every class in it has
finite risk at every parameter.

For a positive affine transformation \(h:x\mapsto b+ax\), use the physical
transport

\[
(T_hp)(x)=b+a\,p(h^{-1}x).
\]

Its exact risk identity is
\(R_{h\theta}(T_hp)=a^2R_\theta(p)\). Equation (10.3) therefore shows that
\(T_h\mathcal K\subseteq\mathcal K\); the inverse transport gives equality.
The established weak action on the oracle cap of constant two restricts to
\(\mathcal K\). It is continuous for each \(h\), preserves convex
combinations, and satisfies the group multiplication law. These are exactly
`GD.N0232.N0720.N1258.d015537`, `GD.N0232.N0720.N1258.d015540`, and
`GD.N0232.N0720.N1258.d015539` from
`GD/Module0979.lean`,
restricted to this invariant subset. Its underlying norm bound is the one
already checked above.

Apply the existing theorem
`GD.N0230.N0664.d001257` to this nonempty
weakly compact convex invariant set and these restricted actions. It gives a
class \(p\in\mathcal K\) fixed by every \(T_h\). This is the same physical
engine used in `GD.N0095.d023061`
and `GD.N0020.d030257`; here the
explicitly verified set is \(\mathcal K\), rather than either source's
particular intersection. The point of using the existing cap-relative action
is that no bounded affine transport on the entire Hilbert space is assumed.

The exact representative-repair theorem
`GD.N0232.N0720.N1214.d014271`
in `GD/Module0916.lean`
now supplies a Borel representative \(e\) that is positive-affine-equivariant
everywhere and equal to the selected class almost everywhere under every
physical law. Its hypotheses hold because \(p\) lies in the finite oracle
cap, all its transported classes have finite reference \(L^2\) norm, and all
of them equal \(p\). Thus \(e\) is finite-risk at every parameter and still
satisfies \(R_\theta(e)\le b_\theta\).

At this point apply the literal theorem
`GD.N0024.N0271.d028029`
in `GD/Module1643.lean`.
Its hypotheses are \(m,n\ge2\), a finite-risk Borel everywhere-affine input
rule, a finite extended-real budget invariant under reflection, and the risk
inequality for that budget. Take the budget to be the finite extended-real
image of \(b_\theta\). Equation (10.3) and the construction of \(e\) check all
these conditions. The theorem first takes a sufficient-summary representative,
then averages reflection, represents it projectively, and clips the
coefficient; every step preserves the specified budget. It yields a bounded
Borel projective coefficient \(g\) with
\(R_\theta(d_g)\le b_\theta\) for every parameter.

Specialize to \(m=n=3\). On the normalized section \(v=1\), the two mean
variances are \(1-t,t\) and \(\tau=t(1-t)\). Equation (1.2) forces

\[
L_t(g)\le\frac{\min(t,1-t)}{t(1-t)}-1
=\frac{\min(t,1-t)}{\max(t,1-t)}.
\]

This contradicts the single finite certificate (10.1). Hence (10.2) is
impossible even without an admissibility or strict-improvement requirement.
The new fine-cap assembly and this unrestricted exclusion have paper-proof
evidence; the cited existing affine-budget theorem is not being represented
as an already compiled arbitrary-raw-input theorem.

<a id="relative-gain-upper-bound"></a>

### 10.2. A relative-risk gain bound

Let \(d_{\mathrm{ref}}=\bar Y+Du\) be the inverse-sample-variance weighted
reference estimator. Equations (1.2)–(1.3) give

\[
L_t(u)=\int_0^1
\left(\frac{u-t}{t+(1-2t)u}\right)^2du<1.
\]

Indeed,
\([t+(1-2t)u]^2-(u-t)^2=4t(1-t)u(1-u)>0\) for interior \(t,u\).
Thus \(R_\theta(d_{\mathrm{ref}})/\tau_\theta<2\) everywhere. If any Borel
rule has a uniform relative-risk cap
\(R_\theta(d)\le cR_\theta(d_{\mathrm{ref}})\) for finite \(c\ge0\), then
it has oracle cap \(2c\). Equation (9.2) forces
\(c\ge(1+\pi/4)/2\).

Consequently the optimal uniform proportional improvement

\[
\Gamma_{3,3}=\sup_{d\ \mathrm{Borel}}\inf_\theta
\left[1-\frac{R_\theta(d)}{R_\theta(d_{\mathrm{ref}})}\right]
\]

satisfies

\[
\boxed{\Gamma_{3,3}\le\frac12-\frac\pi8.} \tag{10.4}
\]

To see that this covers the infimum definition as well, a rule with finite
worst relative risk has exactly such a cap \(c\), while infinite worst
relative risk gives improvement \(-\infty\). No equality or strictness of
the bound in (10.4) is asserted.

## 11. Refined rate and the scope of the moving-measure rigidity

Retain the sharper estimates

\[
1-\rho_N\le\frac7{2N^2(1-N^{-4})},\quad
\lambda_N\le\frac{6\log N}{N(N-1)},\quad
E_N\le\frac2{(N-1)(1-N^{-4})},\quad
z-J_N\le2N^{-2}+zN^{-3}+8zN^{-4}.
\]

Equation (7.5) then gives

\[
\begin{aligned}
\Delta_N\le{}&\frac{2z}{N}
+\frac2{(N-1)(1-N^{-4})}
+\frac{6z\log N}{N(N-1)}\\
&+\frac4{N^2}+\frac{7z}{2N^2(1-N^{-4})}
+\frac z{N^3}+\frac{23z}{2N^4}.
\end{aligned} \tag{11.1}
\]

Therefore

\[
0\le\liminf_N N\Delta_N\le\limsup_N N\Delta_N
\le2z+2=\frac\pi2+2. \tag{11.2}
\]

Let \(\mathcal M=\{g\in\mathcal G:\sup_tL_t(g)\le z\}\), and let the finite
measure \(\mu_N\) have density \(M_0(\widehat P_N;u,s)\) on \(\Omega\).
The exact completion (3.3) gives, for every \(g\in\mathcal M\),

\[
\|g-g_{\widehat P_N}\|_{L^2(\mu_N)}^2
=\int L_t(g)\,d\widehat P_N(t)-B_N
\le\Delta_N<\frac{14}{N}\quad(N\ge16). \tag{11.3}
\]

For \(g,h\in\mathcal M\), the squared triangle inequality yields

\[
\|g-h\|_{L^2(\mu_N)}^2<\frac{56}{N}. \tag{11.4}
\]

These are bounds in varying measures. They do not imply equality in any fixed
\(L^2\) space or equality almost everywhere on \(\Omega\). In fact, on each
compact subset of \(\Omega\), the explicit formula gives uniformly
\(K_t=O(t^{3/2})\) and \(K_{1-t}=O(t^{3/2})\) as \(t\downarrow0\). All small
atoms in \(\widehat P_N\) are at most \(d_N\to0\), so the density of \(\mu_N\)
tends uniformly to zero on such a compact set. Its mass is not retained on
fixed interior compact sets. Ordinary admissibility, uniqueness, and a
generalized-Bayes representation are consequently separate questions.

<a id="formalization-boundary"></a>

## 12. Proof authority and exact source prerequisites

The complete new analytic proof is Sections 3–11 of this document, with the
explicit physical kernel derivation and upper calculation in Sections 1–2.
Its evidence class is **paper-proof**, including the physical minimax transfer
which invokes the existing complete constant-cap reduction.

The precise prerequisite sources inspected for this transfer are:

| Required fact | Source and declaration |
| --- | --- |
| Complete finite oracle-cap reduction, with the oracle term subtracted | `GD/Module1461.lean`, `GD.N0045.d023068` |
| Native probability density, before division by \(t(1-t)\) | `GD/Module1376.lean`, `GD.N0062.d022145` |
| Exact physical coefficient map | `GD/Module0940.lean`, `GD.N0232.N0720.N1425.d014720`; native bounded risk identity used in `GD/Module1461.lean` |
| Existing strict upper bound for the explicit rule | `GD/Module1902.lean`, `GD.N0010.d030852` and `GD.N0010.d030851` |
| Integral upper-bound calculation reproduced in Section 2 | `GD/Module0558.lean`, `GD.N0016.d008318` and `GD.N0016.d008320` |
| Exact pair-to-many minimax comparison | `GD/Module1443.lean`, `GD.N0036.d022918` |
| Preservation of an arbitrary finite reflection-invariant budget after affine repair | `GD/Module1643.lean`, `GD.N0024.N0271.d028029` |
| Physical cap-relative action and fixed-point assembly pattern | `GD/Module0979.lean`, `GD.N0232.N0720.N1258.d015537`, `GD.N0232.N0720.N1258.d015540`, `GD.N0232.N0720.N1258.d015539`; `GD/Module1835.lean`, `GD.N0020.d030257` |

Current verification records report the checks performed on the linked sources.

The supplied conditional formalization is retained at
`GD/Module0486.lean`; its current check is reported with the source verification results.
`GD.N0209.d007523`, `GD.N0209.d007524`, and
`GD.N0209.d007525` take the window bounds as explicit hypotheses.
`GD.N0209.d007526` proves a conditional order-theoretic consequence.
The formalization does **not** construct \(K_t\), \(\widehat P_N\),
\(\mathfrak B\), or a realization of the window-bound hypotheses for these objects. The continuum
and discretization inequalities, their concrete estimates, and the physical
minimax equality are therefore not claimed as newly kernel-checked results.
