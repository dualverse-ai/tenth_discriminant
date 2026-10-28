# Meixner moments, singular values, and Schur sums

Original section and equation numbers are retained.

The numerical contract preceding the original Section 5 is omitted. For that section assume $A>0$, $0<v<1$, $\beta<0$, $AR_0>1$, $f(1)<0$, $R\geq R_0$, $S\geq S_0$, $0<\varepsilon_-\leq J/R\leq\varepsilon_+\leq1$, and $\theta=M/(nJ)\geq\theta_->0$. Proposition 6 imposes the additional conditions stated there, including $R_0>3$. The classical references [7], [11], and [12] are listed in README.txt. The arithmetic interface is given in note 06. The final finite example explains why the sum over arbitrary orders in Proposition 5 cannot simply be replaced by the largest consecutive orders.

## 2. The matrix and a radial lemma

Let $R=KS$, with integer $K\geq2$, and put

$$
\Lambda=\{(r,s)\in\mathbb Z_{\geq0}^2:r+Ks<R\},\qquad
M=\frac{R(S+1)}2,\qquad W=\frac{R^2S}3.
$$

For nodes $u_i$ in the unit disk and orders $0\leq j<J$, define

$$
A_{(r,s),(i,j)}(L)=
\frac{(r)_{\underline j}}{R^j}e^{Lj}
u_i^{r-j}\bar u_i^{s},
$$

with zero entries when $j>r$. Here $(r)_{\underline j}$ is the falling
factorial. Every minor considered below uses all $M$ rows and $M$ selected
columns. This is the residual matrix after the common row radius and
factorial/prime-power accounting in notes 02–04. Our real diagonal weights are
devices for bounding this matrix; they do not replace the integral minor
or alter its arithmetic valuations. The normalized determinant quantity
bounded throughout is $\log|\det A_C(L)|^2/W$.

For arbitrary row prices $\lambda_{r,s}$, write
$B=\operatorname{diag}(e^{-\lambda/2})A$ and let $G_i=B_i^*B_i$ be a
node's column Gram matrix. If $C_i$ is the set of selected orders there,
Fischer and interlacing give

$$
\log|\det A_C|^2\leq
\sum_{\Lambda}\lambda_{r,s}
+\sum_i\log\det G_i[C_i,C_i].                    \tag{2.1}
$$

The determinant inequality also holds for singular minors.

**Lemma 2.** Every principal minor of a node Gram matrix is a polynomial
in $q=|u|^2$ with nonnegative coefficients.

**Proof.** The node angle is removed by diagonal unitaries in the row and
column indices. For a row set $H$ and order set $T$ of equal size, a squared
minor is

$$
e^{-\sum_H\lambda}\prod_{j\in T}\frac{e^{2Lj}}{R^{2j}}
\det[(r)_{\underline j}]_{H,T}^{2}
q^{\sum_H(r+s)-\sum_Tj}.
$$

If the factorial determinant is nonzero, one nonzero permutation term
matches each order $j$ to a row with $r\geq j$. Its exponent is therefore
a nonnegative integer. Zero determinants contribute zero. Cauchy--Binet
proves the assertion, and continuity includes $q=0$. $\square$

Thus each fixed selected node minor can first be moved to an upper radius.
We do not assert that individual eigenvalues, or the Gram matrix in Loewner
order, are monotone in $q$.

## 3. General Meixner weights

Use the rising factorial $(b)_r=b(b+1)\cdots(b+r-1)$ and choose

$$
b=AR,\quad A>0,\quad0<v<1,\qquad
e^{-\lambda_{r,s}}=\frac{(b)_r}{r!}v^r e^{-\beta s}. \tag{3.1}
$$

At a fixed node, complete the triangular row set to
$r\geq0$, $0\leq s<S$. The additional row outer products are positive
semidefinite, so this gives an upper Gram matrix. Put

$$
w=vq,\qquad B(q)=\sum_{s=0}^{S-1}(e^{-\beta}q)^s.
$$

The completed $r$-measure has total mass $(1-w)^{-b}$. Its normalized
negative-binomial distribution has monic Meixner norms and connection
coefficients

$$
\begin{aligned}
h_\ell&=\ell!(b)_\ell\frac{w^\ell}{(1-w)^{2\ell}},\\
(r)_{\underline j}
&=\sum_{\ell=0}^j\binom j\ell(b+\ell)_{j-\ell}
\left(\frac{w}{1-w}\right)^{j-\ell}P_\ell(r).
\end{aligned}                                                   \tag{3.2}
$$

These are the classical formulas [7] in monic normalization. They can also
be obtained by comparing coefficients in

$$
\mathbb E[(1+x)^r(1+y)^r]
=\left(\frac{1-w}{1-w(1+x)(1+y)}\right)^b.
$$

Factoring the denominator as
$(1-\alpha x)(1-\alpha y)-\delta xy$, with
$\alpha=w/(1-w)$ and $\delta=w/(1-w)^2$, and expanding its binomial
series gives the orthogonal factor in (3.2). This verifies its constants
without requiring an asymptotic orthogonal-polynomial result.

Choose a positive column scale $\tau$ and put

$$
\nu_j=\log(j!)+\log((b)_j)+2j\bigl(L-\log(R\tau)\bigr). \tag{3.3}
$$

Dividing column $j$ by $e^{\nu_j/2}$ changes its coefficient to
$\tau^j/\sqrt{j!(b)_j}$. Formula (3.2) shows that the completed factor
is $\sqrt{B(q)(1-vq)^{-b}}$ times the finite polynomial compression of
composition by

$$
\phi(z)=a+dz,\qquad
a=\frac{\tau v\sqrt q}{1-vq},\qquad
d=\frac{\tau\sqrt v}{1-vq},                            \tag{3.4}
$$

on the space $\mathcal H_b$ with reproducing kernel
$(1-z\bar w)^{-b}$. Its orthonormal monomials are
$\sqrt{(b)_j/j!}\,z^j$. Indeed the corresponding factor entry is

$$
\binom j\ell\sqrt{\frac{(b)_j\ell!}{j!(b)_\ell}}
a^{j-\ell}d^\ell.
$$

The triangular constraint admits a more useful completion. Put
$\delta(q)=(\log q-\beta)_+$, with $\delta(0)=0$, and
$v_q=v\exp(-\delta(q)/K)$. At row degree $r<R$, the actual conjugate-power
sum satisfies

$$
\sum_{s=0}^{S-1-\lfloor r/K\rfloor}(qe^{-\beta})^s
\leq S\exp\bigl((S-r/K)\delta(q)\bigr).               \tag{3.5}
$$

There are at most $S$ terms, and each allowed exponent is at most
$S-r/K$. Multiplying the $r$-measure by the last factor in (3.5) replaces
$v$ by $v_q$, with scalar mass $B_*(q)=S\exp(S\delta(q))$.
Extending $r$ to infinity is again a positive-semidefinite majorant.
All factor formulas remain valid with $v_q$ and $B_*$ replacing $v$ and
$B$; the original row-price sum still uses $v$. The primary bound uses
this tilted completion. The rectangular completion is retained as an
explicit comparator.

## 4. Affine composition spectrum and occupancy

**Lemma 3.** Suppose $a,d\geq0$, $d>0$, and $a+d<1$. Write

$$
U=ad,\quad V=d^2,\quad Z=1-a^2,
$$

$$
h=\frac{2U}{Z-V+\sqrt{(1-(a+d)^2)(1-(a-d)^2)}},\quad
\Gamma=\frac1{Z-Uh},\quad
\xi^2=\frac{V+Uh}{Z-Uh}.
$$

Then the squared singular values of $C_\phi$ on $\mathcal H_b$ are
$\Gamma^b\xi^{2\ell}$, $\ell\geq0$.

**Proof.** Here $0\leq h<1$, $0<\xi<1$, and
$Uh^2-(Z-V)h+U=0$. The kernel of $C_\phi C_\phi^*$ is

$$
[Z-U(z+\bar w)-Vz\bar w]^{-b}.
$$

The standard automorphism operator

$$
(W_hf)(z)=\frac{(1-h^2)^{b/2}}{(1-hz)^b}
f\left(\frac{z-h}{1-hz}\right)
$$

is unitary on $\mathcal H_b$, as follows directly by transforming the
reproducing kernel. Expanding the denominator and using the quadratic
equation for $h$ gives

$$
C_\phi C_\phi^*=\Gamma^b W_hD_{\xi^2}W_h^*,\qquad
(D_tf)(z)=f(tz).
$$

The monomial eigenvalues of $D_{\xi^2}$ are $\xi^{2\ell}$. This proves
the claim and compactness. The calculation is valid for every real $b>0$;
the analytic powers have their branch fixed at the origin. $\square$

Finite compression cannot increase singular values. Consequently a node
with $m$ selected columns has the upper cost

$$
F_q(m)=\sum_{\text{largest }m\text{ orders }j}\nu_j
+m\left[\log B(q)+b\log\frac{\Gamma}{1-vq}\right]
+m(m-1)\log\xi.                                      \tag{4.1}
$$

The selected column-price sum in (3.3) is bounded by its largest $m$
values; no assumption about which orders are selected is made.

For computation, choose $0<\xi<1$ directly and use

$$
\Gamma=\frac{1+\xi^2+\sqrt{(1-\xi^2)^2+4vq\xi^2}}2,
\qquad
\tau=\frac{\xi(1-vq)}{\Gamma\sqrt v}.                 \tag{4.2}
$$

Substitution into (3.4) gives $a+d<1$ and the spectrum in Lemma 3.
The choice can be made separately at every node and occupancy: each is
an upper bound for the same original minor. Restricting all nodes by the
sufficient global condition $\tau<v^{-1/2}-1$ loses room when $q<1$.

### 4.1 Complementary products for finite affine maps

The finite polynomial factor exists for every $a\geq0,d>0$. An affine
map that expands the disk can therefore be useful even though its infinite
composition operator is unavailable.

**Lemma 4.** Let $T_J$ be composition by $a+dz$ on the polynomials of
degree less than $J$ in $\mathcal H_b$. For $0\leq m\leq J$, set $n=J-m$.
Choose $0<r_0<1$ and define

$$
G=\frac{1+r_0^2+\sqrt{(1-r_0^2)^2+4a^2r_0^2}}2,
\qquad \sigma=\frac{d r_0}{G}.
$$

The logarithm of the product of the largest $m$ squared singular values
of $T_J$ is at most

$$
J(J-1)\log d+nb\log G+n(n-1)\log r_0-N\log\sigma,    \tag{4.3}
$$

where $N=n(2J-n-1)$ if $\sigma\leq1$, and $N=n(n-1)$ if $\sigma\geq1$.

**Proof.** The diagonal entries of $T_J$ are $d^j$, so
$\det(T_J^*T_J)=d^{J(J-1)}$. The product in question equals this
determinant times the product of the largest $n$ squared singular values
of $T_J^{-1}$. The inverse is composition by $(z-a)/d$.

Let $D_\sigma=\operatorname{diag}(\sigma^j)_{j<J}$. Then
$T_J^{-1}D_\sigma$ is composition by
$-a r_0/G+(r_0/G)z$. Since $G>(a+1)r_0$, this map sends the disk
strictly inside itself. Changing the sign of the translation does not
change singular values. Lemma 3 gives the infinite squared singular values
$G^b r_0^{2\ell}$.

Finite compression and the exterior-power inequality
$\|\bigwedge^n(XY)\|\leq\|\bigwedge^nX\|\,\|\bigwedge^nY\|$
bound the singular product of
$T_J^{-1}=(T_J^{-1}D_\sigma)D_\sigma^{-1}$.
The largest $n$ entries of $D_\sigma^{-1}$ have indices $J-n,\ldots,J-1$
when $\sigma\leq1$ and $0,\ldots,n-1$ when $\sigma\geq1$. Their squared
product contributes $-N\log\sigma$. This proves (4.3). $\square$

For the tilted node factor, choose any $\kappa>0$ and set

$$
d=\frac{\kappa}{1+\sqrt{v_q q}},\quad a=d\sqrt{v_q q},
\quad \tau=\frac{d(1-v_q q)}{\sqrt{v_q}}.             \tag{4.4}
$$

Values $\kappa>1$ give expanding finite affine maps. The original column
prices (3.3), the scalar mass, and (4.3) still bound every selected node
minor. Intersect this bound with (4.1). All choices bound the same minor.

## 5. Uniform finite-size estimates

### 5.1 Signed row sum

Let $\ell(x)=x\log x$, with $\ell(0)=0$, and define

$$
f(x)=\ell(x)-\ell(A+x)+\ell(A)-x\log v,
\qquad C=-A\log(1-v)>0.
$$

Integral comparison gives

$$
\log(r!)\leq r\log r-r+\log(r+1)+1,
$$

$$
\log((b)_r)\geq\int_0^r\log(b+t)\,dt
-\log\frac{b+r}{b-1}.
$$

For the latter, first compare with the integral over $[-1,r-1]$ and bound
the two endpoint intervals. Hence

$$
\lambda_{r,s}\leq Rf(r/R)+\beta s+\delta_R,
\quad
\delta_R=\log(R+1)+1+\log\frac{A+1}{A-1/R}.            \tag{5.1}
$$

The function $f$ is convex, $f(0)=0$, $f(1)<0$, and its minimum for
$x\geq0$ is $-C$. Thus $f\leq0$ on $[0,1]$. The exact row multiplicity
$S-\lfloor r/K\rfloor$ is at least $S(1-r/R)$; its lower bound therefore
gives an upper bound when multiplied by $f$. Moreover
$\operatorname{TV}((1-x)f(x))\leq3C$, since
$\operatorname{TV}(f)\leq2C$. A left Riemann sum differs from its integral
by at most total variation divided by $R$.

Using $\sum_\Lambda s=KS(S^2-1)/6$, the normalized row-price sum is at most

$$
U_{\rm row}=
3\int_0^1(1-x)f(x)\,dx+\frac{9C}{R_0}
+\frac\beta{2K}(1-S_0^{-2})
+\frac{3(1+S_0^{-1})}{2R_0}\delta_{R_0}.              \tag{5.2}
$$

All error terms divided by $R$ decrease above $R_0$. The integral is
elementary; antiderivatives of $x\log x$ and $x^2\log x$ give its value
in logarithms of $A$, $A+1$ and $v$.

### 5.2 Column capacities

For each upper node radius and any chosen $\tau>0$, (3.3) satisfies

$$
\frac{\nu_j}{R}\leq g(j/R)+E_{\rm col},
$$

$$
g(z)=\ell(z)+\ell(A+z)-\ell(A)
+2z\bigl(L-\log\tau-1\bigr),\qquad
E_{\rm col}=\frac{\log(R_0+1)+1}{R_0}.                \tag{5.3}
$$

Here the increasing left sum bounds $\log((AR)_j)$ above by its integral,
and $J\leq R$. The function $g$ is convex. Partition
$[0,\varepsilon_+]$ into $N_z$ bins and bound it on each bin by the larger
endpoint, then by its maximum with zero. Each bin has normalized capacity

$$c_z=\frac{\varepsilon_+}{N_z}+\frac1{R_0}.$$

Let $C_{q,\xi}(t)$ be the maximum cost of selecting mass $t$ from these
capacities and nonnegative upper costs. Every actual selection of $m$
orders is feasible at $t=m/R$. This is valid even if some exact column
prices are negative. Sorting the bin costs evaluates $C_{q,\xi}$ exactly;
it is nondecreasing.

For either the original geometric sum or the tilted mass $B_*$, we have

$$
\frac{\log B(q)}R\leq\frac{\log R_0}{R_0}
+\frac{(\log q-\beta)_+}{K}.
$$

Consequently (4.1), divided by $R^2$, is at most

$$
\mathcal F_{q,\xi}(t)=C_{q,\xi}(t)+d_{q,\xi}t
+t^2\log\xi,
$$

$$
d_{q,\xi}=A\log\frac\Gamma{1-v_q q}
+\frac{(\log q-\beta)_+}{K}
+\frac{\log R_0}{R_0}+E_{\rm col}-\frac{\log\xi}{R_0}. \tag{5.4}
$$

The last positive correction accounts for $m(m-1)$ rather than $m^2$.

### 5.3 Occupancy and radial errors

Fix a positive scalar dual $a_0$. On an occupancy cell $[l,h]$, the function
$\mathcal F_{q,\xi}(t)-a_0t$ is bounded above by

$$
C_{q,\xi}(h)
+(d_{q,\xi}-a_0)
\begin{cases}h,&d_{q,\xi}\geq a_0,\\l,&d_{q,\xi}<a_0,\end{cases}
+l^2\log\xi.                                        \tag{5.5}
$$

Intersect these whole-cell upper bounds over the fixed choices of $\xi$,
then maximize over cells and zero. Denote the result by $H(q)$. This order
of operations bounds the entire cell before choosing a spectral parameter.

The available ordered-radius bound is

$$
q_i\leq Q(i/n),\qquad
Q(t)=\left(\frac{\sqrt t+\eta}{1+\eta}\right)^2.
$$

By Lemma 2 we may first move a node to its bin's upper radius and then use
(5.5). Split $i/n$ into $N_t$ bins. Each contains at most $n/N_t+1$ nodes.
Since $H\geq0$ and

$$
\frac nS=\frac{1+1/S}{2\theta(J/R)}
\leq\frac{1+1/S_0}{2\theta_-\varepsilon_-},
$$

the normalized determinant is at most

$$
U_{\rm row}+\frac{3a_0(1+1/S_0)}2
+3\left(\frac{1+1/S_0}{2\theta_-\varepsilon_-N_t}
+\frac1{S_0}\right)\sum_{k=1}^{N_t}H(Q(k/N_t)).        \tag{5.6}
$$

The checker rounds each upper radius upward to a dyadic number; the last
radius is exactly one. Negative row-price sums were handled separately in
(5.2), so no upper count is multiplied by a negative charge.

### 5.4 Uniform complementary bound

Write $e=J/R$, $t=m/R$ and retain $G,\sigma,r_0,d$ from Lemma 4.
Define, initially with the actual $e$,

$$
\begin{aligned}
c_0&=e(A+e)\log G,\\
c_1&=-A\log G-e\bigl(2\log r_0-\log\sigma-|\log\sigma|\bigr),\\
c_2&=\log r_0-|\log\sigma|<0.
\end{aligned}                                                   \tag{5.7}
$$

Direct substitution into both branches of (4.3) gives the exact normalized
expression

$$
c_0+c_1t+c_2t^2-\frac{t\log d+(e-t)\log G}{R}.       \tag{5.8}
$$

Its last term is at most $t\max(0,-\log d)/R_0$. The leading expression
increases with $e\geq t$: its derivative is
$(A+2e)\log G-2t\log r_0$ when $\sigma\leq1$, and
$2t\log d+(A+2e-2t)\log G$ when $\sigma\geq1$.
The latter branch has $d>1$. Thus replace $e$ by
$\varepsilon_+$ in (5.7).

Let $C_{q,\tau}$ denote the column-capacity function of Section 5.2 with
the scale (4.4). The complementary node cost divided by $R^2$ is at most

$$
C_{q,\tau}(t)+c_0+(c_1+e_q)t+c_2t^2,
$$

$$
e_q=-A\log(1-v_q q)+\frac{\delta(q)}K
 +\frac{\log R_0}{R_0}+E_{\rm col}
 +\frac{\max(0,-\log d)}{R_0}.                       \tag{5.9}
$$

On a cell $[l,h]$, bound $C_{q,\tau}(t)$ by $C_{q,\tau}(h)$,
add $c_0$, evaluate $(c_1+e_q-a_0)t$ at the appropriate endpoint according
to its sign, and use $c_2l^2$. Intersect these whole-cell bounds with the
forward bounds (5.5) before maximizing over cells. The same nonnegative
$H$ and the radial formula (5.6) then apply. All errors are uniform in
$R\geq R_0$; this step introduces no large-order numerical matrix.

### 5.5 Arbitrary derivative-order sums by Schur functions

The spectral estimates can be supplemented by a finite bound for all order
selections at once. Its ingredients are the classical gamma moment
determinant, the Schur Cauchy identity [11] and Littlewood–Richardson
positivity [12]. They are combined below with the Meixner factor and uniform triangular completion; the argument does not assume that the largest consecutive orders maximize a minor.

For $b>0$ and $0<w<1$, define

$$
M_{jk}(b,w)=\sum_{r\geq0}\frac{(b)_r}{r!}w^r
(r)_{\underline j}(r)_{\underline k}.
$$

Here $(b)_r$ is rising and $(r)_{\underline j}$ is falling. Let
$G_{jk}=\mathcal B\sigma^{j+k}M_{jk}$ for $0\leq j,k<J$, where
$\mathcal B,\sigma>0$. Put

$$
c=\frac{\sigma\sqrt w}{1-w},\qquad z=(bc)^{-2}.
$$

**Proposition 5.** If $bc>1$, then for every $0\leq m\leq J$, with
$a=J-m$ and $s_*=ma+m(m-1)/2$,

$$
\sum_{\substack{T\subseteq\{0,\ldots,J-1\}\\|T|=m}}
\det G[T,T]
\leq \mathcal B^m(1-w)^{-bm}c^{2s_*}
\prod_{i=0}^{m-1}i!(b)_{2a+i}\,(1-z)^{-m^2}.       \tag{5.10}
$$

The empty product is one. The right side also bounds the product of the
$m$ largest eigenvalues of $G$, because that product is at most the
elementary symmetric sum on the left.

**Step 1: positive Meixner numerator.** The finite Meixner factor gives

$$
M_{jk}=(1-w)^{-b-j-k}(b)_j(b)_k
\sum_{\ell=0}^{\min(j,k)}
\frac{(j)_{\underline\ell}(k)_{\underline\ell}}
{\ell!(b)_\ell}w^{j+k-\ell}.
$$

Fix $T=\{j_0<\cdots<j_{m-1}\}$, write $s=\sum_{j\in T}j$, and
set $V_{\ell j}=(j)_{\underline\ell}/\sqrt{\ell!(b)_\ell}$.
Cauchy--Binet expresses

$$
(1-w)^{bm+2s}\det M[T,T]
=\prod_{j\in T}(b)_j^2
\sum_{|L|=m}\det(V_{L,T})^2 w^{2s-\sum_{\ell\in L}\ell}.
$$

A nonzero minor has a nonzero permutation term matching each $\ell$ to
an order $j\geq\ell$. Thus $\sum L\leq s$. After taking out $w^s$,
the remaining polynomial has nonnegative coefficients and is bounded by
its value at $w=1$. The terminating Vandermonde identity gives

$$
(b)_j(b)_k\sum_\ell V_{\ell j}V_{\ell k}=(b)_{j+k}.
$$

Consequently, with $D_T=\det[(b)_{j+k}]_{j,k\in T}$,

$$
\det G[T,T]\leq\mathcal B^m(1-w)^{-bm}c^{2s}D_T.  \tag{5.11}
$$

No integer restriction on $b$ is used.

**Step 2: a Schur bound for the gamma minor.** Define the partition
$\lambda_{m-i}=j_i-i$ for $0\leq i<m$. The gamma moment integral and
Andreief's identity give

$$
D_T=D_0\,\mathbb E[s_\lambda(X)^2],\qquad
D_0=\prod_{i=0}^{m-1}i!(b)_i,
$$

where $X$ has the Laguerre density proportional to
$\Delta(X)^2\prod_i X_i^{b-1}e^{-X_i}$. Its Schur average is

$$
\mathbb E[s_\nu(X)]
=s_\nu(1^m)\prod_{i=1}^m(b+m-i)_{\nu_i}.          \tag{5.12}
$$

For completeness, insert the alternant formula for $s_\nu$, apply
Andreief, factor a gamma value from each row, and evaluate the remaining
Vandermonde. This proves (5.12). It is also the Laguerre limit of [11,
equation (2.46)] at Schur parameter one.

In the Littlewood--Richardson expansion of $s_\lambda^2$, every
coefficient is nonnegative, and each occurring partition $\nu$ is
dominated by $2\lambda$. Partitions with more than $m$ parts vanish.
The vector $(b+m-i+2\lambda_i)_i$ majorizes
$(b+m-i+\nu_i)_i$. Convexity of $\log\Gamma$ on the positive axis
therefore shows that the product in (5.12) is at most its value for
$2\lambda$. Evaluating the Littlewood--Richardson expansion at $1^m$
sums the remaining dimension factors to $s_\lambda(1^m)^2$. Hence

$$
D_T\leq
\left(\prod_{0\leq i<k<m}\frac{j_k-j_i}{k-i}\right)^2
\prod_{i=0}^{m-1}i!(b)_{2j_i-i}.                  \tag{5.13}
$$

For consecutive orders $j_i=a+i$, equality holds in (5.13), and
$D_T=\prod_i i!(b)_{2a+i}$ by the monic Laguerre norms.

**Step 3: sum complementary partitions.** Put $d_i=a+i-j_i$.
Then $a\geq d_0\geq\cdots\geq d_{m-1}\geq0$, and the dimension
factor in (5.13) is $s_d(1^m)$. The ratio
$(b)_{2j_i-i}/(b)_{2a+i}$ removes $2d_i$ factors, each at least $b$.
Combining this with (5.11) gives

$$
\frac{\det G[T,T]}
{\mathcal B^m(1-w)^{-bm}c^{2s_*}\prod_i i!(b)_{2a+i}}
\leq s_d(1^m)^2 z^{|d|}.
$$

Sum over these partitions and enlarge to all partitions of length at most
$m$. The Cauchy identity [11, equation (2.44), Schur specialization] gives
$\sum_d s_d(1^m)^2z^{|d|}=(1-z)^{-m^2}$. This proves (5.10).

#### Uniform transfer to the triangular completion

Use the notation and original row prices of Sections 2–5. Set $b=AR$,
$R=KS$, $J/R=e\leq\varepsilon$, and $t=m/R$. At a node with
$q=|u|^2$, let

$$
\delta=(\log q-\beta)_+,\quad
v_* =v e^{-\delta/K},\quad w=v_*q,\quad
\mathcal B=S e^{S\delta},\quad
\sigma=\frac{e^L}{R\sqrt q}.
$$

The completed measure majorizes the triangular Gram as proved in Section 3.
The formulas below extend at $q=0$ by continuity; the radial checker uses
positive upper endpoints. Define

$$
c_0=L+\tfrac12\log v_* -\log(1-w),\quad
z=A^{-2}e^{-2c_0},\quad
I(x)=\tfrac12x^2\log x-\tfrac14x^2,
$$

with $I(0)=0$, and

$$
\begin{aligned}
g_e(t)={}&t\bigl(\delta/K-A\log(1-w)\bigr)
 +(2et-t^2)(c_0-1)\\
&+I(t)+I(A+2e-t)-I(A+2e-2t)-tA\log A
 -t^2\log(1-z).
\end{aligned}                                                   \tag{5.14}
$$

**Proposition 6.** Suppose $0<A\leq1$, $0<\varepsilon\leq1$,
$\varepsilon(A+2\varepsilon)\leq1$, $A e^{c_0}>1$, and $R\geq R_0>3$.
The logarithm of the right side of (5.10), divided by $R^2$, is at most

$$
g_\varepsilon(t)+E_0,\qquad
E_0=\frac{\varepsilon}{R_0}
\bigl(2\log R_0+2-\log\varepsilon-\log A\bigr).  \tag{5.15}
$$

**Proof.** For every nonnegative integer $i$,
$\log i!\leq i\log i-i+\log(i+1)+1$. Monotonicity also gives
$\log(b)_n\leq\int_0^n\log(b+x)\,dx$.
All $\log R$ terms cancel exactly against $c^{2s_*}$.
Replacing $2s_*/R^2=2et-t^2-t/R$ by $2et-t^2$ drops the
nonpositive term $-tc_0/R$. The mass contributes at most
$\varepsilon\log R/R$, and the factorial remainders contribute at most
$\varepsilon(\log R+1)/R$ because $i+1\leq J\leq R$.

The remaining left Riemann sum has integrand

$$
f(x)=x\log x+(A+2e-2t+x)\log(A+2e-2t+x)
-A\log A-2e+2t-2x.
$$

On $[0,t]$, its derivative is $\log[x(A+2e-2t+x)]\leq0$.
Its variation is at most
$t(1-\log t-\log A)\leq\varepsilon(1-\log\varepsilon-\log A)$.
This bounds the Riemann error by that quantity divided by $R$.
Their sum decreases for $R>3$, so evaluate it at $R_0$.
Finally

$$
\partial_e g_e(t)=2\int_0^t
\log\bigl(e^{c_0}(A+2e-2t+x)\bigr)\,dx>0,
$$

which permits replacing $e$ by $\varepsilon$.

For occupancy cells, the checker uses

$$
g_\varepsilon''(t)=
\log\frac{t(A+2\varepsilon-t)}
{e^{2c_0}(A+2\varepsilon-2t)^4(1-z)^2}.
$$

It verifies the sufficient condition
$\varepsilon(A+\varepsilon)z<A^2(1-z)^2$ at each radial endpoint.
Thus a tangent at a cell midpoint bounds $g_\varepsilon(t)-a_0t$
throughout that cell. Arb rounds each tangent bound upward to a dyadic
rational. These whole-cell bounds can be intersected with the forward
and complementary bounds before maximizing. The signed row sum, radial
counting and final occupancy dual are unchanged from Sections 5.1–5.3. The new branch introduces no
column-capacity bin error.

The sum over arbitrary orders is necessary. For the completed Meixner
Gram at $R=248$, $J=14$, $b=.12R$, $v=.8$, $q=.25$ and
$L=4.072584776803$, the minor on $\{3,5,6,\ldots,13\}$ exceeds that
on $\{4,5,6,\ldots,13\}$ by a logarithmic amount greater than
$.75147826818$. This is a finite counterexample to exact consecutive-order
maximization, not an assertion about the original triangular minor or an
asymptotic normalized gain.
