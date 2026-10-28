# Combining the arithmetic and spectral bounds

Original section and equation numbers are retained.

This extract supplies the exact scaling between the integral interpolation matrix and the matrix bounded in note 05. The arithmetic term and column debits are provided by notes 02–04 and the corresponding verification formulas. The original text permits composite products of two, three, and four factors; the main paper uses only the first two of these cases. The referenced lattice radius bound is proved in the main paper.

For the first $n$ lattice points $z_i\in\mathcal O_{-D}$, the integral
matrix is

$$
V_{(r,s),(i,j)}=\binom rj z_i^{r-j}\bar z_i^s,
\qquad 0\leq j<J.
$$

Set $\rho=\sqrt{n\sqrt D/(2\pi)}+\sqrt{D+4}/4$ and $u_i=z_i/\rho$.
The lattice bound of the main paper gives the radial majorant of Section 5.3
with $\eta=(\sqrt{D+4}/4)/\sqrt{n\sqrt D/(2\pi)}$.
Let $b(j)$ be the remaining column debit after the imported valuations
and split-prime estimates have been separated into a column-independent
arithmetic term $\mathcal A$. Their interface is

$$
W\mathcal A-2\sum_{(i,j)\in C}b(j)\leq\log|\det V_C|^2. \tag{6.1}
$$

Here $\mathcal A$ is the source's `padic - split_loss + ufd_save`, including
the ramified-prime term and the $k=2,3,4$ composite subtractions. Uniform
column refunds already charged in the source remain in $\mathcal A$.
Put $F(j)=\log(j!)-b(j)$. The source supplies $\sigma$ and $c_j$ with

$$
H(j)=j\sigma-F(j),\qquad
2\sum_{(i,j)\in C}H(j)\leq Mc_j                         \tag{6.2}
$$

for every selection $C$. It bounds and sorts the effective remainder
array, allowing at most $n$ copies of each order. Both the guaranteed
split-prime first-power floors and the higher prime-power floors enter
this array. Thus $\sigma$ is the effective slope constant, not solely a
universal prime-power sum.

With $L=\log(R/\rho)-\sigma$, exact diagonal scaling yields

$$
A_C(L)=\operatorname{diag}_{(r,s)}(\rho^{-r-s})\,
V_C\,\operatorname{diag}_{(i,j)\in C}
\bigl(j!(\rho/R)^je^{Lj}\bigr).
$$

Substitution in (6.1), followed by (6.2), gives

$$
\mathcal A\leq\frac{W_1+W_2}{W}\log\rho
+\frac{\log|\det A_C(L)|^2}{W}+\frac{Mc_j}{W},        \tag{6.3}
$$

where $W_1=2\sum_\Lambda r$ and $W_2=2\sum_\Lambda s$.
For $L_*\geq L$, column scaling gives
$|\det A_C(L)|^2=e^{-2(L_*-L)\sum_Cj}|\det A_C(L_*)|^2$,
so an upper endpoint for $L$ remains admissible even in the presence of
determinant cancellation. Lemma 2 permits the upper radial endpoints.

A uniform Meixner upper bound $U_{\rm M}$ may therefore replace the entire
source expression `unif_j_norm*slope_hi - F_lb - derivative_saving`.
Retaining the positive counting allowance gives the conservative comparison

$$
\mathcal A\leq C_{\rm common}+U_{\rm M},\qquad
C_{\rm common}=\frac{W_1+W_2}{W}\log\rho
+\frac{Mc_j+2M\log M}{W}.                            \tag{6.4}
$$

The old Fubini–Jensen and derivative savings are removed together. The
new determinant estimate is not added to either of those old savings.

## Explicit column terms and norm-loss weights

The following notation spells out the arithmetic quantities in (6.1)–(6.4).
It is a transcription of the finite formulas accompanying the derivations in
note 03. Throughout this section, the class-number-one hypothesis remains in
force. Write $M=M_{\rm tri}$, $W=W_{\rm main}$, and $P=P_{\max}$.
The small primes $p<K$ are inert. In the finite comparisons $P\geq J-1$.

Put

$$
T(N,q)=\sum_{s=0}^{N-1}(N-s)\lfloor s/q\rfloor,
\qquad w(x)=\frac{S_r(R,K,x)\log x}{KW}.
$$

The provisional arithmetic row contribution is

$$
\mathcal A_0=
\sum_{p<K}w_{\rm keep}(p)\log p
+\frac{2K}{W}\sum_{p\geq K}\sum_{a\geq1}T(S,p^{2a})\log p
+\sum_{K\leq p\leq P}w(p).
$$

All sums indexed by $p$ are over primes. Note 02 supplies $w_{\rm keep}$ and
$S_r$; terms with $p^{2a}>S$ vanish. The debit paired with this provisional
contribution is $B_0(j)=\sum_{p\leq j}\lfloor j/p\rfloor\log p$.

For a fixed discriminant, let $\mathcal P_s(D)$ be the split primes whose
primitive representatives belong to the slope window $\mathcal S$ of note 03.
Define

$$
T_s(j;D)=\sum_{p\in\mathcal P_s(D)}\lfloor j/p\rfloor\log p,
\qquad b(j)=B_0(j)-T_s(j;D).
$$

Thus, exactly,

$$
F(j)=\log(j!)-b(j)=P_2(j)+T_s(j;D),\qquad
P_2(j)=\sum_{p}\sum_{a\geq2}\lfloor j/p^a\rfloor\log p.
$$

This is the $F$ in (6.2). The word “slope” refers to the chosen window, not to
an additional algebraic condition on a prime. Both $P_2$ and $T_s$ are
nondecreasing in $j$.

For the row loss, a split prime has the additional conjugate-variable credit

$$
s(x)=\frac{2K}{W}\sum_{a\geq1}T(S,x^{2a-1}).
$$

When its representative is outside the slope window, its first-power column
refund can be bounded uniformly over the selected columns. If $M=nt+r$,
$0\leq r<n$, put

$$
C(x)=n\sum_{j=0}^{t-1}\lfloor j/x\rfloor+r\lfloor t/x\rfloor.
$$

Every selection of $M$ columns satisfies
$\sum_C\lfloor j/x\rfloor\geq C(x)$: fill the smallest available orders first.
Let $\iota=1$ mean that the representative is in the slope window. The loss
at a split prime $p$ is bounded by

$$
\ell(p,\iota)=
\left[w(p)-s(p)\log p-(1-\iota)\frac{2C(p)\log p}{W}\right]_+.
$$

The refund is charged here only when it has not already been placed in
$T_s(j;D)$. For a norm interval $a\leq p\leq b$, valid endpoint bounds are

$$
\begin{aligned}
\ell^+(a,b,\iota)
 &=\left[w(a)-s(b)\log a-(1-\iota)\frac{2C(b)\log a}{W}\right]_+,\\
\ell^-(a,b,\iota)
 &=\left[w(b)-s(a)\log b-(1-\iota)\frac{2C(a)\log b}{W}\right]_+.
\end{aligned}
$$

These follow from the monotonicity of $w$, $s$, and $C$ for arguments at least
$3$. For an upper loss, use $\iota=1$ only for a candidate entirely in
$\mathcal S$. For a composite correction, the corresponding choice $\iota=1$
requires the product-inclusion test in note 03; otherwise use $\iota=0$.
The clipping of norm intervals to $[X_{\rm lo}+1,P]$ in the finite enumeration
only enlarges the possible-prime upper bound.

The ramified prime is handled separately. With
$e(x)=2K\sum_{a\geq1}T(S,x^{2a})/W$, its interval loss is at most

$$
\ell^+_{\rm ram}(a,b)=
\frac12\left[w(a)+e(a)\log b-\frac{2C(b)\log a}{W}\right]_+.
$$

The factor $1/2$ comes from the ramified ideal valuation in note 02, rather
than the doubled inert-prime contribution. The ramified representative is
excluded from $\mathcal S$.

Let $L_{\rm norm}$ be the sum of $\ell^+$ over the non-ramified primitive
norm candidates, together with $\ell^+_{\rm ram}$ for the ramified candidate.
Let $C_k$ be the sum of $\mu\ell^-(m_{\rm lo},m_{\rm hi},\iota)$ over the
certified $k$-factor product classes wholly below $P$. The multiplicity $\mu$
and endpoint tests are those in note 03. Then an admissible arithmetic term is

$$
\mathcal A=\mathcal A_0-L_{\rm norm}+C_2+C_3.
$$

Further valid composite corrections may be discarded. This is why products
of four factors need not contribute to the arithmetic lower bound in the main
paper. The slope window itself has cutoff below $M_{\rm lo}^4$, so its
composite terms have at most three factors, as required in the next formulas.

## Interval slopes and the column remainder

For each candidate in $\mathcal S$, write $[a,b]$ for its norm interval.
Let $\mathcal C_{\rm out}$ be the list of possible two- and three-factor
composite product classes with $m_{\rm lo}\leq q_{\rm cap}$, with their
multiplicities. The enumeration in note 03 includes every composite that
can occur in $\mathcal S$. Let $\mathcal C_{\rm in}$ contain those entries
whose factors are guaranteed and whose product-inclusion test proves that
they stay in $\mathcal S$ throughout the interval. Thus the first list can
be used for a subtraction in a lower bound, and the second for a subtraction
in an upper bound.

With $\sigma_{pp}=\sum_{p,a\geq2,\ p^a\leq J-1}\log p/p^a$, set

$$
\begin{aligned}
\sigma_-&=\sigma_{pp}+\sum_{[a,b]\in\mathcal S}\frac{\log a}{b}
 -\sum_{\mathcal C_{\rm out}}\mu\frac{\log m_{\rm hi}}{m_{\rm lo}},\\
\sigma_+&=\sigma_{pp}+\sum_{[a,b]\in\mathcal S}\frac{\log b}{a}
 -\sum_{\mathcal C_{\rm in}}\mu\frac{\log m_{\rm lo}}{m_{\rm hi}},\\
T_-(j)&=\sum_{[a,b]\in\mathcal S}\lfloor j/b\rfloor\log a
 -\sum_{\mathcal C_{\rm out}}\mu\lfloor j/m_{\rm lo}\rfloor\log m_{\rm hi}.
\end{aligned}
$$

Then $T_-(j)\leq T_s(j;D)$, and $\sigma_-$ and $\sigma_+$ enclose
$\sigma_{pp}+\sum_{p\in\mathcal P_s(D)}\log p/p$.
Choose $\sigma=\sigma_-$ in (6.2), rounding downward in the numerical
calculation. The spectral comparison uses
$L\leq\log(R/\rho_{\rm lo})-\sigma_-$.
The upper slope $\sigma_+$ is also used when a lower derivative slope is
needed for the entrywise radial estimate.

For completeness, the finite calculation groups derivative orders into
blocks of at most $32$. Let $j_0=32b$ and $j_1=\min(J,32b+32)$.
The checked slopes satisfy $\sigma_-\geq0$. For $j_0\leq j<j_1$,

$$
H(j)=j\sigma_--F(j)
\leq (j_1-1)\sigma_--P_2(j_0)-T_-(j_0)=:H_b^+.
$$

This uses monotonicity of the actual $F$, even if $T_-$ is not monotone.
Assign $H_b^+$ to each order in its block, sort these $J$ upper bounds as
$h_{(1)}\geq\cdots\geq h_{(J)}$, and again write $M=nt+r$. The constant

$$
c_j=\frac2M\left(n\sum_{i=1}^t h_{(i)}+r h_{(t+1)}\right)
$$

satisfies (6.2) for every selected minor. If $r=0$, the final summand is
omitted. Directed rounding enlarges this upper bound.

The computational names `padic`, `split_loss`, `ufd_save`, `sigma2_lo`,
`const_j`, and `slope_j_hi` correspond respectively to $\mathcal A_0$,
$L_{\rm norm}$, $C_2+C_3$ (with any retained further corrections),
$\sigma_-$, $c_j$, and the upper endpoint for $L$ above. These definitions give the arithmetic interface in (6.1).
