# Inert and ramified prime divisibility

Original section and equation numbers are retained.

The setting is $−D$ a fundamental discriminant of class number one, $D>163$ prime with $D≡3\pmod 8$, and $\mathcal O_K=\mathbb Z[(1+\sqrt{-D})/2]$. The elementary reduction to this setting and the inertness of primes $p\leq(D-3)/4$ are proved in the main paper. The symbol $K$ also denotes the integer slope of the triangle in the original notation; its use as a field subscript should not be confused with that slope. Triangle parameters are defined in note 01. Split primes are treated in note 03. The displayed $w_{\rm keep}$ is normalized by $W_{\rm main}$, and $\theta=M_{\rm tri}/(nJ)$.

**Lemma 2.2 (Maximal-Order Frobenius Congruence Including $p = 2$).** *Let $D \equiv 3 \pmod{8}$ be prime, $\mathcal{O}_K = \mathbb{Z}[\omega]$, and let $p \geq 2$ be any prime that is inert in $\mathcal{O}_K$. Define $\psi_1(z, z') := z^p - z'$ and $\psi_2(z) := z^{p^2} - z$. Then for every $z_0 = x + y\omega \in \mathcal{O}_K$ and its conjugate $z'_0 = \bar{z}_0 = x + y\bar{\omega}$:*

$$
\psi_1(z_0, z'_0) = z_0^p - z'_0 \in p\mathcal{O}_K, \qquad \psi_2(z_0) = z_0^{p^2} - z_0 \in p\mathcal{O}_K.
$$

*Proof.* Since $p$ is unramified and inert in $\mathcal{O}_K$, the quotient $\mathcal{O}_K / p\mathcal{O}_K$ is the finite field $\mathbb{F}_{p^2}$ of $p^2$ elements, and complex conjugation $z \mapsto \bar{z}$ induces the non-trivial Galois automorphism $\text{Frob}_p(z) = z^p$ of $\mathbb{F}_{p^2} / \mathbb{F}_p$. Explicitly, for $p = 2$, since $D \equiv 3 \pmod{8}$, the integer $m := \frac{D+1}{4}$ is odd and $\omega^2 = \omega - m \equiv \omega - 1 = -\bar{\omega} \equiv \bar{\omega} \pmod{2\mathcal{O}_K}$. Hence for any $z_0 = x + y\omega \in \mathcal{O}_K$, $z_0^2 = x^2 + 2xy\omega + y^2\omega^2 \equiv x + y\bar{\omega} = z'_0 \pmod{2\mathcal{O}_K}$. Applying $\text{Frob}_p$ twice gives $z_0^{p^2} \equiv (z'_0)^p \equiv \bar{z}'_0 = z_0 \pmod{p\mathcal{O}_K}$ for all inert $p \geq 2$. $\square$

### 4.1 Exact Triangle $h_1$ Identity and Right-Subtriangle Parameterization

For each inert prime $p \leq X$ and each bidegree $(r, s) \in \Lambda_{\text{tri}} = \{r + Ks < KS = R\}$, define the primary Frobenius exponent

$$
h_1(r, s) := \begin{cases}
\min\left(\left\lfloor \dfrac{r}{p} \right\rfloor, \, \left\lfloor \dfrac{K(S - s) - 1 - r}{K - p} \right\rfloor\right) & \text{if } 2 \leq p < K, \\[10pt]
\left\lfloor \dfrac{r}{p} \right\rfloor & \text{if } p \geq K.
\end{cases}
$$

**Lemma 4.1 (Exact Triangle $h_1$ Identity and Right-Subtriangle Parameterization).** *For every integer $1 \leq p < K$:*

1. *The sum of $2h_1(r, s)$ over $\Lambda_{\text{tri}}$ is independent of $p$ and equals $W_2$ identically:*
   $$
   2 \sum_{(r,s)\in\Lambda_{\text{tri}}} h_1(r, s) = \frac{R(S^2 - 1)}{3} = W_2.
   $$
2. *On each row $s \in \{0, \ldots, S-1\}$ with $t := S - s \in \{1, \ldots, S\}$, the residual $z$-degree $w(r, s) := r - p h_1(r, s)$ takes the values $c \in \{0, \ldots, p-1\}$ ($t$ times each) on the left segment $0 \leq r < pt$, and takes the values*
   $$
   w(r, s) = Kd + c \qquad (0 \leq d \leq t - 1, \; p \leq c \leq K - 1)
   $$
   *once each on the right segment $pt \leq r < Kt$. Across all of $\Lambda_{\text{tri}}$, each value $Kd + c$ ($0 \leq d \leq S-1$, $p \leq c \leq K-1$) occurs with exact multiplicity $S - d$.*

*Proof.* (1) Fix $s \in \{0, \ldots, S-1\}$ and let $t = S - s \in \{1, \ldots, S\}$. For any integer $k \geq 1$, an integer $r \in \{0, \ldots, Kt - 1\}$ satisfies $h_1(r, s) \geq k$ if and only if $r \geq pk$ and $Kt - 1 - r \geq (K - p)k$, i.e., $pk \leq r \leq Kt - 1 - (K - p)k$. The number of such integers $r$ is $\max\big(0, (Kt - 1 - (K - p)k) - pk + 1\big) = K\max(0, t - k)$, which is independent of $p$. Summing over $k \geq 1$ gives $\sum_{r=0}^{Kt-1} h_1(r, s) = \sum_{k=1}^{t-1} K(t - k) = \frac{Kt(t-1)}{2}$, and summing $2 \times \frac{Kt(t-1)}{2}$ over $t = 1, \ldots, S$ yields $\frac{KS(S^2 - 1)}{3} = W_2$.

(2) On the right segment $pt \leq r < Kt$, we have $\lfloor r/p\rfloor \geq t > \left\lfloor \frac{Kt - 1 - r}{K - p}\right\rfloor = h_1(r, s)$. Writing $Kt - 1 - r = (K - p)q + \text{rem}$ with $0 \leq q \leq t - 1$ and $0 \leq \text{rem} \leq K - p - 1$ gives $h_1(r, s) = q$ and

$$
r - p h_1(r, s) = \big(Kt - 1 - (K - p)q - \text{rem}\big) - pq = K(t - 1 - q) + (K - 1 - \text{rem}) = Kd + c,
$$

where $d := t - 1 - q \in \{0, \ldots, t-1\}$ and $c := K - 1 - \text{rem} \in \{p, \ldots, K-1\}$. Summing over $t \in \{d+1, \ldots, S\}$ gives multiplicity $S - d$. $\square$

### 4.2 Exact Quadratic Floor Sum $S_r(R, K, p)$, Bernoulli-3 Expansion, and Over-Scaling $R = c_R X$

For primes $p \geq K$, replacing $z^p$ by $-z'$ decreases $r + Ks$ by $p - K \geq 0$, so $h_1(r, s) = \lfloor r/p\rfloor$ has zero top-boundary truncation on $\Lambda_{\text{tri}}$. Because $R = KS$ is a multiple of $K$, for each $r \in \{0, \ldots, R-1\}$, writing $r = Kd + c$ with $d = \lfloor r/K\rfloor \in \{0, \ldots, S-1\}$ and $c = r \bmod K \in \{0, \ldots, K-1\}$ shows that the exact number of $s \in \{0, \ldots, S-1\}$ with $(r, s) \in \Lambda_{\text{tri}}$ is

$$
\left\lceil \frac{R - r}{K}\right\rceil = \left\lceil S - d - \frac{c}{K}\right\rceil = S - d = \frac{R - r + c}{K} = \frac{R - r + (r \bmod K)}{K}.
$$

**Lemma 4.2 (Exact Quadratic Floor Sum $S_r(R, K, p)$, Strict Monotonicity of $w_r(p)\log p$, and Bernoulli-3 Expansion).** *For any integers $R = KS \geq 1$ and $p \geq 1$, let $q := \lfloor R/p\rfloor$, $r_0 := R - qp \in \{0, \ldots, p-1\}$, and $\theta_p := r_0 / p \in [0, 1)$, and define $\Sigma_{\text{tri}}(R, p) := \sum_{r=0}^{R-1}\lfloor r/p\rfloor(R - r)$ and $S_r(R, K, p) := 2\Sigma_{\text{tri}}(R, p) + (K - 1)\sum_{r=0}^{R-1}\lfloor r/p\rfloor$. Then:*

1. *For every integer $p \geq 1$, summing over $m = 1, \dots, q$ with $q = \lfloor R/p\rfloor$ and $c_m := mp \bmod K \in \{0, \dots, K-1\}$ gives the exact remainder identity*
   $$
   2K\sum_{(r,s)\in\Lambda_{\text{tri}}} \left\lfloor\frac{r}{p}\right\rfloor = 2\sum_{m=1}^q \sum_{r=mp}^{R-1}\big(R - r + (r \bmod K)\big) = S_r(R, K, p) + \sum_{m=1}^q c_m(K - c_m),
   $$
   *where $S_r(R, K, p) := 2\Sigma_{\text{tri}}(R, p) + (K - 1)\sum_{r=0}^{R-1}\lfloor r/p\rfloor = \sum_{m=1}^q (R - mp)(R + K - mp) = A_q - B_q p + C_q p^2$ ($A_q := qR(R + K)$, $B_q := \frac{q(q+1)}{2}(2R + K)$, $C_q := \frac{q(q+1)(2q+1)}{6}$). Since $c_m(K - c_m) \geq 0$ for all $m$, this proves $2\sum_{(r,s)\in\Lambda_{\text{tri}}} \lfloor r/p\rfloor \geq \frac{1}{K} S_r(R, K, p)$ for all $p \geq K$ with an explicit, strictly non-negative remainder.*
2. *Considered as a piecewise polynomial on $(0, \infty)$ with $q = \lfloor R/p\rfloor$, $S_r(R, K, p)$ is continuous at every knot $p = R/q$ (where $(R - qp)(R + K - qp) = 0$) and satisfies on each interval $p \in \big(\frac{R}{q+1}, \frac{R}{q}\big]$ ($q \geq 1$, $r_0 = R - qp \in [0, p)$) the exact derivative identity*
   $$
   -\frac{d}{dp}\Big[p \cdot S_r(R, K, p)\Big] = 2 B_q p - 3 C_q p^2 - A_q = q\left(\frac{q - 1}{2}p^2 + r_0(2p - r_0) + K(p - r_0)\right) > 0.
   $$
   *Since both $p \mapsto p \cdot S_r(R, K, p)$ and $p \mapsto \frac{\log p}{p}$ are positive and strictly decreasing on $[3, R]$, their product $w_r(p)\log p := \frac{S_r(R, K, p)\log p}{K W_{\text{main}}}$ is strictly decreasing on $[3, R]$ (and $0$ on $[R, \infty)$).*
3. *Expanding in $\theta_p = r_0 / p \in [0, 1)$ gives $\Sigma_{\text{tri}}(R, p) = \frac{R^3}{6p} - \frac{R^2}{4} + \frac{R^2}{4p} + \frac{pR}{12} - \frac{R}{4} - \frac{p^2}{12}\theta_p(1 - \theta_p)(1 - 2\theta_p) + \frac{p}{4}\theta_p(1 - \theta_p)$ and the analytical Bernoulli-3 lower bound*
   $$
   w_r(p) = \frac{S_r(R, K, p)}{K W_{\text{main}}} \geq \frac{1}{p} - \frac{3}{2R} + \frac{3K}{2Rp} + \frac{p}{2R^2} - \frac{3K}{2R^2} - \frac{p^2}{12\sqrt{3} R^3}.
   $$

*Proof.* Writing $\lfloor r/p\rfloor = \sum_{m=1}^q \mathbf{1}_{r \geq mp}$ and exchanging summation order gives $2K\sum_{(r,s)\in\Lambda_{\text{tri}}}\lfloor r/p\rfloor = 2\sum_{m=1}^q \sum_{r=mp}^{R-1}(R - r + (r \bmod K))$. For each $m$, the inner sum over $r \in [mp, R-1]$ has length $R - mp$, which partitions into $\lfloor (R - mp)/K\rfloor$ full blocks of length $K$ (where $\sum_{c=0}^{K-1} c = \frac{K(K-1)}{2}$) plus a boundary block of length $(R - mp) \bmod K = (K - c_m) \bmod K$ starting at $c_m$, where the sum of $r \bmod K$ exceeds the block average $\frac{K-1}{2}$ by exactly $\frac{c_m(K - c_m)}{2}$. Summing across all $m$ yields $2\sum_{m=1}^q \frac{(R - mp)(R - mp + 1)}{2} + (K - 1)\sum_{m=1}^q (R - mp) + \sum_{m=1}^q c_m(K - c_m) = S_r(R, K, p) + \sum_{m=1}^q c_m(K - c_m)$, proving (1). Substituting $R = qp + r_0$ into $2 B_q p - 3 C_q p^2 - A_q$ yields $q(q+1)K p - q(qp + r_0)K = qK(p - r_0)$ for the $K$-linear part and $q\big(2(q+1)(qp + r_0)p - \frac{(q+1)(2q+1)}{2}p^2 - (qp + r_0)^2\big) = q\big(\frac{q-1}{2}p^2 + r_0(2p - r_0)\big)$ for the $K = 0$ part, proving (2). Substituting $q = \frac{R - p\theta_p}{p}$ and $|\theta_p(1-\theta_p)(1-2\theta_p)| \leq \frac{1}{6\sqrt{3}}$ gives (3). $\square$

Notice three crucial features of Lemma 4.2: first, for finite prime sums and norm intervals $[p_{\text{lo}}, p_{\text{hi}}] \subset [3, \infty)$, Part (1) and Part (2) give the exact quadratic weight $w_r(p) = \frac{A_q - B_q p + C_q p^2}{K W_{\text{main}}}$ (summable in $O(\sqrt{R})$ operations by grouping primes with identical $q = \lfloor R/p\rfloor$) and the exact endpoint enclosure $w_r(p_{\text{hi}})\log p_{\text{hi}} \leq w_r(p)\log p \leq w_r(p_{\text{lo}})\log p_{\text{lo}}$; second, in the analytical Bernoulli-3 expansion of Part (3), the floor loss on $\Lambda_{\text{tri}}$ is $-\frac{3}{2R}$ accompanied by $+\frac{3K}{2Rp}$; third, choosing $R = K \lfloor c_R X / K\rfloor \approx c_R X$ with $c_R = 2.3 > 1$ reduces the floor loss $\frac{3}{2R}\sum_{p \leq X} \log p \approx \frac{1.5}{c_R}$ by a factor of $2.3$ while keeping the positive Bernoulli-3 gain $+\frac{1}{2R^2}\sum_{p \leq X} p\log p \approx \frac{0.25}{c_R^2}$.

### 4.3 Biconjugate $\mathbb{F}_{p^2}$-Frobenius Basis, Pure-$z'$ Tower on $T_{\text{bot}}(L_0)$, and Unified Valuation

For every inert prime $p \geq 2$, define the Artin–Schreier–Witt integer polynomial tower $F_\ell(z') \in \mathbb{Z}[z']$ ($\ell \geq 1$) in the conjugate variable $z'$ alone by $F_1(z') := (z')^{p^2} - z'$ and $F_{\ell+1}(z') := F_\ell(z')^{p^2} - p^{\nu_\ell(p^2 - 1)} F_\ell(z')$, where $\nu_\ell := \frac{p^{2\ell} - 1}{p^2 - 1}$. By Lemma 2.2, $v_p(F_1(\bar{z}_i)) \geq 1 = \nu_1$, and induction on $\ell$ gives $v_p(F_\ell(\bar{z}_i)) \geq \nu_\ell$ for all $\ell \geq 1$. Writing the base-$p^2$ digits of $s \geq 0$ as $d_0 := s - p^2\lfloor s/p^2\rfloor$ and $d_\ell := \lfloor s/p^{2\ell}\rfloor - p^2\lfloor s/p^{2\ell+2}\rfloor$ ($\ell \geq 1$), define $B_s^{(p)}(z') := \prod_{\ell \geq 1} F_\ell(z')^{d_\ell} \in \mathbb{Z}[z']$ (monic of degree $p^2\lfloor s/p^2\rfloor$ in $z'$ alone, with $v_p(B_s^{(p)}(\bar{z}_i)) \geq \sum_{\ell \geq 1} d_\ell \nu_\ell = \sum_{\ell \geq 1} \lfloor s / p^{2\ell}\rfloor$) and $A_s^{(p)}(z') := (z')^{d_0} B_s^{(p)}(z') \in \mathbb{Z}[z']$.

For each inert prime $2 \leq p < K$, $(r, s) \in \Lambda_{\text{tri}}$, and integer cut $L_0 \in \{0, \ldots, S\}$ partitioning the right subtriangle $\{r \geq p(S - s)\}$ into $T_{\text{top}}(L_0) := \{1 \leq S - d \leq L_0\}$ and $T_{\text{bot}}(L_0) := \Lambda_{\text{tri}} \setminus T_{\text{top}}(L_0)$, set $m(r, s) := \left\lfloor \frac{r - p h_1(r, s)}{p^2}\right\rfloor$, $r_0 := r - p h_1(r, s) - p^2 m(r, s) \geq 0$, $u(s) := \lfloor s/p\rfloor \bmod p \in \{0, \ldots, p-1\}$, $M(r, s) := m(r, s) + \lfloor s/p\rfloor$, and $M_{\text{bot}}(r, s) := m(r, s) + u(s)$, and define the biconjugate $p$-adapted basis polynomial

$$
P_{r,s}^{(p)}(z, z') := \begin{cases}
z^{r_0} \big(z^{p^2} - z\big)^{m(r,s)} \big(z^p - z'\big)^{h_1(r,s)} (z')^{s \bmod p} \big((z')^p - z\big)^{\lfloor s/p\rfloor} & \text{if } (r, s) \in T_{\text{top}}(L_0), \\[8pt]
z^{r_0} \big(z^{p^2} - z\big)^{m(r,s)} \big(z^p - z'\big)^{h_1(r,s)} (z')^{s \bmod p} \big((z')^p - z\big)^{u(s)} B_s^{(p)}(z') & \text{if } (r, s) \in T_{\text{bot}}(L_0),
\end{cases}
$$

while for $p \geq K$ we set $P_{r,s}^{(p)}(z, z') := z^{r \bmod p} (z^p - z')^{\lfloor r/p\rfloor} A_s^{(p)}(z')$. Under the total order $\prec_p$ on $\Lambda_{\text{tri}}$ sorted lexicographically by $(pr + s, \, s)$, replacing $z^{p^2} \mapsto z$ decreases $pr + s$ by $p(p^2 - 1)$, replacing $z^p \mapsto z'$ decreases $pr + s$ by $p^2 - 1$ while staying inside $\Lambda_{\text{tri}}$ by the definition of $h_1(r, s)$, replacing $(z')^p \mapsto z$ preserves $pr + s$, decreases $s$ by $p$, and changes $r + Ks$ by $1 - Kp < 0$, and lower terms of $B_s^{(p)}(z')$ decrease $s$ while preserving $r$. Hence $\{P_{r,s}^{(p)}\}_{(r,s)\in\Lambda_{\text{tri}}}$ is unitriangular with determinant $\pm 1$ with respect to $\{z^r (z')^s\}_{(r,s)\in\Lambda_{\text{tri}}}$.

**Lemma 4.3 (Unified Hasse–Schmidt Biconjugate $\mathbb{F}_{p^2}$-Frobenius Valuation Lemma).** *Let $P_i = (z_i, \bar{z}_i) \in \mathcal{O}_K$ and $j \geq 0$.*

1. *For every inert prime $2 \leq p < K$, $(r, s) \in T_{\text{top}}(L_0)$ satisfies $v_p\big(\mathcal{D}_z^{(j)} P_{r,s}^{(p)}(P_i)\big) \geq \max\big(0, \, h_1(r, s) - \lfloor (j - M)/p\rfloor, \, h_1(r, s) + M - j\big)$, while $(r, s) \in T_{\text{bot}}(L_0)$ satisfies*
   $$
   v_p\Big(\mathcal{D}_z^{(j)} P_{r,s}^{(p)}(P_i)\Big) \geq \max\left(0, \; h_1(r, s) - \left\lfloor \frac{j - M_{\text{bot}}}{p} \right\rfloor\right) + \sum_{\ell \geq 1} \left\lfloor \frac{s}{p^{2\ell}} \right\rfloor \geq h_1(r, s) + \left\lfloor \frac{m(r, s) + u(s)}{p} \right\rfloor + \sum_{\ell \geq 1} \left\lfloor \frac{s}{p^{2\ell}} \right\rfloor - \left\lfloor \frac{j}{p} \right\rfloor.
   $$
2. *For every inert prime $p \geq K$ and every $(r, s) \in \Lambda_{\text{tri}}$ with $0 \leq j \leq r$ (while $\mathcal{D}_z^{(j)} P_{r,s}^{(p)} \equiv 0$ for $j > r$),*
   $$
   v_p\Big(\mathcal{D}_z^{(j)} P_{r,s}^{(p)}(P_i)\Big) \geq \max\left(0, \; \left\lfloor \frac{r}{p} \right\rfloor - \left\lfloor \frac{j}{p} \right\rfloor\right) + \sum_{\ell \geq 1} \left\lfloor \frac{s}{p^{2\ell}} \right\rfloor.
   $$
3. *For every ramified prime $q \mid D$ ($q\mathcal{O}_K = \mathfrak{p}_q^2$, residue field $\mathcal{O}_K/\mathfrak{p}_q \cong \mathbb{F}_q$ of cardinality $q$), replacing $B_s^{(q)}(z')$ in $P_{r,s}^{(q)}(z, z')$ by the **ramified pure-$z'$ polynomial** $\widehat{B}_s^{(q)}(z') := \big((z')^q - z'\big)^{q\lfloor s/q^2\rfloor} \in \mathbb{Z}[z']$ (monic of the same degree $q^2\lfloor s/q^2\rfloor$ in $z'$ alone, so $\{P_{r,s}^{(q,\text{ram})}\}_{(r,s)\in\Lambda_{\text{tri}}}$ remains unitriangular with determinant $\pm 1$) satisfies $v_{\mathfrak{p}_q}\big(\widehat{B}_s^{(q)}(\bar{z}_i)\big) \geq q\lfloor s/q^2\rfloor \geq \sum_{\ell \geq 1}\lfloor s/q^{2\ell}\rfloor$ for **every** $\bar{z}_i \in \mathcal{O}_K$, and $v_{\mathfrak{p}_q}\big(\mathcal{D}_z^{(j)} P_{r,s}^{(q,\text{ram})}(P_i)\big)$ satisfies the exact lower bounds of (1)–(2) with $p = q$.*

*Proof.* (1) By Lemma 2.2, $c_0 := z_i^p - \bar{z}_i \in p\mathcal{O}_K$, $\bar{c}_0 = \bar{z}_i^p - z_i \in p\mathcal{O}_K$, and $d_0 := z_i^{p^2} - z_i \in p\mathcal{O}_K$, with $(z_i + t)^p - \bar{z}_i = (c_0 + p g_1(t)) + t^p$, $\bar{z}_i^p - (z_i + t) = \bar{c}_0 - t$, and $(z_i + t)^{p^2} - (z_i + t) = (d_0 + p g_2(t)) + (-t + t^{p^2})$ for polynomials $g_1, g_2 \in \mathcal{O}_K[t]$. Expanding $P_{r,s}^{(p)}(z_i + t, \bar{z}_i)$ by the binomial theorem, each summand indexed by $0 \leq a_1 \leq h_1$ (selecting $t^p$ from $(z_i+t)^p - \bar{z}_i$) and $0 \leq a_2 \leq M$ (selecting $-t$ or $-t + t^{p^2}$ from the $M$ factors) has coefficients in $p^{(h_1 - a_1) + (M - a_2)}\mathcal{O}_K$ and is divisible by $t^{p a_1 + a_2}$. Thus it contributes to $[t^j]$ only if $p a_1 + a_2 \leq j$, which implies both $a_1 + a_2 \leq j$ and $p(a_1 + a_2) = p a_1 + a_2 + (p - 1)a_2 \leq j + (p - 1)M$, so $(h_1 - a_1) + (M - a_2) \geq \max\big(0, \, h_1 + M - j, \, h_1 - \lfloor (j - M)/p\rfloor\big)$. On $T_{\text{bot}}(L_0)$, because $B_s^{(p)}(z') \in \mathbb{Z}[z']$ is independent of $z$, $\mathcal{D}_z^{(j)}$ factors through $B_s^{(p)}(\bar{z}_i)$, adding $v_p(B_s^{(p)}(\bar{z}_i)) \geq \sum_{\ell \geq 1}\lfloor s/p^{2\ell}\rfloor$ to the untowered bound with $M_{\text{bot}} = m(r, s) + u(s)$.
(2) For $p \geq K$, $\mathcal{D}_z^{(j)}$ factors through $A_s^{(p)}(\bar{z}_i)$, adding $v_p(A_s^{(p)}(\bar{z}_i)) \geq \sum_{\ell \geq 1} \lfloor s/p^{2\ell}\rfloor$ to the $M = 0$ case of (1).
(3) At a ramified prime $q \mid D$ ($q\mathcal{O}_K = \mathfrak{p}_q^2$, $\mathcal{O}_K/\mathfrak{p}_q \cong \mathbb{F}_q$), Fermat's Little Theorem in $\mathbb{F}_q$ gives $\bar{z}_i^q - \bar{z}_i \in \mathfrak{p}_q$ for every $\bar{z}_i \in \mathcal{O}_K$ (whether $\bar{z}_i \in \mathfrak{p}_q$ or $\bar{z}_i \notin \mathfrak{p}_q$), so $v_{\mathfrak{p}_q}(\widehat{B}_s^{(q)}(\bar{z}_i)) = q\lfloor s/q^2\rfloor v_{\mathfrak{p}_q}(\bar{z}_i^q - \bar{z}_i) \geq q\lfloor s/q^2\rfloor \geq 2\lfloor s/q^2\rfloor \geq \sum_{\ell \geq 1}\lfloor s/q^{2\ell}\rfloor$ for all $q \geq 2$ and $s \geq 0$ (whereas the inert tower $F_1(\bar{z}_i) = \bar{z}_i^{q^2} - \bar{z}_i$ has $v_{\mathfrak{p}_q}(F_1(\bar{z}_i)) = 1$ when $\bar{z}_i \in \mathfrak{p}_q \setminus \mathfrak{p}_q^2$). Since $z_i \equiv \bar{z}_i \pmod{\mathfrak{p}_q}$, $z_i^q - \bar{z}_i, \, \bar{z}_i^q - z_i, \, z_i^{q^2} - z_i \in \mathfrak{p}_q$, and $q\mathcal{O}_K = \mathfrak{p}_q^2 \subset \mathfrak{p}_q$, the binomial expansion in (1)–(2) holds verbatim in $\mathfrak{p}_q$-adic valuation. $\square$


Crucially, on the right subtriangle $r \geq p(S - s)$ parameterized in Lemma 4.1(2) by $d \in \{0, \ldots, S-1\}$, $c \in \{p, \ldots, K-1\}$, and $s \in \{0, \ldots, L - 1\}$ with $L := S - d$, $m(d, c) = \lfloor (Kd + c)/p^2\rfloor$ is independent of $s$. As $s$ runs over $\{0, \ldots, L - 1\}$, **Hermite's identity** $\sum_{u=0}^{p-1}\left\lfloor \frac{m + u}{p}\right\rfloor = m$ holds identically on each full block of length $p^2$, while on the remaining $L \bmod p^2$ elements the deficit is at most $\frac{p^2}{4}$, yielding the exact pointwise inequality $\sum_{s=0}^{L-1}\left\lfloor \frac{m(d, c) + u(s)}{p}\right\rfloor \geq \frac{L}{p}m(d, c) - \frac{p^2}{4}$. On $T_{\text{top}}(L_0) = \{1 \leq L \leq L_0\}$ of exact cardinality $m := |T_{\text{top}}(L_0)| = (K - p)\frac{L_0(L_0+1)}{2} =: q_0 M_{\text{tri}}$, decomposing $\left\lfloor \frac{s}{p}\right\rfloor = \sum_{\ell \geq 1}\left\lfloor \frac{s}{p^{2\ell}}\right\rfloor + \left(\left\lfloor \frac{s}{p}\right\rfloor - \sum_{\ell \geq 1}\left\lfloor \frac{s}{p^{2\ell}}\right\rfloor\right)$ combines the even powers $\sum_{\ell \geq 1}\lfloor s/p^{2\ell}\rfloor$ across all of $\Lambda_{\text{tri}} = T_{\text{bot}}(L_0) \cup T_{\text{top}}(L_0)$ into $2K\sum_{\ell \geq 1}\Sigma_{\text{tri}}(S, p^{2\ell})$ and leaves $2(K - p)\big(\Sigma_{\text{tri}}(L_0, p) - \sum_{\ell \geq 1}\Sigma_{\text{tri}}(L_0, p^{2\ell})\big)$ on $T_{\text{top}}(L_0)$. Moreover, on the $m$ rows of $T_{\text{top}}(L_0)$, subtracting the global first-power Legendre column term $-\lfloor j_r/p\rfloor$ from $-j_r$ leaves the column charge $\delta_p(j_r) := j_r - \lfloor j_r/p\rfloor$. Since $\delta_p(j)$ is non-decreasing in $j \geq 0$ with exact prefix sum $S_p(B) := \sum_{j=0}^{B-1}(j - \lfloor j/p\rfloor) = \frac{p-1}{2p}B^2 - \frac{r_B(p - r_B)}{2p}$ ($r_B := B \bmod p \in \{0, \ldots, p-1\}$, where the $-B/2$ from $0$-indexing $j \in \{0, \ldots, B-1\}$ and the $+B/2$ from the average mod-$p$ remainder cancel identically inside $\frac{p-1}{2p}B^2$), the maximum of $\sum_{r=1}^m \delta_p(j_r)$ over any $m = q_{\text{col}}n + r_{\text{col}}$ columns in $\{1, \ldots, n\} \times \{0, \ldots, J-1\}$ ($A := J - q_{\text{col}}$) equals $(n - r_{\text{col}})(S_p(J) - S_p(A)) + r_{\text{col}}(S_p(J) - S_p(A-1)) \leq \frac{p-1}{p}\big(mJ - \frac{m^2}{2n}\big) + \mathbf{1}_{m > 0}\, n\frac{\lfloor p^2/4\rfloor}{2p}$. Multiplying by $\frac{2}{W_{\text{main}}}$ using the exact finite-$S$ ratio $\frac{2M_{\text{tri}}}{W_{\text{main}}} = \frac{3(S+1)}{RS} = \frac{3}{R}\big(1 + \frac{1}{S}\big)$ and $\sum_{c=p}^{K-1} m(d, c) \geq \frac{K-p}{p^2}\big(K(S - L) + \frac{K+p-1}{2} - (p^2 - 1)\big)$ gives the closed-form lower bound $w_{\text{keep}}(p)$ for $2 \leq p < K$ with $K_{\text{drop}} = 0$:

$$
w_{\text{keep}}(p) := \frac{W_2 + 2K\sum_{\ell \geq 1} \Sigma_{\text{tri}}(S, p^{2\ell})}{W_{\text{main}}} + \max_{0 \leq L_0 \leq S}\left[\frac{\big(m_{\text{top}}(L_0) + m_{\text{bot}}(L_0) - \frac{p^2}{2}(S - L_0)(K - p) + 2(K - p)(\Sigma_{\text{tri}}(L_0, p) - \sum_{\ell \geq 1}\Sigma_{\text{tri}}(L_0, p^{2\ell}))\big)_+}{W_{\text{main}}} - 3\left(1 + \frac{1}{S}\right)q_0\left(1 - \frac{1}{2}q_0\theta\right)\frac{p - 1}{p}\frac{J}{R} - \mathbf{1}_{L_0 > 0}\frac{M_{\text{tri}}\lfloor p^2/4\rfloor}{p\theta (J/R) R W_{\text{main}}}\right],
$$

where $\Sigma_{\text{tri}}(N, m) := \sum_{s=0}^{N-1}(N - s)\lfloor s/m\rfloor$ is given in closed form by Lemma 4.2, $m_{\text{top}}(L_0) := \frac{2(K-p)}{p^2}\big(K\sum_{L=1}^{L_0} L(S-L) + c_{K,p}\sum_{L=1}^{L_0} L\big)$, and $m_{\text{bot}}(L_0) := \frac{2(K-p)}{p^3}\big(K\sum_{L=L_0+1}^S L(S-L) + c_{K,p}\sum_{L=L_0+1}^S L\big)$ with $c_{K,p} := \frac{K+p-1}{2} - (p^2 - 1)$.
