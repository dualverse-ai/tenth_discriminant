# Resultants and the rank of the interpolation matrix

Original section and equation numbers are retained.

**Editorial correction.** In the proof of Lemma 3.3 the term $M_y R W_1^*/S$ in the original notes contains an extra $R$. It is written below as $M_y W_1^*/S$, in agreement with Lemma 3.2 and the following displayed bound. Pure factors in $z^{\prime}$ are counted with multiplicity capped at $J$: their distinct roots can affect at most $d_0^{\prime}$ nodes, since conjugation is injective on the nodes. The resulting contribution is at most $Jd_0^{\prime}$.

### 3.1 Weighted Sylvester Resultant Degree Bound on $\Lambda_{\text{tri}}$

Fix an integer slope $K \geq 2$ and an integer $S \geq 10$, and set $R := KS$. Define the weighted triangular bidegree polytope

$$
\Lambda_{\text{tri}} := \big\{(r, s) \in \mathbb{Z}_{\geq 0}^2 : r + Ks < KS = R\big\} = \big\{(r, s) \in \mathbb{Z}_{\geq 0}^2 : 0 \leq s < S, \, 0 \leq r < K(S - s)\big\}.
$$

Summing over $t := S - s \in \{1, 2, \ldots, S\}$ gives the exact dimension and degree moments of $\Lambda_{\text{tri}}$:

$$
\begin{aligned}
M_{\text{tri}} &:= |\Lambda_{\text{tri}}| = \sum_{t=1}^S Kt = \frac{R(S+1)}{2}, \qquad W_{\text{main}} := \frac{R^2 S}{3}, \\
W_1 &:= \sum_{(r,s)\in\Lambda_{\text{tri}}} 2r = \sum_{t=1}^S Kt(Kt - 1) = \frac{R^2(S+1)(2S+1)}{6S} - M_{\text{tri}}, \\
W_2 &:= \sum_{(r,s)\in\Lambda_{\text{tri}}} 2s = \sum_{t=1}^S 2Kt(S - t) = \frac{R(S^2 - 1)}{3}.
\end{aligned}
$$

**Lemma 3.1 (Weighted Sylvester Resultant Degree Bound on $\Lambda_{\text{tri}}$).** *Let $F(z, z') = \sum_{(r,s)\in\Lambda_{\text{tri}}} a_{r,s} z^r (z')^s \in \mathbb{C}[z, z']$ be a non-zero polynomial supported in $\Lambda_{\text{tri}}$, factored into irreducibles as $F(z, z') = F_0(z') \prod_{\ell=1}^k F_\ell(z, z')$, where $d_\ell := \deg_z F_\ell \geq 1$ and $d'_0 := \deg_{z'} F_0$. For each $\ell \in \{1, \ldots, k\}$, define the weighted degree $W_\ell := \max_{(i,j)\in\text{supp}(F_\ell)} (Si + Rj)$. Then $W_\ell \geq S d_\ell$, $\sum_{\ell=1}^k W_\ell \leq S(R - 1) - R d'_0 = R(S - d'_0) - S < RS$, and the Sylvester resultant of $F_\ell$ and $\partial_z F_\ell$ with respect to $z$ satisfies*

$$
\deg_{z'} \text{Res}_z\big(F_\ell, \partial_z F_\ell\big) \leq \left\lfloor \frac{(2d_\ell - 1)W_\ell - S d_\ell(d_\ell - 1)}{R} \right\rfloor \leq \frac{W_\ell^2}{RS}, \qquad \sum_{\ell=1}^k \deg_{z'} \text{Res}_z\big(F_\ell, \partial_z F_\ell\big) < RS.
$$

*Proof.* Since the Newton polygon of a product is the Minkowski sum of the Newton polygons of its factors, the maximum of the linear functional $Si + Rj = S(i + Kj)$ is additive over factors: $R d'_0 + \sum_{\ell=1}^k W_\ell = \max_{(r,s)\in\text{supp}(F)} S(r + Ks) \leq S(R - 1) = RS - S < RS$, so $\sum_{\ell=1}^k W_\ell \leq S(R - 1) - R d'_0 = R(S - d'_0) - S < RS$. Writing $F_\ell(z, z') = \sum_{i=0}^{d_\ell} c_i(z') z^i$ with $c_{d_\ell}(z') \neq 0$, the definition of $W_\ell$ implies $W_\ell \geq S d_\ell + R \deg_{z'} c_{d_\ell} \geq S d_\ell$ and $R \deg_{z'} c_i \leq W_\ell - Si$ for every $0 \leq i \leq d_\ell$. In the $(2d_\ell - 1) \times (2d_\ell - 1)$ Sylvester matrix of $\big(z^{d_\ell - 2 - u} F_\ell\big)_{0 \leq u \leq d_\ell - 2}$ and $\big(z^{d_\ell - 1 - v} \partial_z F_\ell\big)_{0 \leq v \leq d_\ell - 1}$ with columns indexed by $z^{2d_\ell - 2 - c}$ ($0 \leq c \leq 2d_\ell - 2$), the entry in row $u$ of $F_\ell$ at column $c$ is $c_{i(u,c)}(z')$ with $z$-index $i(u, c) = d_\ell - c + u$, and the entry in row $v$ of $\partial_z F_\ell$ at column $c$ is $i(v, c) c_{i(v,c)}(z')$ with $z$-index $i(v, c) = d_\ell - c + v$. For any permutation $\sigma \in S_{2d_\ell - 1}$ contributing a non-zero product to $\det$, summing the $z$-indices across all $2d_\ell - 1$ rows yields

$$
\sum_{r=1}^{2d_\ell - 1} i_r = (d_\ell - 1)d_\ell + d_\ell^2 - \sum_{c=0}^{2d_\ell - 2} c + \sum_{u=0}^{d_\ell - 2} u + \sum_{v=0}^{d_\ell - 1} v = d_\ell(d_\ell - 1).
$$

Hence the $z'$-degree of that diagonal product is at most $\frac{1}{R}\sum_{r=1}^{2d_\ell - 1} (W_\ell - S i_r) = \frac{(2d_\ell - 1)W_\ell - S d_\ell(d_\ell - 1)}{R}$. Because $W_\ell \geq S d_\ell > S(d_\ell - 1)$, we have $W_\ell^2 - S\big((2d_\ell - 1)W_\ell - S d_\ell(d_\ell - 1)\big) = (W_\ell - S d_\ell)\big(W_\ell - S(d_\ell - 1)\big) \geq 0$, and therefore $\deg_{z'} \text{Res}_z(F_\ell, \partial_z F_\ell) \leq \frac{W_\ell^2}{RS}$. Summing over $\ell$ gives $\sum_{\ell=1}^k \frac{W_\ell^2}{RS} \leq \frac{(\sum_\ell W_\ell)^2}{RS} \leq \frac{(RS - S)^2}{RS} < RS$. $\square$

### 3.2 Irreducible Fiber-Line Zero Bound and Removal of the $+R$ Rank Artifact

**Lemma 3.2 (Irreducible Factor Classification and Zero Multiset Bound on $E_{\rho_n}$).** *Let $D > 163$, let $E = \{P_1, \ldots, P_n\} \subset \mathcal{O}_K$ be contained in the disk $|z| \leq \rho_n$, and define the horizontal fiber count $M_y := 2\lfloor 2\rho_n / \sqrt{D}\rfloor + 1$ and fiber width $M_x := \lfloor 2\rho_n\rfloor + 1$ ($M_y \leq M_x$). For any irreducible polynomial $F_\ell(z, z') \in \mathbb{C}[z, z']$ of weighted degree $W_\ell := \max_{(i,j)\in\text{supp}(F_\ell)}(Si + Rj)$ with $d_\ell := \deg_z F_\ell \geq 1$:*

1. *(Type 2, horizontal-line factors): If $F_\ell(z, z') = c_\ell(z - z' - y_\ell\sqrt{-D})$ for some $y_\ell \in \mathbb{Z}$, then $W_\ell = R$, $F_\ell$ has simple $z$-roots ($m_i(\ell) \leq 1$), and $\sum_{i=1}^n m_i(\ell) \leq M_x$.*
2. *(Type 1, general factors): If $F_\ell$ is not of Type 2, then its restriction $g_{\ell, y_0}(z) := F_\ell(z, z - y_0\sqrt{-D}) \not\equiv 0$ on every horizontal line $y = y_0 \in \mathbb{Z}$ has degree $\leq \max_{(i,j)\in\text{supp}(F_\ell)}(i+j) \leq \frac{W_\ell}{S}$ (since $S(i+j) \leq Si + Rj \leq W_\ell$), so the number of points with $m_i(\ell) \geq 1$ satisfies $|E_1(\ell)| \leq M_y \frac{W_\ell}{S}$, while the higher multiplicity sum satisfies $\sum_{i\in E_2(\ell)}(m_i(\ell)-1) \leq \frac{W_\ell^2}{RS}$ (Lemma 3.1).*

*Proof.* For Type 2, $z - \bar{z} - y_\ell\sqrt{-D} = (y - y_\ell)\sqrt{-D}$ vanishes identically on the single horizontal line $y = y_\ell$, which contains at most $M_x$ points of $E$, and for each point the $z$-derivative is $\partial_z F_\ell = c_\ell \neq 0$, so all roots are simple ($E_2(\ell) = \emptyset$). For Type 1, $g_{\ell, y_0}(z) \not\equiv 0$ on all $y_0$, so $g_{\ell, y_0}$ has at most $\deg g_{\ell, y_0} \leq \frac{W_\ell}{S}$ roots on each of the $\leq M_y$ lines, giving $|E_1(\ell)| \leq M_y \frac{W_\ell}{S}$. Lemma 3.1 gives the higher-multiplicity bound $\sum_{i\in E_2(\ell)}(m_i(\ell)-1) \leq \deg_{z'}\text{Res}_z(F_\ell, \partial_z F_\ell) \leq \frac{W_\ell^2}{RS}$. $\square$

**Lemma 3.3 (Full-Rank Criterion on $\Lambda_{\text{tri}}$ Without the $+S$ Artifact).** *Let $J \geq 2$ be an integer and let $V^{\text{HS}}$ be the $M_{\text{tri}} \times (nJ)$ Hasse–Schmidt evaluation matrix with rows $(r, s) \in \Lambda_{\text{tri}}$, columns $(i, j) \in \{1, \ldots, n\} \times \{0, \ldots, J-1\}$, and entries $\mathcal{D}_z^{(j)}\big(z^r (z')^s\big)\big|_{P_i} = \binom{r}{j} z_i^{r-j} \bar{z}_i^s$. If $\max(J, M_x) \leq R + M_y K$ and*

$$
n > \frac{RS + M_y R}{J},
$$

*then $\text{rank}(V^{\text{HS}}) = M_{\text{tri}}$, so there exists a subset $C \subset \{1, \ldots, n\} \times \{0, \ldots, J-1\}$ of cardinality $|C| = M_{\text{tri}}$ such that the square submatrix $V_C^{\text{HS}}$ is non-singular ($\det V_C^{\text{HS}} \in \mathcal{O}_K \setminus \{0\}$).*

*Proof.* Suppose $\text{rank}(V^{\text{HS}}) < M_{\text{tri}}$. Then there exists a non-zero polynomial $F(z, z') = F_0(z') \prod_{\ell=1}^k F_\ell(z, z')$ supported in $\Lambda_{\text{tri}}$ vanishing to order $\geq J$ at all $P_i$. Partition the non-constant factors $F_\ell$ ($\deg_z F_\ell \geq 1$) into Type 2 factors $\mathcal{T}_2$ ($k_2 := |\mathcal{T}_2|$, each having $W_\ell = R$) and Type 1 factors $\mathcal{T}_1$. By additivity of the weighted degree $W(GH) = W(G) + W(H)$ on the Newton polygon, $R d'_0 + R k_2 + \sum_{\ell\in\mathcal{T}_1} W_\ell \leq S(R - 1) < RS$. Setting $W_1^* := \sum_{\ell\in\mathcal{T}_1} W_\ell$ and $\beta := \frac{W_1^*}{RS} \in [0, 1)$, we have $d'_0 + k_2 < (1 - \beta)S$. Summing the root multiplicities over all $P_i$ using Lemma 3.2 gives
$$
J n \leq J d'_0 + M_x k_2 + \frac{(W_1^*)^2}{RS} + M_y \frac{W_1^*}{S} < (1 - \beta)\max(J, M_x)S + \beta^2 RS + \beta M_y R.
$$
Since $\beta^2 < \beta$ for $\beta \in (0, 1)$, the convex combination satisfies $(1 - \beta)\max(J, M_x)S + \beta(RS + M_y R) \leq \max\big(\max(J, M_x)S, \, RS + M_y R\big)$. Whenever $\max(J, M_x) \leq R + M_y K$ (i.e. $\max(J, M_x)S \leq RS + M_y R$), the right-hand side is at most $RS + M_y R$, so $J n < RS + M_y R$, contradicting $n > \frac{RS + M_y R}{J}$. The non-singularity and integrality of $\det V_C^{\text{HS}} \in \mathcal{O}_K \setminus \{0\}$ follow from the full row rank and the integrality of the matrix entries. $\square$
