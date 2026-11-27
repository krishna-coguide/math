# Fusing two pendant paths strictly increases the hitting time index

**Local theorem (proved).** Let a joint $b$ of a finite simple tree have two
pendant paths $b,a_1,\ldots,a_p$ and $b,b_1,\ldots,b_q$, where $p\ge q\ge1$.
The two paths meet only at $b$. Here “pendant” means that each interior
vertex has degree two and each tip has degree one. Let $R$ be the remaining set of $c$ vertices,
including $b$, and suppose $c\ge p+1$. Delete $ba_1$ and add $b_q a_1$.
The resulting tree has strictly larger hitting time index.

Palacios and Petojević prove increase for $q=1$ and $n\ge2p+2$ in Proposition 1 of
[*An Edge Operation That Increases the Hitting Time Index of Trees*](https://doi.org/10.3390/math14142525),
*Mathematics* 14 (2026), 2525. Their conclusion proposes fusing two general
pendant paths. The proof below allows both arms to have arbitrary positive
lengths under the displayed size condition.

## The distance formula for the index

Write $n=p+q+c$. Let $t(u)=\sum_x d(u,x)$ be the transmission of $u$, and
$W=\sum_{\{u,v\}}d(u,v)$ the Wiener index; all pair sums are over unordered
distinct vertices, once each. Write $H(u,v)$ for the expected first hitting
time of $v$ starting at $u$ for simple random walk. Then

$$
\mathrm{HT}=\sum_{\{u,v\}}\max(H(u,v),H(v,u))
=(n-1)W+\sum_{\{u,v\}}|t(v)-t(u)|.
$$

For the derivation from first-step equations for the walk, see
[the random-walk convention](structure.md#the-random-walk-convention).

## Distance and transmission changes

**Proof of the local theorem.** Write $A=\{a_i:1\le i\le p\}$ and
$B=\{b_j:1\le j\le q\}$. Deleting the edge detaches exactly $A$, and the new
edge reconnects it, so the new graph is a tree on the same vertex set. Write
$\Delta$ for new minus old. Distances within $A$ and within $R\cup B$ are
unchanged. For $x\in R$ the old distance from $a_i$ is $i+d(b,x)$ and the
new one is $i+q+d(b,x)$. For $b_j\in B$ these distances are $i+j$ and
$i+q-j$, respectively. Consequently

$$
\Delta W=pcq+p\sum_{j=1}^q(q-2j)=pq(c-1).
$$

Summing distance changes at each endpoint gives the shifts $h(v)=\Delta t(v)$:

$$
 h(x)=pq\quad(x\in R),\qquad
 h(a_i)=q(c-1),\qquad h(b_j)=p(q-2j).
$$

These obey $h(a_i)\ge h(x)>h(b_1)>\cdots>h(b_q)$ by $c\ge p+1$.

## A lower bound that keeps the gains at selected pairs

For any old transmission difference $z$ and its shift $d$, the change of the
absolute difference is $|z+d|-|z|\ge-|d|$. If $z\ge0$ and $d\ge0$, its
actual change is $d$, so it contributes $2d$ more than this lower bound.
The direction in which both differences are taken must be the same.

Let $S=\sum_{\{u,v\}}|h(u)-h(v)|$. Pairs within $A$ or within $R$ contribute
zero. The four other classes contribute, in order:

- $A,R$: $pc\,q(c-1-p)$;
- $A,B$: $p\sum_j[q(c-1)-p(q-2j)]=pq[q(c-1)+p]$;
- $R,B$: $c\sum_j 2pj=cpq(q+1)$;
- within $B$: $2p\sum_{1\le j<k\le q}(k-j)=pq(q^2-1)/3$.

For the last identity the integer gap $d$ occurs $q-d$ times, so the sum
before multiplication by $2p$ is $\sum_{d=1}^{q-1}d(q-d)=q(q^2-1)/6$.
No assumption about the signs of old or new transmission differences within
$B$ was used. The baseline lower bound for $\Delta\mathrm{HT}$, divided by the
positive factor $pq$, is therefore

$$
\begin{aligned}
D&=\frac{(n-1)\Delta W-S}{pq}\\
 &=(p+q+c-1)(c-1)-c(c-1-p)-q(c-1)-p-c(q+1)-(q^2-1)/3\\
 &=(2p-q-2)c-2p+(4-q^2)/3.
\end{aligned}
$$

Now pair the moved tip $a_p$ with **every** vertex of $B$. Along the
$p$-arm the component beyond its $i$th edge has size $p-i+1$, so
$t(a_i)-t(a_{i-1})=n-2(p-i+1)$, with $a_0=b$. Summing gives
$t(a_p)-t(b)=p(n-p-1)$; the analogous formula at $b_q$ gives
$t(a_p)-t(b_q)=(p-q)(c-1)\ge0$. Also $t(b_j)-t(b_{j-1})=n-2(q-j+1)>0$
because $n>2q$. Thus $t(a_p)-t(b_j)\ge0$ for **each** $j$, and
$h(a_p)-h(b_j)>0$ by the shift ordering. For these $q$ distinct pairs
the exact change exceeds the baseline by a total of

$$
2\sum_{j=1}^{q}[q(c-1)-p(q-2j)]=2q[q(c-1)+p].
$$

Adding this correction and factoring yields the single bound

$$
\begin{aligned}
\frac{\Delta\mathrm{HT}}{pq}
 &\ge D+2+\frac{2q(c-1)}p \\
 &=q(c-q-1)+\frac{(q-1)(2q-1)+3}{3}
   +2(p-q)(c-1)(1-1/p)>0.
\end{aligned}
$$

Indeed $c\ge p+1\ge q+1$ and $p\ge q\ge1$, so all three terms are
nonnegative and the middle term is strictly positive. The calculation
includes equal arms, even when the old tip transmissions tie. ∎

**Formalized portion.** In [Fusion.lean](Fusion.lean),
`Fusion.selected_change_bound` is the finite-pair inequality with the selected
correction. `Fusion.finite_budget_pos` proves positivity before evaluating
the one- and two-index sums for the stationary arm, for all admissible natural
sizes. Its `d` is the shift of $A$ minus the shift of $R$. The assignment
of tree pairs to these sums and the old-transmission ordering at the tip are
written proofs above, not statements about graphs in Lean.
