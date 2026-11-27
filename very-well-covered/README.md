# A non-unimodal independence polynomial after one leafy extension

Levit and Mandrescu's [2003 question](https://arxiv.org/abs/math/0307012) asks: given a finite simple graph $G$ with independence number $\alpha(G)\ge 5$, attach one new leaf to each vertex. Must the resulting graph have a unimodal independence polynomial? **No.** The connected counterexample below has 14,592 vertices. It also disproves the conjecture for very well-covered graphs and the clique corona conjecture at $p=1$.

An independent set is a set of pairwise nonadjacent vertices; $\alpha(G)$ is its largest possible size. The independence polynomial $I(G;x)=\sum_{k=0}^{\alpha(G)}s_k x^k$ counts the independent sets by size, including $s_0=1$ for the empty set. Its coefficients are **unimodal** if for some $m$ they satisfy $s_0\le\cdots\le s_m\ge\cdots\ge s_{\alpha(G)}$. Equalities are allowed.

## The counterexample (proved)

Let $t=192$. Take two disjoint graphs: $A$ consists of $t$ disjoint copies of the complete graph $K_{30}$, and $B$ consists of $4t$ disjoint copies of $K_2$. Form their **join** $H$ by adding every edge between $A$ and $B$. Write $n=38t=7296$ for its order. An independent set in $H$ lies on one side of the join and takes at most one vertex per clique. Taking one from every clique of $B$ attains $\alpha(H)=4t=768$.

For each old vertex $v$ of $H$, attach a new vertex $v'$ adjacent only to $v$. The resulting graph $W$ is connected: the join connects the two nonempty sides, and every new vertex has an old neighbor. Thus $W$ has $2n=14592$ vertices and no isolated vertices.

An independent set in $W$ takes at most one vertex from each pair $\{v,v'\}$. If it misses both, it can add $v'$, so a maximal independent set takes exactly one vertex from every pair. Conversely, for any independent set $S$ of old vertices, take $S$ together with the leaves of *all* old vertices outside $S$. This is independent and cannot be enlarged, since every omitted vertex has its partner in the set. These are precisely the maximal independent sets, all of size $n$. Thus $W$ is **very well-covered**: it has no isolated vertices and each inclusion-maximal independent set has half the order of the graph.

### Counting the coefficients

In each clique of size $q$, the choices for an independent set are the empty set or one of $q$ vertices. The choices across disjoint cliques multiply. Across the join the two sides contribute separately, except that the empty set is counted twice. Hence

$$
I(H;y)=(1+30y)^t+(1+2y)^{4t}-1.
$$

For each independent set of $j$ old vertices, any subset of the $n-j$ remaining leaves can be added. Its contribution to $I(W;x)$ is $x^j(1+x)^{n-j}$. Summing and substituting the polynomial for $H$ gives

$$
\begin{aligned}
I(W;x)&=(1+x)^n I\!\left(H;\frac{x}{1+x}\right)\\
&=(1+x)^{37t}(1+31x)^t+(1+x)^{34t}(1+3x)^{4t}-(1+x)^{38t}.
\end{aligned}
$$

Why this choice of cliques? Each positive summand has the same sum of coefficients, $M=2^{42t}$. Their mass sits at different degrees: for a polynomial $F$ with nonnegative coefficients, the mean degree weighted by its coefficients is $F'(1)/F(1)$. The two means here are $37t/2+31t/32=3738$ and $34t/2+3t=3840$. This suggests comparing the coefficients there with the coefficient halfway between them; the means alone do not prove a dip.

### An exact valley

Write $s_k=[x^k]I(W;x)$. To evaluate only the three counts needed, separate the sets consisting solely of leaves from those with $j\ge 1$ old vertices:

$$
s_k=\binom{n}{k}+\sum_{j=1}^{\min(k,4t)}
\left[\binom{t}{j}30^j+\binom{4t}{j}2^j\right]\binom{n-j}{k-j}.
$$

Here $\binom{a}{b}=0$ for $b>a$. The bracket counts the choices of occupied cliques and the vertex in each; the last factor chooses the leaves. Integer evaluation gives the following floors, not floating-point estimates:

| $k$ | $\lfloor 10^6 s_k/M\rfloor$ |
| ---: | ---: |
| 3738 | 9957 |
| 3789 | 9105 |
| 3840 | 9976 |

In particular, $s_{3738}>s_{3789}<s_{3840}$. If a mode were at or before 3789, the later rise would be impossible; if at or after 3789, the earlier drop would be impossible. This proves non-unimodality. ∎

[check_coefficients.py](check_coefficients.py) evaluates the displayed binomial sum with Python integers. Run `python very-well-covered/check_coefficients.py` from the repository root to reproduce the table and check the strict comparisons on the unscaled counts.

## What this answers

- V. E. Levit and E. Mandrescu, [*A family of well-covered graphs with unimodal independence polynomials*](https://arxiv.org/abs/math/0307012) (2003), end of §3, ask the one-leaf-per-vertex question above after proving the cases $\alpha(G)\le4$. The bound is on the **base**, not its leafy extension. S.-Y. Chen and H.-J. Wang later extended the positive result to $\alpha(G)\le8$ (*Ars Combinatoria* 97A (2010), 509–529), as reported by [Brown and Cameron](https://arxiv.org/abs/1709.08236), introduction.
- A well-covered graph need only have all maximal independent sets of the same size, not necessarily half its order. [T. Michael and W. Traves (2003)](https://doi.org/10.1007/s00373-002-0515-7) and [Levit and Mandrescu (2006)](https://doi.org/10.1016/j.ejc.2005.04.007) gave non-unimodal examples for this larger class. The latter paper, §4, distinguishes those examples from the very well-covered question. J. I. Brown and B. Cameron, [*On the unimodality of independence polynomials of very well-covered graphs*](https://doi.org/10.1016/j.disc.2017.10.007) (2018), introduction and §2, record the broader Levit–Mandrescu conjecture and prove strict log-concavity after sufficiently many iterations of the leafy extension. That result does not require the **first** extension to be unimodal.
- D. T. Hoang, V. E. Levit, E. Mandrescu and M. H. Pham, [*Unimodality of the independence polynomial of clique corona graphs*](https://doi.org/10.26493/1855-3974.3383.3c7) (2026), [Conjecture 6.1](https://amc-journal.eu/index.php/amc/article/download/3383/2273), ask whether $I(G\circ K_p;x)$ is unimodal for every finite simple graph $G$ without isolated vertices (their convention, §1) and all $p\ge1$. Our base has no isolated vertices, since both sides of the join are nonempty. In this corona each old vertex is joined to every vertex of its own new $p$-clique. Our graph is exactly $H\circ K_1$, so the universal claim fails at $p=1$; the special cases proved in that paper are not contradicted.

The explicit counterexample is proved here; the cited papers pose the unrestricted questions or prove restricted cases, not this negative result. This is not a counterexample for trees: the base already contains triangles. We make no claim of minimum order or of publication priority.
