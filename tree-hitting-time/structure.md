# From hitting times to pendant-path fusions

**Theorem (proved).** Let $T$ be a finite, simple, undirected tree on $n\ge1$ vertices. Among trees of that order, the path $P_n$ uniquely maximizes the hitting time index, up to isomorphism. This is a written proof; the local estimate used in the last section is proved in [the fusion lemma](fusion.md).

## The random-walk convention

For $n\ge2$, start a simple random walk at $u$, choosing a neighbor uniformly at each step. Let $H(u,v)$ be the expected number of steps until its first visit to $v$, with $H(v,v)=0$. Sum the larger direction once for each unordered pair of **distinct** vertices:

$$
\operatorname{HT}(T)=\sum_{\{u,v\}\subseteq V(T)}\max\{H(u,v),H(v,u)\}.
$$

For the one-vertex tree define the index by the empty sum $0$; no transition from an isolated vertex is needed. For the two-vertex tree both directions take one step, so its index is $1$.

Write $d(u,v)$ for graph distance, $t(u)=\sum_x d(u,x)$ for transmission, and $W(T)=\sum_{\{u,v\}}d(u,v)$ for the Wiener index. Pair sums here and below are over two-element subsets.

**Lemma (distance formula).** For $n\ge2$,

$$
H(u,v)=(n-1)d(u,v)+t(v)-t(u).
$$

**Proof.** Hitting times are integrable: from any starting point a path of length at most $n-1$ reaches $v$ with probability at least $\varepsilon=(n-1)^{-(n-1)}$. Thus the probability of not reaching $v$ in $k$ successive blocks of $n-1$ steps is at most $(1-\varepsilon)^k$. The vertices on the unique path from $u$ to $v$ are first visited in path order. The strong Markov property at these first visits makes $H(u,v)$ the sum of the forward hitting times across the path edges.

Consider one edge $uv$, and let $s$ be the size of the component containing $u$ after cutting it. A first step from $u$ to a neighbor $w\ne v$ must be followed by a return to $u$ before the walk reaches $v$. Conditioning on the first step and rearranging gives

$$
H(u,v)=\deg(u)+\sum_{w\sim u,\,w\ne v}H(w,u).
$$

Induct on $s$ to obtain $H(u,v)=2s-1$. For $s=1$ the step from the leaf to its parent takes exactly one unit of time. Otherwise, the components on the $w$-sides of the edges $wu$, for $w\ne v$, partition the $s-1$ vertices other than $u$ in the $u$-component. Substituting $2s_w-1$ for each term gives $\deg(u)+2(s-1)-(\deg(u)-1)=2s-1$.

Crossing $uv$ towards $v$ increases the distance to the $s$ vertices on the $u$-side by one each, and decreases the distance to all others by one each. Hence $t(v)-t(u)=2s-n$ and $H(u,v)=(n-1)+t(v)-t(u)$. Sum this equality along the path: the distance counts its edges and the transmission differences telescope. ∎

Taking the larger direction gives the identity used in the local estimate:

$$
\operatorname{HT}(T)=(n-1)W(T)+\sum_{\{u,v\}} |t(v)-t(u)|.
$$

If the two transmissions agree then so do the two hitting times; the equality still counts that pair once.

## An admissible fusion exists at every nonpath

A *pendant path* at $b$ is an entire component of $T-b$ that is a path, with one endpoint formerly adjacent to $b$. This includes a single pendant vertex. Its length is the number of vertices in that component. The [fusion lemma](fusion.md) states: if at a vertex $b$ of degree at least three there are two pendant paths of lengths $p\ge q\ge1$, and the number $c=n-p-q$ of remaining vertices (including $b$) satisfies $c\ge p+1$, then detaching the $p$-path from $b$ and reattaching it at the far end of the $q$-path strictly increases $\operatorname{HT}$.

**Lemma (selection).** Every nonpath tree admits such a choice of $b,p,q$.

**Proof.** Choose a vertex $r$ minimizing $t(r)$. No component of $T-r$ has more than $n/2$ vertices: if one had size $a>n/2$, crossing the edge into it would change transmission by $n-2a<0$, as in the edge computation above.

Root $T$ at $r$. A finite tree of maximum degree at most two is a path, so choose a vertex $b$ of degree at least three at greatest possible distance from $r$. Every child subtree of $b$ is a pendant path, since a branch in it would give a deeper vertex of degree at least three.

If $b\ne r$, it has at least two children. Choose two of their paths, of lengths $p\ge q$. The component of $T-r$ containing $b$ contains $b$ and both paths, so $p+q+1\le n/2$. In particular $c=n-p-q\ge p+1$.

If $b=r$, it has at least three child paths. Choose the two shortest and call their lengths $p\ge q$. At least one unchosen path has length at least $p$, and that entire path and $b$ belong to the remainder. Thus $c\ge p+1$, including when the lengths tie. ∎

**Proof of the theorem.** At each nonpath apply the selection lemma and the strict fusion lemma. The result of a fusion is again a tree on the same vertices: the deleted edge disconnects the moved path and the new edge reconnects the two components. Exactly one leaf is lost. Indeed, the far end of the stationary path goes from degree one to two; $b$ loses one incident edge but retains degree at least two; the detached endpoint of the moved path has unchanged degree. This also covers one-vertex arms. All other degrees are unchanged.

The nonnegative number of leaves cannot keep falling, so this process terminates. By the selection lemma the final tree must be a path. From any nonpath at least one strict increase occurs, yielding $\operatorname{HT}(T)<\operatorname{HT}(P_n)$. Isomorphic paths have the same index. This proves the equality characterization, including the orders $1$ and $2$ handled above. ∎
