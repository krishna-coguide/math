# The path maximizes the hitting time index of trees

**Theorem (proved).** For every finite simple undirected tree $T$ of order $n\ge1$,

$$
\operatorname{HT}(T)\le \operatorname{HT}(P_n),
$$

with equality if and only if $T$ is isomorphic to the path $P_n$. The index sums, over unordered pairs of distinct vertices, the larger of the two expected first hitting times of simple random walk. For $n=1$ the empty sum is $0$; for $n=2$ the only tree has index $1$.

## Proof and checks

- [Hitting times and the structural reduction](structure.md) derives the distance formula and shows how every nonpath admits a fusion satisfying the required size bound. Each fusion removes one leaf.
- [The strict fusion lemma](fusion.md) proves the local increase for two pendant paths. The key estimate keeps the gains from pairing the moved tip with each vertex of the stationary path, instead of bounding every change by a possible loss. Together these two notes prove the theorem for all orders.
- **Formalized portion:** in [Fusion.lean](Fusion.lean), `Fusion.selected_change_bound` bounds the sum of absolute-value changes while retaining the gains at selected pairs; `Fusion.finite_budget_pos` proves strict positivity of the resulting finite-sum estimate for all admissible arm lengths. The random-walk identity, graph counts, choice of fusion, and full extremal theorem are written proofs, not Lean theorems.
- [Exact finite check](check_trees.py): `python tree-hitting-time/check_trees.py --max-n 11` (from the worktree root) checks all 436 unlabeled trees of orders 1–11 and all 4,111 admissible ordered fusions on those representatives. It computes directed hitting times using integer first-step recurrences and checks them against both the walk equations and the distance formula. This is a check, not the proof.

To rebuild the Lean portion from the worktree root, enter `tree-hitting-time/`, then run `lake build` and `lake env lean CheckFusion.lean`. [CheckFusion.lean](CheckFusion.lean) prints the axioms used by the formalized lemmas. On a fresh checkout, download the Mathlib build cache first with `lake exe cache get`.

## Published context

José Luis Palacios and Aleksandar Petojević, [*An Edge Operation That Increases the Hitting Time Index of Trees*](https://doi.org/10.3390/math14142525), *Mathematics* 14 (2026), 2525, propose that “the maximum HT index among $n$-vertex trees is attained by the $n$-path.” Their Proposition 1 proves strict increase when the stationary path is a single pendant vertex and $n\ge 2p+2$, with $p$ the length of the moved path. Their conclusion discusses fusing two pendant paths. The argument here supplies a sufficient estimate for arbitrary arm lengths and proves uniqueness, not just attainment.

Shunya Tamura, José Luis Palacios and Aleksandar Petojević, [*A Decomposition of the Hitting Time Index Using the Kirchhoff Index and an Asymmetry Term*](https://arxiv.org/abs/2610.05663), Theorem 3.1 and §5, give the decomposition underlying the distance formula. We derive its tree case directly; we do not need an extremal result for the asymmetry term alone.

José Luis Palacios, Shunya Tamura, Jason Wiberg and Aleksandar Petojević, [*The hitting time index: bounds, a sharp threshold, the proof of a conjecture and the disproof of another conjecture*](https://arxiv.org/html/2611.34295v1#S3), §3, distinguish the tree conjecture from the false claim that the path maximizes the index among all connected graphs.
