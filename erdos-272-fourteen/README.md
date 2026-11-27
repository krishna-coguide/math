# Erdős #272 on fourteen points

**Lean-checked result: the unrestricted maximum is between 95 and 101, inclusive.**
A family is a collection of distinct subsets of $[14]=\{1,\ldots,14\}$.
It is *valid* if the intersection of every two different members is exactly a nonempty arithmetic progression (AP).
A singleton or a pair counts as an AP. The members need not be APs.
Szabó's construction gives 95 members. The question is whether 96 are possible.

## What is proved

Call a progression *long* if it has at least seven terms. Call a set *short* if it contains no seven-term AP.
The distinction between a set **containing** a progression and two sets **intersecting exactly in** that progression matters.

1. **Four long-containing members are necessary.**
   Every valid family of size at least 96 has at least four distinct members that are not short.
   There are only 752 such subsets among the 16,383 nonempty subsets of the board.
2. **A stronger alternative.**
   Every such family either contains one of [54 explicitly listed sets](Erdos272/Catalog.lean), or at least four **distinct long APs actually occur as intersections** of pairs of different members.
   There are 38 long APs on the board. The four pairs need not be disjoint.
   The list consists of the 38 long APs and 16 non-APs with nonpositive score, as defined below.
3. **The obstruction survives deletions.**
   Delete any three or fewer members of a valid family of size at least 96.
   The remainder still contains a member of the special list or two members whose intersection is a long AP.
4. **A restricted case is within one.**
   For families with no common point and with every member short, the maximum is **91 or 92**.
   The upper bound holds even for the short part of a larger valid family with no common point.
   For 91, take all pairs and triples through 4 except the pair $\{4,9\}$, then add $[14]\setminus\{4,9\}$.
   This gives $12+78+1=91$ members. The added set has no run of seven consecutive integers and contains neither all odds nor all evens.
   It meets every other member in a singleton or a pair.

The unrestricted theorems are in [`Erdos272.lean`](Erdos272.lean): `E272.four_long`, `E272.special_or_four_intersections`, and `E272.unavoidable_after_three`.
The examples are `E272.lower_bound` in [Construction](Erdos272/Construction.lean) and `E272.short_example` in [ShortExample](Erdos272/ShortExample.lean).
Bit zero stands for the integer 1. Bitwise AND is intersection.
The AP table is proved equal to the output of an enumerator that extends a progression by positive steps while it stays inside the board.

## Proof idea

If all sets share a point, there are at most 95 by [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004).
[Stars](Erdos272/Stars.lean) proves this at 14 independently of Yang's theorem.
For each choice of common point it covers all sets containing it by at most 95 classes.
No two distinct members of one class are compatible. The class certificates are checked by Lean.
It therefore suffices to consider a family with no common point.

For a set $A$, let $a_j(A)$ count the $j$-term APs it contains and put

$$
q(A)=1+\binom{|A|}{2}-|A|-a_3(A)-a_4(A)-a_6(A).
$$

On short sets the score $q$ is zero for APs and positive for non-APs.
[ScoreTables](Erdos272/ScoreTables.lean) proves this on all 14-bit masks using bit tables whose interpretation is proved in Lean.
Record, for each member, a constant 1 and its 91 pair indicators as one vector, and its singleton and 3-, 4-, and 6-term AP indicators as another.
The difference of their inner products for $A,B$ is $q(A\cap B)$.
For distinct short members of a valid family this is zero.
A sum-of-squares argument and the elimination of the possible five-term AP relations show that the first vectors are linearly independent on the short members when the whole family has no common point.
There are only $1+91=92$ coordinates.
This adapts [Lyons's thirteen-point rank argument](https://github.com/Cameron-Lyons/formal-math-lab/tree/c87e3fd138b58d9a3ec81035f296e666c5c9c25a/erdos-272-thirteen) to fourteen points.

For the stronger alternative, suppose the family avoids the 54 special sets and at most three distinct long APs occur as pair intersections.
Adjoin one containment indicator per prescribed long AP to the 92 coordinates.
There is a correction to the score that cancels it on the three prescribed APs, is zero on short sets, and is nonnegative on all sets.
To see why, order the three masks by integer value. Assign the first indicator weight minus the score at the first mask.
At each later mask assign its indicator the weight needed to make the total correction there equal to minus its score.
The first two weights are nonnegative because minus the score is positive and monotone under inclusion on long APs.
The third weight may be negative, but on any superset of the third mask the total correction is at least its value on that mask; elsewhere the third weight contributes nothing.
The corrected rank argument bounds the family by $92+3=95$, a contradiction.
The precise hypotheses and the signed-weight argument are in [RankLocal](Erdos272/RankLocal.lean), `E272.three_pattern_bound`.

## A numerical upper bound

The first rank estimate bounds the unrestricted maximum by 119. It gives a more useful bound when we track which progressions occur.
For a family with no common point, let $h$ count the distinct 7- or 11-term APs contained in some member, and let $z$ count the 9-, 10-, or 13-term APs that **are themselves members**.
Then $|F|\leq 92+h+z$ (`E272.mobius_cost_bound`).
There are only 14 possible progressions in the first count and 13 in the second.
For example, if no member contains an 11-term progression and none is a 9-, 10-, or 13-term progression, the bound is 102.
Families with a common point already have size at most 95.

[FullRank](Erdos272/FullRank.lean) adds the 7- and 11-term indicators to the positive coordinates of the rank proof, and the 8-, 12-, and 14-term indicators to the negative coordinates.
The resulting score is zero on every AP, not only the short ones, and positive on every non-AP.
Remove only the $z$ actual members before applying the rank argument. Inactive positive coordinates can then be dropped.
This is an upper bound, not an exclusion of 96.

## How the bound drops to 101

**Theorem (formalized).** For every valid family $F$ of distinct subsets of $[14]$, $|F|\leq 101$.
The declaration is `E272.Search.Run101.upper101` in the `Erdos272Bounds` build target.
There is no hypothesis on the members, their sizes, or their common intersection.

Suppose instead that $F$ has at least 102 members. The common-point case is already impossible. The four-column refinement below gives $h+\min(4,z)\geq10$, so at least six of the 14 possible positive-coordinate progressions must occur.
The proof splits according to which of the 14 possible positive-coordinate progressions are contained in a member.
These decisions constrain *every* member. For example, if $T\subseteq A\in F$ is a progression, every $B\in F$ meets $T$ in a progression or in the empty set: for $B\ne A$, intersect the AP $A\cap B$ with $T$.
If $T$ is not contained in any member, all its supersets can be removed instead.

In a remaining case the proof can split on the presence of a particular set $A$.
If present, all other candidates must intersect it in a nonempty AP. If absent, $A$ is removed.
Some branches contradict a required containment or the rank bound directly.
For the others, the certificate colors the remaining candidates with at most 101 colors so that **no two distinct subsets of the same color have a nonempty AP as their intersection**.
A valid family can take at most one set from each color.
If a proposed coloring fails, select sets meeting every conflicting same-color pair and split on their membership. When all those sets are absent, the remaining coloring works; each presence branch is checked separately.
[Search](Erdos272/Search.lean) proves the case splits are exhaustive, [ColorProof](Erdos272/ColorProof.lean) checks the classes and their coverage, and [Certificate](Erdos272/Certificate.lean) joins these proofs.
The certificate starts with every subset available and no required progression. It does not assume a successful search, an absent singleton, or a chosen anchor.

### The four-column refinement

A separate algebraic argument sharpens the rank estimate for a family with no common point to

$$
|F|\leq 92+h+\min(4,z).
$$

Here $h$ and $z$ are the same counts as above. Since $h\leq14$, this gives 110 even without the coloring certificates. [NeutralBound](Erdos272/NeutralBound.lean) proves this by adding four linear checks on the zero-weight APs.
A nonzero rational dependence would give a nonzero parity pattern; [NeutralCover](Erdos272/NeutralCover.lean) verifies that every such pattern forces incompatible members or a common point.
[FourSharp](Erdos272/FourSharp.lean) gives a valid 30-member example with four independent dependencies in the uncorrected feature matrix.
This is sharpness of the **four-column rank correction**, not sharpness of 101 for the original question.
[ActiveWindows](Erdos272/ActiveWindows.lean) also improves the restricted bound of 102 above to 101 under the same exclusions.
The 101 certificate uses the four-column bound; neither the sharpness example nor the restricted 101 theorem is needed.

## What remains

No 96-member family was found, and none of the theorems excludes **all** such families.
The next proof can split on a member of the 54-set list or exploit four specified long *intersections*, rather than searching every family without restrictions.
To settle the question one must either exhibit 96 sets or lower the upper bound from 101 to 95. A failed or interrupted search is not an upper bound.
No claim of priority is made.

## Reproduce

From this directory in the repository's Nix shell, with the pinned Lean and Mathlib **v4.36.0**:

```sh
lake exe cache get
lake build
lake env lean Check.lean
python audit.py

# Generate and kernel-check the separate, larger proof.
python generate_bound.py
lake build Erdos272Bounds
lake env lean CheckBound.lean

# Optional: audit the four-column refinement and its sharpness example.
lake build Erdos272.NeutralBound Erdos272.FourSharp Erdos272.ActiveWindows
lake env lean CheckRefinement.lean
```

[`generate_bound.py`](generate_bound.py) uses the project Python and a C++20 compiler to propose certificates, then writes the Lean source under the ignored `.lake/proof-src/`. No generated build artifacts need to be committed. The generator is not a verifier: an invalid coloring or an uncovered branch fails the Lean build. The proof is split over eight modules to allow parallel checking.

[`Check.lean`](Check.lean) and [`CheckBound.lean`](CheckBound.lean) print the axioms of the results. The only ones used are standard `propext`, `Classical.choice`, and `Quot.sound` (some results use fewer).
[`audit.py`](audit.py) is an independent exact-integer check of the counts. `--palettes` prints the rooted cover data.

Sources: [Erdős problem #272](https://www.erdosproblems.com/272); [T. Szabó, *Intersection properties of subsets of integers*, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf#page=21); [Z. Yang, *Exact values and exact upper bounds for families of integers with arithmetic progression intersections*, Theorems 1.1 and 1.4](https://arxiv.org/abs/2607.23004); Lyons's thirteen-point proof linked above.
