# Erdős #272 on fourteen points

**Status: Lean-checked structural result; the unrestricted maximum is not determined here.**
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

## What remains

No 96-member family was found, and none of the theorems excludes **all** such families.
The next proof can split on a member of the 54-set list or exploit four specified long *intersections*, rather than searching every family without restrictions.
An experimental clique search was stopped; no theorem depends on it or on Python output.
No claim of priority is made.

## Reproduce

From this directory in the repository's Nix shell, with the pinned Lean and Mathlib **v4.36.0**:

```sh
lake exe cache get
lake build
lake env lean Check.lean
python audit.py
```

[`Check.lean`](Check.lean) prints the axioms of the results. The only ones used are standard `propext`, `Classical.choice`, and `Quot.sound` (some results use fewer).
[`audit.py`](audit.py) is an independent exact-integer check of the counts. `--palettes` prints the rooted cover data.

Sources: [Erdős problem #272](https://www.erdosproblems.com/272); [T. Szabó, *Intersection properties of subsets of integers*, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf#page=21); [Z. Yang, *Exact values and exact upper bounds for families of integers with arithmetic progression intersections*, Theorems 1.1 and 1.4](https://arxiv.org/abs/2607.23004); Lyons's thirteen-point proof linked above.
