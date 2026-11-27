module

public import VeryWellCovered.Defs

@[expose] public section

/-! Exact coefficient comparisons for the leafy extension on 14,592 vertices. -/

namespace VeryWellCovered

/-- Summand contributed by choosing `j` cliques on a side with `m` cliques of size `q`. -/
private def term (m q n k j : ℕ) : ℕ :=
  m.choose j * q ^ j * (n - j).choose (k - j)

private def partialSum (m q n k t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, term m q n k (j + 1)

private theorem partialSum_succ (m q n k t : ℕ) :
    partialSum m q n k (t + 1) = partialSum m q n k t + term m q n k (t + 1) :=
  Finset.sum_range_succ _ _

private theorem partialSum_stable (m q n k t : ℕ) (h : m ≤ t) :
    partialSum m q n k t = partialSum m q n k m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, partialSum_succ, ih]
    simp [term, Nat.choose_eq_zero_of_lt (show m < m + d + 1 by omega)]

private theorem split_count (k : ℕ) :
    leafyCount 7296 baseCount k = (7296 : ℕ).choose k
      + partialSum 192 30 7296 k k + partialSum 768 2 7296 k k := by
  unfold leafyCount
  rw [Finset.sum_range_succ']
  simp only [baseCount, Nat.add_one_ne_zero, ite_false, ite_true, Nat.sub_zero,
    Nat.add_mul, Finset.sum_add_distrib, one_mul, term, partialSum]
  rw [Nat.add_comm (_ + _) _, ← Nat.add_assoc]

/-- The two adjacent-binomial identities give the next summand with one exact division. -/
private theorem next_term (m q n k j : ℕ) (hj : j < k) (hk : k ≤ n) :
    term m q n k j * (m - j) * q * (k - j) / ((j + 1) * (n - j)) = term m q n k (j + 1) := by
  have hden : 0 < (j + 1) * (n - j) := Nat.mul_pos (by omega) (by omega)
  apply Nat.div_eq_of_eq_mul_right hden
  have hc := Nat.add_one_mul_choose_eq (n - (j + 1)) (k - (j + 1))
  rw [show n - (j + 1) + 1 = n - j by omega, show k - (j + 1) + 1 = k - j by omega] at hc
  unfold term
  rw [pow_succ]
  calc
    _ = (m.choose j * (m - j)) * (q ^ j * q) * ((n - j).choose (k - j) * (k - j)) := by ac_rfl
    _ = _ := by rw [← Nat.choose_succ_right_eq, ← hc]; ac_rfl

/-- Initialize the `j = 0` term without reducing the Pascal recursion for `Nat.choose`. -/
private def binom (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (binom n k * (n - k)) / (k + 1)

/-- Accumulate the next `l` positive-index terms, starting from the term at index `j`. -/
private def sideSum (m q n k : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | l + 1, j, term, acc =>
    let next := (term * (m - j) * q * (k - j)) / ((j + 1) * (n - j))
    sideSum m q n k l (j + 1) next (acc + next)

private def evalCount (k : ℕ) : ℕ :=
  let t := binom 7296 k
  t + sideSum 192 30 7296 k 192 0 t 0 + sideSum 768 2 7296 k 768 0 t 0

private theorem binom_eq (n k : ℕ) : binom n k = n.choose k := by
  induction k with
  | zero => simp [binom]
  | succ k ih =>
    rw [binom, ih, ← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (by omega)]

private theorem sideSum_eq (m q n k : ℕ) (hk : k ≤ n) (l j : ℕ) (hj : j + l ≤ k) :
    sideSum m q n k l j (term m q n k j) (partialSum m q n k j) = partialSum m q n k (j + l) := by
  induction l generalizing j with
  | zero => rfl
  | succ l ih =>
    rw [sideSum, next_term m q n k j (by omega) hk, ← partialSum_succ, ih (j + 1) (by omega)]
    congr 1; omega

private theorem evalCount_eq (k : ℕ) (hk : 768 ≤ k) (hn : k ≤ 7296) :
    evalCount k = leafyCount 7296 baseCount k := by
  have side (m q : ℕ) (hm : m ≤ k) := sideSum_eq m q 7296 k hn m 0 (by omega)
  have ht (m q : ℕ) : term m q 7296 k 0 = (7296 : ℕ).choose k := by simp [term]
  have hz (m q : ℕ) : partialSum m q 7296 k 0 = 0 := by simp [partialSum]
  simp only [ht, hz, Nat.zero_add] at side
  rw [evalCount, binom_eq, split_count, partialSum_stable 192 30 7296 k k (by omega),
    partialSum_stable 768 2 7296 k k hk]
  rw [side 192 30 (by omega), side 768 2 hk]

/-- At index 3789 the coefficient is strictly smaller than both exterior coefficients. -/
theorem leafyCount_valley :
    leafyCount 7296 baseCount 3789 < leafyCount 7296 baseCount 3738 ∧
    leafyCount 7296 baseCount 3789 < leafyCount 7296 baseCount 3840 := by
  rw [← evalCount_eq 3789 (by decide) (by decide), ← evalCount_eq 3738 (by decide) (by decide),
    ← evalCount_eq 3840 (by decide) (by decide)]
  decide +kernel

/-- The strict valley prevents the presence of a mode. -/
theorem leafyCount_not_isUnimodal : ¬ IsUnimodal (leafyCount 7296 baseCount) := by
  intro ⟨m, hinc, hdec⟩
  obtain hm | hm := le_total 3789 m
  · exact leafyCount_valley.1.not_ge
      (hinc (show 3738 ≤ m by omega) hm (by decide : 3738 ≤ 3789))
  · exact leafyCount_valley.2.not_ge
      (hdec hm (show m ≤ 3840 by omega) (by decide : 3789 ≤ 3840))

end VeryWellCovered
