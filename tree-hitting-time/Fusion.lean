module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Arithmetic of a pendant-path fusion

The parameters count the moved arm (`p`), stationary arm (`q`), and remainder
(`c`, including the joint). Pair sums count unordered pairs once.
-/

@[expose] public section

namespace Fusion

open Finset

/-- Wiener contribution `(n - 1) ΔW`. -/
def distanceGain (p q c : ℚ) : ℚ := (p + q + c - 1) * (p * q * (c - 1))

/-- Total absolute transmission-shift difference, after grouping pairs. -/
def penalty (p q c : ℚ) : ℚ :=
  p * c * (q * (c - 1 - p)) + p * q * (q * (c - 1) + p) +
  c * p * q * (q + 1) + p * q * (q^2 - 1) / 3

/-- Improvement over the reverse triangle inequality from the moved tip
paired with every vertex of the stationary arm. -/
def tipCredit (p q c : ℚ) : ℚ := 2 * q * (q * (c - 1) + p)

/-- The grouped lower bound is strictly positive for arms of *all* admissible
sizes, not just for parameters below a cutoff. -/
theorem budget_pos (p q c : ℚ) (hq : 1 ≤ q) (hp : q ≤ p) (hc : p + 1 ≤ c) :
    0 < distanceGain p q c - penalty p q c + tipCredit p q c := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hq1 : 0 ≤ q - 1 := by linarith
  have hq2 : 0 ≤ 2 * q - 1 := by linarith
  have hpc : 0 ≤ c - q - 1 := by linarith
  have hdiff : 0 ≤ p - q := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  calc
    0 < p * q * (q * (c - q - 1) + ((q - 1) * (2 * q - 1) + 3) / 3) +
        2 * q * (p - q) * (c - 1) * (p - 1) := by positivity
    _ = _ := by unfold distanceGain penalty tipCredit; ring

/-- Shift of an absolute difference relative to its worst possible decrease. -/
def credit (old shift : ℚ) : ℚ := |old + shift| - |old| + |shift|

theorem credit_nonneg (old shift : ℚ) : 0 ≤ credit old shift := by
  have h := abs_sub (old + shift) shift
  rw [add_sub_cancel_right] at h
  unfold credit
  linarith

theorem credit_of_nonneg {old shift : ℚ} (ho : 0 ≤ old) (hs : 0 ≤ shift) :
    credit old shift = 2 * shift := by
  simp only [credit, abs_of_nonneg ho, abs_of_nonneg hs, abs_of_nonneg (add_nonneg ho hs)]
  ring

/-- Reverse triangle inequality for all pairs, with the exact gain restored
on a selected subset whose old differences and shifts are nonnegative. -/
theorem selected_change_bound {α : Type*} {pairs good : Finset α} (hsub : good ⊆ pairs)
    (old shift : α → ℚ) (ho : ∀ i ∈ good, 0 ≤ old i) (hs : ∀ i ∈ good, 0 ≤ shift i) :
    2 * (∑ i ∈ good, shift i) - (∑ i ∈ pairs, |shift i|) ≤
      ∑ i ∈ pairs, (|old i + shift i| - |old i|) := by
  have h₁ : (∑ i ∈ good, credit (old i) (shift i)) ≤ ∑ i ∈ pairs, credit (old i) (shift i) :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => credit_nonneg (old i) (shift i)
  have h₂ : (∑ i ∈ good, credit (old i) (shift i)) = 2 * ∑ i ∈ good, shift i := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi => credit_of_nonneg (ho i hi) (hs i hi)
  rw [h₂] at h₁
  simp only [credit, sum_add_distrib] at h₁
  linarith

/-- Differences between a fixed shift and the stationary shifts in depth order.
`offset` is the difference before adding `2*p` for the first depth. -/
def depthSum (q : ℕ) (offset p : ℚ) : ℚ :=
  ∑ j ∈ range q, |offset + 2 * p * ((j : ℚ) + 1)|

/-- Shift differences within the stationary arm; each pair occurs once. -/
def internalSum (q : ℕ) (p : ℚ) : ℚ :=
  ∑ k ∈ range q, ∑ j ∈ range k, |2 * p * ((k : ℚ) - j)|

private theorem sum_affine (n : ℕ) (a b : ℚ) :
    (∑ j ∈ range n, (a + b * j)) = n * a + b * n * (n - 1 : ℚ) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

theorem depthSum_eq (q : ℕ) (u p : ℚ) (hu : 0 ≤ u) (hp : 0 ≤ p) :
    depthSum q u p = q * (u + p * (q + 1)) := by
  calc
    _ = ∑ j ∈ range q, ((u + 2 * p) + (2 * p) * j) := by
      unfold depthSum
      apply sum_congr rfl
      intro j _
      rw [abs_of_nonneg (by positivity)]
      ring
    _ = _ := by rw [sum_affine]; ring

theorem internalSum_eq (q : ℕ) (p : ℚ) (hp : 0 ≤ p) :
    internalSum q p = p * q * ((q : ℚ)^2 - 1) / 3 := by
  unfold internalSum
  induction q with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have inner : (∑ j ∈ range k, |2 * p * ((k : ℚ) - j)|) =
        ∑ j ∈ range k, ((2 * p * k) + (-2 * p) * j) := by
      apply sum_congr rfl
      intro j hj
      have hjk : (j : ℚ) ≤ k := by exact_mod_cast (mem_range.mp hj).le
      rw [abs_of_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hjk))]
      ring
    rw [inner, sum_affine, Nat.cast_succ]
    ring

/-- The strict budget before evaluating the sums over individual stationary
vertices and pairs. The last summand corrects the bound at the moved tip. -/
theorem finite_budget_pos (p q c : ℕ) (hq : 1 ≤ q) (hp : q ≤ p) (hc : p + 1 ≤ c) :
    let d : ℚ := q * ((c : ℚ) - 1 - p)
    0 < distanceGain p q c -
      (p * (c : ℚ) * |d| + p * depthSum q d p + c * depthSum q 0 p + internalSum q p) +
      2 * depthSum q d p := by
  dsimp only
  have hq' : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hp' : (q : ℚ) ≤ p := by exact_mod_cast hp
  have hc' : (p : ℚ) + 1 ≤ c := by exact_mod_cast hc
  have hd : 0 ≤ (q : ℚ) * ((c : ℚ) - 1 - p) := mul_nonneg (by positivity) (by linarith)
  rw [abs_of_nonneg hd, depthSum_eq _ _ _ hd (by positivity),
    depthSum_eq _ _ _ le_rfl (by positivity), internalSum_eq _ _ (by positivity)]
  convert budget_pos p q c hq' hp' hc' using 1
  unfold penalty tipCredit
  ring

end Fusion
