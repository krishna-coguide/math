import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Erdos272.Basic

namespace E272
namespace RankProof
open Finset
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

instance : Fintype Mask := Fintype.ofEquiv (Fin (2^14))
  { toFun := BitVec.ofFin, invFun := BitVec.toFin, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

def inc (t a : Mask) : ℚ := if sub t a then 1 else 0
def feature (l : List Mask) (a : Mask) (i : Fin l.length) : ℚ := inc l[i] a

theorem inc_inter (t a b : Mask) : inc t a * inc t b = inc t (a &&& b) := by
  have h : (t &&& (a &&& b) = t) ↔ (t &&& a = t ∧ t &&& b = t) := by
    constructor
    · intro h
      constructor
      · calc
          t &&& a = (t &&& (a &&& b)) &&& a := by rw [h]
          _ = t &&& ((a &&& a) &&& b) := by ac_rfl
          _ = t := by simpa using h
      · calc
          t &&& b = (t &&& (a &&& b)) &&& b := by rw [h]
          _ = t &&& (a &&& (b &&& b)) := by ac_rfl
          _ = t := by simpa using h
    · rintro ⟨ha,hb⟩; rw [← BitVec.and_assoc,ha,hb]
  simp only [inc, sub, beq_iff_eq, h]
  split_ifs <;> simp_all

theorem dot_count (l : List Mask) (a b : Mask) :
    (∑ i : Fin l.length, feature l a i * feature l b i) =
      ((l.countP fun t => sub t (a &&& b)) : ℚ) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    change (∑ i : Fin (xs.length + 1), feature (x::xs) a i * feature (x::xs) b i) = _
    rw [Fin.sum_univ_succ]
    change inc x a * inc x b + (∑ i : Fin xs.length, feature xs a i * feature xs b i) = _
    rw [inc_inter, ih, List.countP_cons]
    by_cases h : sub x (a &&& b) = true <;> simp [inc, h, add_comm]

theorem gram (a b : Mask) :
    (∑ i, feature pos a i * feature pos b i) =
      (∑ j, feature neg a j * feature neg b j) + (score (a &&& b) : ℚ) := by
  rw [dot_count, dot_count]; simp [score]

theorem expansion {I J : Type*} [Fintype I] [Fintype J]
    (c : I → ℚ) (u : I → J → ℚ) :
    (∑ j, (∑ a, c a * u a j)^2) = ∑ a, ∑ b, c a * c b * (∑ j, u a j * u b j) := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ a, ∑ j, ∑ b, c b * u b j * (c a * u a j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro j _; ring

theorem gram_kernel {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
    (u : I → J → ℚ) (v : I → K → ℚ) (d c : I → ℚ)
    (diag : ∀ i, 0 ≤ d i)
    (hi : ∀ a b, (∑ j, u a j * u b j) = (∑ j, v a j * v b j) + if a = b then d a else 0)
    (hc : ∀ j, ∑ a, c a * u a j = 0) :
    (∀ k, ∑ a, c a * v a k = 0) ∧ ∀ i, 0 < d i → c i = 0 := by
  classical
  have h : (0 : ℚ) = (∑ k, (∑ a, c a * v a k)^2) + ∑ i, c i ^ 2 * d i := by
    calc
      0 = ∑ j, (∑ a, c a * u a j)^2 := by simp [hc]
      _ = _ := expansion c u
      _ = _ := by simp_rw [hi, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]; simp [← expansion, pow_two]
  have hn : ∀ i, 0 ≤ c i ^ 2 * d i := fun i => mul_nonneg (sq_nonneg _) (diag i)
  have h₁ := Finset.sum_nonneg (s := Finset.univ) (fun (k : K) _ => sq_nonneg (∑ a, c a * v a k))
  have h₂ := Finset.sum_nonneg (s := Finset.univ) (fun (i : I) _ => hn i)
  constructor
  · intro k; have e := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ Finset.univ) => sq_nonneg (∑ a, c a * v a k))).mp (le_antisymm (by linarith) h₁) k (Finset.mem_univ _)
    exact (sq_eq_zero_iff.mp e)
  · intro i hd
    have e := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)).mp (le_antisymm (by linarith) h₂) i (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_right hd.ne')

end RankProof
end E272
