import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace E272.Neutral
open Finset

/-- Any nonzero rational vector has a rational multiple whose entries are integral
    and not all even. Minimize the norm of one specified nonzero coordinate. -/
theorem primitive_parity {n : ℕ} (z : Fin n → ℚ) {k : Fin n} (hk : z k ≠ 0) :
    ∃ (r : ℚ) (b : Fin n → ℤ), r ≠ 0 ∧ (∀ i, (b i : ℚ) = r * z i) ∧ ∃ i, (b i : ZMod 2) ≠ 0 := by
  classical
  let D := ∏ i, (z i).den
  have hd : 0 < D := Finset.prod_pos (fun i _ => (z i).den_pos)
  have hdvd (i : Fin n) : (z i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let P := fun m : ℕ => ∃ (r : ℚ) (b : Fin n → ℤ), r ≠ 0 ∧ (∀ i, (b i : ℚ) = r * z i) ∧ (b k).natAbs = m
  have hex : ∃ m, P m := by
    let b : Fin n → ℤ := fun i => ((D / (z i).den : ℕ) : ℤ) * (z i).num
    refine ⟨(b k).natAbs, (D : ℚ), b, (by positivity), ?_, rfl⟩
    intro i
    have hmul := Nat.div_mul_cancel (hdvd i)
    have hq : ((D / (z i).den : ℕ) : ℚ) * (z i).den = D := by exact_mod_cast hmul
    have hh := Rat.num_div_den (z i)
    change (((((D / (z i).den : ℕ) : ℤ) * (z i).num : ℤ) : ℚ)) = _
    rw [Int.cast_mul,Int.cast_natCast]
    calc
      _ = ((D / (z i).den : ℕ) : ℚ) * ((z i).den * z i) := by
        congr 1
        have hh' : ((z i).den : ℚ) ≠ 0 := by exact_mod_cast (z i).den_nz
        rw [mul_comm]; exact (div_eq_iff hh').mp hh
      _ = (D : ℚ) * z i := by rw [← mul_assoc,hq]
  obtain ⟨r,b,hr,hb,he⟩ := Nat.find_spec hex
  refine ⟨r,b,hr,hb,?_⟩
  by_contra! h
  have even (i : Fin n) : 2 ∣ b i := by
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (b i) 0 2).mp (by simp [h])
    simpa using hh
  let d : Fin n → ℤ := fun i => b i / 2
  have htwo (i : Fin n) : d i * 2 = b i := Int.ediv_mul_cancel (even i)
  have hmin := Nat.find_min' hex (m := (d k).natAbs) (by
    refine ⟨r/2,d,(div_ne_zero hr (by norm_num)),?_ ,rfl⟩
    intro i
    have hD : (d i : ℚ) * 2 = (b i : ℚ) := by exact_mod_cast htwo i
    rw [hb] at hD; linarith)
  have hn : b k ≠ 0 := by intro e; have h := hb k; rw [e, Int.cast_zero] at h; exact mul_ne_zero hr hk h.symm
  have hpos : 0 < (b k).natAbs := Int.natAbs_pos.mpr hn
  have hh := Int.natAbs_ediv_of_dvd (even k)
  change (b k / 2).natAbs = _ at hh
  change Nat.find hex ≤ (b k / 2).natAbs at hmin
  simp only [show (2:ℤ).natAbs = 2 from rfl] at hh
  omega

end E272.Neutral
