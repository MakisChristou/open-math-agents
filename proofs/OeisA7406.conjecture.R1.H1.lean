import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.FieldTheory.Finite.Basic

/-! The reciprocal-square form of Wolstenholme's congruence. Clearing
denominators is legitimate modulo p because none of 1 through p-1
vanishes. Inversion permutes the field, whose second power sum is zero. -/
namespace OMA.WolstenholmeSquares
open Finset

lemma inverse_sum (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∑ k ∈ Icc 1 (p-1), ((k : ZMod p)⁻¹)^2 = 0 := by
  have hs : Icc 1 (p-1) = (range p).erase 0 := by
    ext k
    simp only [mem_Icc, mem_erase, mem_range]
    omega
  rw [hs]
  have herase := sum_erase_add (range p) (fun k : ℕ => ((k : ZMod p)⁻¹)^2)
    (mem_range.mpr (by omega : 0 < p))
  simp only [Nat.cast_zero, inv_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at herase
  rw [herase, ← Fin.sum_univ_eq_sum_range]
  have cast_eq (i : Fin p) : (i.val : ZMod p) = ZMod.finEquiv p i := by
    obtain _|p := p
    · omega
    · exact Fin.cast_val_eq_self i
  simp_rw [cast_eq]
  trans ∑ x : ZMod p, (x⁻¹)^2
  · exact (ZMod.finEquiv p).toEquiv.sum_comp (fun x : ZMod p => (x⁻¹)^2)
  trans ∑ x : ZMod p, x^2
  · exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x : ZMod p => x^2)
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]
  omega

end OMA.WolstenholmeSquares

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := by
  intro p h3 hp
  letI : Fact p.Prime := ⟨hp⟩
  let D := (p-1).factorial
  let S := Finset.Icc 1 (p-1)
  let X := ∑ k ∈ S, (D / k)^2
  let Q : ℚ := ∑ k ∈ S, 1/(k:ℚ)^2
  have hk {k} (h : k ∈ S) : k ∣ D :=
    Nat.dvd_factorial (Finset.mem_Icc.mp h).1 (Finset.mem_Icc.mp h).2
  have hX : Q*(D:ℚ)^2 = X := by
    dsimp only [Q,X]
    rw [Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro k h
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by have := (Finset.mem_Icc.mp h).1; omega : k ≠ 0)
    rw [Nat.cast_div (hk h) hk0]
    field_simp
  have hmod : (X : ZMod p) = 0 := by
    dsimp only [X]
    push_cast
    calc
      _ = ∑ k ∈ S, (D : ZMod p)^2 * ((k : ZMod p)⁻¹)^2 := by
        apply Finset.sum_congr rfl
        intro k h
        have hb := Finset.mem_Icc.mp h
        have hk0 : (k : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt hb.1 (by omega)
        rw [Nat.cast_div (hk h) hk0, div_eq_mul_inv, mul_pow]
      _ = 0 := by rw [← Finset.mul_sum, OMA.WolstenholmeSquares.inverse_sum p h3, mul_zero]
  have hrel : (Q.num : ℤ) * (D : ℤ)^2 = (X : ℤ) * (Q.den : ℤ) := by
    have hrat : (Q.num : ℚ) * (D:ℚ)^2 = (X:ℚ) * (Q.den:ℚ) := by
      rw [← Rat.mul_den_eq_num, ← hX]
      ring
    exact_mod_cast hrat
  have hfield := congrArg (fun x : ℤ => (x : ZMod p)) hrel
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hmod, zero_mul] at hfield
  have hD : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (show ¬ p ≤ p-1 by omega) (hp.dvd_factorial.mp h)
  have hn := (mul_eq_zero.mp hfield).resolve_right (pow_ne_zero _ hD)
  have hd : (p : ℤ) ∣ Q.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
  simp only [OeisA89026.a, if_pos hp, Nat.gcd_eq_left_iff_dvd]
  exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
