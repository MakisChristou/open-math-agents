import OMAReductions.R_OeisA5258_conjecture_R1
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! At p = n + 1 the Apéry polynomial reduces to 1 modulo p, and its
leading coefficient contains exactly one factor of p. Gauss's lemma and
a coefficient comparison give the reciprocal Eisenstein criterion. -/

namespace OMA.Apery
open Polynomial Finset

def term (n k : ℕ) : ℕ := n.choose k ^ 2 * (n+k).choose k

noncomputable def poly (n : ℕ) : ℤ[X] := ∑ i ∈ range (n+1), C (term n i : ℤ)*X^i

lemma coeff (n i : ℕ) : (poly n).coeff i = if i ≤ n then (term n i : ℤ) else 0 := by
  simp [poly,finsetSum_coeff,mem_range]

lemma zeroCoeff (n : ℕ) : (poly n).coeff 0=1 := by simp [coeff,term]

lemma topCoeff (n : ℕ) : (poly n).coeff n = ((n+n).choose n:ℤ) := by simp [coeff,term]

lemma degree (n : ℕ) : (poly n).natDegree=n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    simp [coeff,hi.not_ge]
  · rw [topCoeff]
    exact_mod_cast (Nat.choose_pos (show n≤n+n by omega)).ne'

lemma primitive (n : ℕ) : (poly n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro z hz
  have h := (C_dvd_iff_dvd_coeff z _).mp hz 0
  rw [zeroCoeff] at h
  exact isUnit_of_dvd_one h

lemma reduction (n : ℕ) (hp : (n+1).Prime) : (poly n).map (Int.castRingHom (ZMod (n+1)))=1 := by
  ext i
  rw [coeff_map]
  rcases i with _|i
  · simp [zeroCoeff]
  · simp only [coeff,coeff_one, Nat.succ_ne_zero,if_false]
    split
    · rename_i hi
      have h : n+1 ∣ term n (i+1) := by
        apply dvd_mul_of_dvd_right
        exact hp.dvd_choose (by omega) (by omega) (by omega)
      simpa using (ZMod.natCast_eq_zero_iff _ _).mpr h
    · simp

lemma leadDiv {p : ℕ} [Fact p.Prime] (g : ℤ[X]) (hu : IsUnit (g.map (Int.castRingHom (ZMod p))))
    (hg : 0<g.natDegree) : (p:ℤ) ∣ g.leadingCoeff := by
  have hh := coeff_eq_zero_of_natDegree_lt (p:=g.map (Int.castRingHom (ZMod p)))
    (n:=g.natDegree) (by simpa [natDegree_eq_zero_of_isUnit hu] using hg)
  rw [coeff_map] at hh
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh

lemma irreducible (n : ℕ) (hn : 1≤n) (hp : (n+1).Prime) : Irreducible (poly n) := by
  let : Fact (n+1).Prime := ⟨hp⟩
  constructor
  · apply not_isUnit_of_natDegree_pos
    rw [degree]
    omega
  intro g h he
  have h0 : IsUnit (g.coeff 0*h.coeff 0) := by
    rw [←mul_coeff_zero,←he,zeroCoeff]
    exact isUnit_one
  have ofConstant (f : ℤ[X]) (hf : IsUnit (f.coeff 0)) (hd : f.natDegree=0) : IsUnit f := by
    rw [eq_C_of_natDegree_eq_zero hd]
    exact hf.map C
  by_cases gd : g.natDegree=0
  · exact Or.inl (ofConstant g (isUnit_of_mul_isUnit_left h0) gd)
  by_cases hd : h.natDegree=0
  · exact Or.inr (ofConstant h (isUnit_of_mul_isUnit_right h0) hd)
  have hu : IsUnit (g.map (Int.castRingHom (ZMod (n+1)))*h.map (Int.castRingHom (ZMod (n+1)))) := by
    rw [←Polynomial.map_mul,←he,reduction n hp]
    exact isUnit_one
  have hg := leadDiv g (isUnit_of_mul_isUnit_left hu) (Nat.pos_of_ne_zero gd)
  have hh := leadDiv h (isUnit_of_mul_isUnit_right hu) (Nat.pos_of_ne_zero hd)
  have hpow := mul_dvd_mul hg hh
  rw [←leadingCoeff_mul,←he,leadingCoeff,degree,topCoeff,←sq] at hpow
  have hN : (n+1)^2 ∣ (n+n).choose n := by exact_mod_cast hpow
  have upper := Nat.factorization_choose_le_one (k:=n) (show n+n < (n+1)^2 by nlinarith)
  have lower := (hp.pow_dvd_iff_le_factorization (Nat.choose_pos (show n≤n+n by omega)).ne').mp hN
  omega

lemma ratMap (n : ℕ) : (poly n).map (Int.castRingHom ℚ)=OeisA5258.aperyPoly n := by
  simp only [poly,OeisA5258.aperyPoly,term,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
  simp

theorem result (n : ℕ) (hn : 1≤n) (hp : (n+1).Prime) : Irreducible (OeisA5258.aperyPoly n) := by
  rw [←ratMap]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (primitive n)).mp (irreducible n hn hp)

end OMA.Apery

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := OMA.Apery.result
