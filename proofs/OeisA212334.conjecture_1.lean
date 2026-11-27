import FormalConjectures.OEIS.«212334»
import Mathlib.FieldTheory.Finite.Basic

/-! At a prime index the binomial product collapses, modulo the square of the prime,
to a sign. Pairing k with p-k reduces the remaining sum to a fourth-power sum.
A prior elementary proof was recorded by rbajaj5 in A212334EnhancedPrimeCongruence. -/
namespace OMA.NeighborWords
open Finset
def pairTerm (p i : ℕ) := (p-1).choose i * (p+i).choose i
def term (p k : ℕ) := p.choose k * (p-1).choose k * (p+k-1).choose k ^ 2

lemma pair_step (p i : ℕ) :
    pairTerm p (i+1)*(i+1)^2 = pairTerm p i * (p-(i+1))*(p+(i+1)) := by
  have h₁ := Nat.choose_succ_right_eq (p-1) i
  have h₂ := Nat.add_one_mul_choose_eq (p+i) i
  unfold pairTerm
  rw [show p+(i+1)=p+i+1 by omega]
  calc
    _ = ((p-1).choose (i+1)*(i+1))*((p+i+1).choose (i+1)*(i+1)) := by ring
    _ = _ := by rw [h₁,← h₂,show p-1-i=p-(i+1) by omega]; ring

lemma term_step (p i : ℕ) (hp : 0<p) :
    term p (i+1)*(i+1)^4 = p^3*(p-(i+1))*(pairTerm p i)^2 := by
  have h₁ := Nat.add_one_mul_choose_eq (p-1) i
  have h₂ := Nat.choose_succ_right_eq (p-1) i
  have h₃ := Nat.choose_succ_right_eq (p+i) i
  rw [show p-1+1=p by omega] at h₁
  rw [show p+i-i=p by omega] at h₃
  unfold term pairTerm
  rw [show p+(i+1)-1=p+i by omega]
  calc
    _ = (p.choose (i+1)*(i+1))*((p-1).choose (i+1)*(i+1))*((p+i).choose (i+1)*(i+1))^2 := by ring
    _ = _ := by rw [← h₁,h₂,h₃,show p-1-i=p-(i+1) by omega]; ring

lemma unit_of_mem {p k d : ℕ} (hp : p.Prime) (hd : 0<d) (hk : 0<k) (hl : k<p) :
    IsUnit (k : ZMod (p^d)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).2 (Nat.not_dvd_of_pos_of_lt hk hl)

lemma pair_mod (p i : ℕ) (hp : p.Prime) (hi : i<p) :
    (pairTerm p i : ZMod (p^2)) = (-1)^i := by
  induction i with
  | zero => simp [pairTerm]
  | succ i ih =>
    have hu := unit_of_mem (d:=2) hp (by decide) (by omega : 0 < i+1) hi
    have hs := congrArg (fun n : ℕ => (n : ZMod (p^2))) (pair_step p i)
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (show i+1≤p by omega),Nat.cast_add,Nat.cast_one] at hs
    have hn : (p:ZMod (p^2))^2=0 := by rw [← Nat.cast_pow,ZMod.natCast_self]
    apply ((hu.pow 2).mul_left_inj).1
    rw [Nat.cast_add,Nat.cast_one,hs]
    rw [ih (by omega),pow_succ (-1:ZMod (p^2)) i]
    linear_combination (-1:ZMod (p^2))^i * hn

def coeff (p k : ℕ) : ZMod (p^5) := (p-(k:ZMod (p^5))) * ((k:ZMod (p^5))⁻¹)^4

lemma weighted_pair (p i : ℕ) (hp : p.Prime) (hi : i<p) :
    (p:ZMod (p^5))^3 * (pairTerm p i)^2 = (p:ZMod (p^5))^3 := by
  have h := congrArg (·^2) (pair_mod p i hp hi)
  have one : ((-1:ZMod (p^2))^i)^2=1 := by rw [← pow_mul,mul_comm,pow_mul]; simp
  change ((pairTerm p i:ZMod (p^2))^2)=((-1:ZMod (p^2))^i)^2 at h
  rw [one,← Nat.cast_pow] at h
  have hm : pairTerm p i ^ 2 ≡ 1 [MOD p^2] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using h)
  have hh := hm.mul_left' (p^3)
  rw [show p^3*p^2=p^5 by ring] at hh
  rw [mul_one] at hh
  exact_mod_cast (ZMod.natCast_eq_natCast_iff ..).mpr hh

lemma term_mod (p k : ℕ) (hp : p.Prime) (hk : 0<k) (hl : k<p) :
    (term p k : ZMod (p^5)) = (p:ZMod (p^5))^3 * coeff p k := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hu := unit_of_mem (d:=5) hp (by decide) hk hl
  have ht := congrArg (fun n : ℕ => (n : ZMod (p^5))) (term_step p i hp.pos)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hl.le] at ht
  have hv := weighted_pair p i hp (by omega)
  have hunit := ZMod.mul_inv_of_unit _ hu
  apply (hu.pow 4).mul_left_inj.mp
  rw [ht,coeff]
  calc
    _ = (p^3*(pairTerm p i : ZMod (p^5))^2)*(p-(↑(i+1:ℕ):ZMod (p^5))) := by ring
    _ = _ := by rw [hv]; linear_combination -(p:ZMod (p^5))^3 * (p-(↑(i+1:ℕ):ZMod (p^5))) *
      (congrArg (·^4) hunit)


lemma reflect_coeff (p k : ℕ) (hp : p.Prime) (hk : 0<k) (hl : k<p) :
    (p:ZMod (p^5))^3 * (coeff p k + coeff p (p-k)) =
      5*(p:ZMod (p^5))^4 * ((k:ZMod (p^5))⁻¹)^4 := by
  let P : ZMod (p^5) := p
  let x : ZMod (p^5) := k
  let y : ZMod (p^5) := p-k
  have hy : y=P-x := rfl
  have ux : IsUnit x := unit_of_mem hp (by decide) hk hl
  have uy : IsUnit y := by
    have hu := unit_of_mem (d:=5) hp (by decide) (by omega : 0 < p-k) (show p-k<p by omega)
    simpa [y,Nat.cast_sub hl.le] using hu
  have nx := ZMod.mul_inv_of_unit x ux
  have ny := ZMod.mul_inv_of_unit y uy
  have nil : P^5=0 := by dsimp [P]; rw [← Nat.cast_pow,ZMod.natCast_self]
  unfold coeff
  rw [Nat.cast_sub hl.le,sub_sub_cancel]
  change P^3*(y*(x⁻¹)^4+x*(y⁻¹)^4)=5*P^4*(x⁻¹)^4
  apply ((ux.pow 4).mul (uy.pow 4)).mul_left_inj.mp
  calc
    _ = P^3*((x*x⁻¹)^4*y^5+(y*y⁻¹)^4*x^5) := by ring
    _ = P^3*(y^5+x^5) := by rw [nx,ny]; ring
    _ = 5*P^4*y^4 := by rw [hy]; linear_combination (-4*P^3+15*P^2*x-20*P*x^2+10*x^3)*nil
    _ = 5*P^4*(x⁻¹)^4*(x^4*y^4) := by
      calc
        _ = 5*P^4*y^4*(x*x⁻¹)^4 := by rw [nx]; ring
        _ = _ := by ring

lemma fourth_sum (p : ℕ) [Fact p.Prime] (hp : 5 < p) :
    ∑ k ∈ Ico 1 p, ((k : ZMod p)⁻¹)^4 = 0 := by
  have hs : Ico 1 p = (range p).erase 0 := by
    ext k; simp only [mem_Ico,mem_erase,mem_range]; omega
  rw [hs]
  have herase := sum_erase_add (range p) (fun k : ℕ => ((k : ZMod p)⁻¹)^4)
    (mem_range.mpr (by omega : 0 < p))
  simp only [Nat.cast_zero, inv_zero, zero_pow (by decide : 4 ≠ 0), add_zero] at herase
  rw [herase, ← Fin.sum_univ_eq_sum_range]
  have cast_eq (i : Fin p) : (i.val : ZMod p) = ZMod.finEquiv p i := by
    obtain _|p := p
    · omega
    · exact Fin.cast_val_eq_self i
  simp_rw [cast_eq]
  trans ∑ x : ZMod p, (x⁻¹)^4
  · exact (ZMod.finEquiv p).toEquiv.sum_comp (fun x : ZMod p => (x⁻¹)^4)
  trans ∑ x : ZMod p, x^4
  · exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x : ZMod p => x^4)
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

lemma annihilate (p : ℕ) (hp : p.Prime) (h5 : 5≤p) :
    5*(p:ZMod (p^5))^4 * ∑ k ∈ Ico 1 p, ((k:ZMod (p^5))⁻¹)^4 = 0 := by
  by_cases h : p=5
  · subst p
    decide +kernel
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f := ZMod.castHom (dvd_pow_self p (by decide : 5≠0)) (ZMod p)
  let S : ZMod (p^5) := ∑ k ∈ Ico 1 p, ((k:ZMod (p^5))⁻¹)^4
  have hf : f S = 0 := by
    dsimp only [S]
    rw [map_sum,← fourth_sum p (by omega)]
    apply sum_congr rfl
    intro k hk
    obtain ⟨h₀,h₁⟩ := mem_Ico.mp hk
    have hu := ZMod.mul_inv_of_unit (k:ZMod (p^5)) (unit_of_mem hp (by decide) h₀ h₁)
    have hv := congrArg f hu
    simp only [map_mul,map_natCast,map_one] at hv
    have hx : (k:ZMod p) ≠ 0 := by
      rw [Ne,ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt h₀ h₁
    rw [map_pow]
    congr 1
    apply mul_left_cancel₀ hx
    rw [hv,mul_inv_cancel₀ hx]
  have hcast := map_natCast f S.val
  rw [ZMod.natCast_zmod_val,hf] at hcast
  obtain ⟨d,hd⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast.symm
  have he : S=(p:ZMod (p^5))*(d:ZMod (p^5)) := by
    calc
      S = S.val := (ZMod.natCast_zmod_val _).symm
      _ = _ := by rw [hd,Nat.cast_mul]
  change 5*(p:ZMod (p^5))^4*S=0
  rw [he]
  have hnil : (p:ZMod (p^5))^5=0 := by rw [← Nat.cast_pow,ZMod.natCast_self]
  linear_combination 5*(d:ZMod (p^5))*hnil

lemma vanish (p : ℕ) (hp : p.Prime) (h5 : 5≤p) :
    (∑ k ∈ Ico 1 p, (term p k : ZMod (p^5))) = 0 := by
  let S := ∑ k ∈ Ico 1 p, (p:ZMod (p^5))^3 * coeff p k
  have hS : ∑ k ∈ Ico 1 p, (term p k : ZMod (p^5)) = S := by
    apply sum_congr rfl
    intro k hk
    exact term_mod p k hp (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
  rw [hS]
  have href : ∑ k ∈ Ico 1 p, (p:ZMod (p^5))^3*coeff p (p-k) = S := by
    simpa [S] using (sum_Ico_reflect (fun j => (p:ZMod (p^5))^3*coeff p j) 1 (by omega : p≤p+1))
  have htot : S+S=0 := by
    calc
      S+S = ∑ k ∈ Ico 1 p, ((p:ZMod (p^5))^3*coeff p k+(p:ZMod (p^5))^3*coeff p (p-k)) := by
        rw [sum_add_distrib,href]
      _ = ∑ k ∈ Ico 1 p, 5*(p:ZMod (p^5))^4*((k:ZMod (p^5))⁻¹)^4 := by
        apply sum_congr rfl
        intro k hk
        rw [← mul_add]
        exact reflect_coeff p k hp (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
      _ = 0 := by rw [← Finset.mul_sum,annihilate p hp h5]
  have hu := unit_of_mem (k:=2) (d:=5) hp (by decide) (by decide) (by omega)
  apply hu.mul_left_inj.mp
  simpa [mul_two] using htot

end OMA.NeighborWords

open Finset OMA.NeighborWords

theorem OMA.solution : type_of% @OeisA212334.conjecture_1 := by
  intro p hp h5
  have hsplit : OeisA212334.a p = 1+∑ k ∈ Ico 1 p, term p k := by
    rw [OeisA212334.a,if_neg hp.ne_zero]
    change ∑ k ∈ range p, term p k = _
    rw [← sum_range_add_sum_Ico (f:=term p) (show 1≤p by omega)]
    simp [term]
  have hm : (OeisA212334.a p : ZMod (p^5))=1 := by
    rw [hsplit,Nat.cast_add,Nat.cast_sum,Nat.cast_one,OMA.NeighborWords.vanish p hp h5,add_zero]
  have hv := (ZMod.natCast_eq_natCast_iff (OeisA212334.a p) 1 (p^5)).mp (by simpa using hm)
  have hpow : 1 < p^5 := one_lt_pow₀ (by omega) (by decide)
  simpa [Nat.ModEq,Nat.mod_eq_of_lt hpow] using hv
