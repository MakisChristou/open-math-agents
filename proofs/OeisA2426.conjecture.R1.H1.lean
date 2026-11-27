import OMAReductions.R_OeisA2426_conjecture_R1
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Dvd

/-! Extracting the central coefficient via (1−X³)ᵖ/(1−X)ᵖ leaves
products of two binomial coefficients divisible by p. The leading
coefficient is handled by Vandermonde's identity. -/

namespace OMA.Trinomial
open Finset PowerSeries
open scoped PowerSeries

variable {R : Type*} [CommRing R]

lemma coeff_mul_nat (n b : ℕ) (F : R⟦X⟧) : coeff n (F*(b:R⟦X⟧))=coeff n F*(b:R) := by
  rw [show (b : R⟦X⟧)=C (b:R) by simp,coeff_mul_C]

lemma chooseQuadratic (k : ℕ) : coeff k ((1+X^2 : R⟦X⟧)^k) =
    if 2∣k then (k.choose (k/2):R) else 0 := by
  rw [add_comm,add_pow,map_sum]
  simp only [one_pow,mul_one,←pow_mul,coeff_mul_nat,coeff_X_pow]
  by_cases h : 2∣k
  · rw [if_pos h,sum_eq_single (k/2)]
    · rw [if_pos (show k=2*(k/2) by omega),one_mul]
    · intro j hj hj'
      rw [if_neg (by omega : k≠2*j),zero_mul]
    · intro hnot
      exact False.elim (hnot (mem_range.mpr (by omega)))
  · rw [if_neg h]
    apply sum_eq_zero
    intro j hj
    rw [if_neg (by omega : k≠2*j),zero_mul]

lemma sumEven (f : ℕ→R) (n : ℕ) :
    ∑ k∈range (n+1),(if 2∣k then f (k/2) else 0)=∑ j∈range (n/2+1),f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih]
    by_cases h : 2∣n+1
    · simp only [if_pos h,show (n+1)/2=n/2+1 by omega,sum_range_succ]
    · simp [h,show (n+1)/2=n/2 by omega]

lemma centralCoeff (n : ℕ) : coeff n ((1+X+X^2 : R⟦X⟧)^n)=(OeisA2426.a n : R) := by
  rw [show (1+X+X^2 : R⟦X⟧)=(1+X^2)+X by ring,add_pow,map_sum]
  calc
    _ = ∑ k∈range (n+1),(if 2∣k then (n.choose (2*(k/2)):R)*((2*(k/2)).choose (k/2):R) else 0) := by
      apply sum_congr rfl
      intro k hk
      have hkn : k≤n := by simpa using hk
      rw [coeff_mul_nat,coeff_mul_X_pow',if_pos (by omega),show n-(n-k)=k by omega,chooseQuadratic]
      by_cases h : 2∣k
      · simp only [if_pos h,show 2*(k/2)=k by omega,mul_comm]
      · simp [h]
    _ = _ := by rw [sumEven (fun j => (n.choose (2*j):R)*((2*j).choose j:R))]; simp [OeisA2426.a]

lemma centralAtPrime {p : ℕ} (hp : p.Prime) (hp3 : 3<p) :
    (((p-1+p).choose (p-1) : ℕ) : ZMod (p^2)) = 1 := by
  let R := ZMod (p^2)
  have hsq (k : ℕ) (hk : 0<k) (hk' : k<p) : ((p.choose k : ℕ):R)^2=0 := by
    rw [←Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow_of_dvd (hp.dvd_choose_self hk.ne' hk') 2)
  have hsum : ∑ i∈range (p+1),((p.choose i : ℕ):R)^2=2 := by
    rw [sum_range_succ]
    rw [sum_eq_single 0]
    · simp; norm_num
    · intro i hi hi0
      exact hsq i (by omega) (mem_range.mp hi)
    · simp [hp.pos]
  have hv : ((∑ i∈range (p+1),p.choose i^2 : ℕ) : ZMod (p^2)) = ((2*p).choose p : ZMod (p^2)) :=
    congrArg (fun v : ℕ => (v : ZMod (p^2))) (Nat.sum_range_choose_sq p)
  simp only [Nat.cast_sum,Nat.cast_pow] at hv
  rw [hsum] at hv
  have he : (p*2).choose p=2*(p-1+p).choose (p-1) := by
    have htop : p*2=(p-1+p)+1 := by omega
    have hlow : p=p-1+1 := by omega
    rw [htop]
    conv_lhs => arg 2; rw [hlow]
    rw [Nat.choose_succ_succ,Nat.choose_symm_of_eq_add (show p-1+p=(p-1)+p by rfl)]
    rw [show (p-1).succ=p by omega]
    omega
  have hv' : (2:R)=2*(((p-1+p).choose (p-1):ℕ):R) := by
    simpa only [show 2*p=p*2 by omega,he,Nat.cast_mul,Nat.cast_ofNat] using hv
  have hc : Nat.Coprime 2 (p^2) := ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right 2
  have hu : IsUnit (2:R) := by simpa using (ZMod.isUnit_iff_coprime 2 (p^2)).mpr hc
  apply hu.mul_right_cancel
  simpa [mul_comm] using hv'.symm

lemma numeratorTerm (U : R⟦X⟧) (p j b : ℕ) :
    coeff p (((-X^3 : R⟦X⟧)^j * (b : R⟦X⟧))*U) =
    ((-1:R)^j*(b:R))*(if 3*j≤p then coeff (p-3*j) U else 0) := by
  have he : (((-X^3 : R⟦X⟧)^j * (b : R⟦X⟧))*U) =
      ((U*X^(3*j))*(b : R⟦X⟧))*C ((-1:R)^j) := by
    rw [map_pow,map_neg,map_one,show (-X^3 : R⟦X⟧)=(-1)*(X^3) by ring,mul_pow,←pow_mul]
    ring
  rw [he,coeff_mul_C,coeff_mul_nat,coeff_mul_X_pow']
  ring

lemma main {p : ℕ} (hp : p.Prime) (hp3 : 3<p) : OeisA2426.a p ≡ 1 [MOD p^2] := by
  let R := ZMod (p^2)
  let U := (invOneSubPow R p).val
  let F := (1+X+X^2 : R⟦X⟧)
  have hp0 := hp.pos
  have hu (k : ℕ) : coeff k U = ((p-1+k).choose (p-1) : ℕ) := by
    dsimp [U]
    rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ hp0,coeff_mk]
  have he : F^p=(1-X^3)^p*U := by
    calc
      F^p = F^p*((1-X)^p*U) := by
        rw [←invOneSubPow_inv_eq_one_sub_pow,show (invOneSubPow R p).inv*U=1 from (invOneSubPow R p).inv_val,mul_one]
      _ = (1-X^3)^p*U := by
        rw [←mul_assoc,←mul_pow,show F*(1-X)=1-X^3 by dsimp [F]; ring]
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  rw [Nat.cast_one,←centralCoeff (R:=R)]
  change coeff p (F^p)=1
  rw [he,show (1-X^3 : R⟦X⟧)=-X^3+1 by ring,add_pow,sum_mul,map_sum]
  simp only [one_pow,mul_one,numeratorTerm]
  rw [sum_eq_single 0]
  · simp [hu,centralAtPrime hp hp3]
  · intro j hj hj0
    by_cases h : 3*j≤p
    · have hjp : j<p := by omega
      have hne : 3*j≠p := by
        rintro e
        have := (Nat.dvd_prime hp).mp (show 3∣p from ⟨j,e.symm⟩)
        omega
      have hd₁ := hp.dvd_choose_self hj0 hjp
      have hd₂ := hp.dvd_choose (a:=p-1) (b:=p-1+(p-3*j)) (by omega) (by omega) (by omega)
      have hprod : (p.choose j : R)*((p-1+(p-3*j)).choose (p-1) : R) = 0 := by
        rw [←Nat.cast_mul]
        exact (ZMod.natCast_eq_zero_iff ..).mpr (by simpa [pow_two] using Nat.mul_dvd_mul hd₁ hd₂)
      simp only [if_pos h,hu,mul_assoc,hprod,mul_zero]
    · simp [h]
  · simp

end OMA.Trinomial

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 := by
  intro p h3 hp
  exact OMA.Trinomial.main hp h3
