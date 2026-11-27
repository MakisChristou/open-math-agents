import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-! At a prime congruent to one modulo four, evaluate the Gaussian product
at both square roots of minus one modulo the required prime power. In
each evaluation it contains a product of consecutive residues. -/

namespace OMA.Moll
open Finset GaussianInt

lemma liftRoot {p e u : ℕ} (hp : p.Prime) (hp2 : p≠2) (he : 0<e) (hu : p^e∣u^2+1) :
    ∃ v : ℕ, p^(e+1)∣v^2+1 := by
  have hd : 2∣u*(u^2+3) := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.mul_mod,Nat.add_mod,Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one u with h|h <;> rw [h]
  obtain ⟨v,hv⟩ := hd
  refine ⟨v,?_⟩
  have hid : 4*(v^2+1)=(u^2+1)^2*(u^2+4) := by
    nlinarith only [congrArg (fun t : ℕ => t*t) hv]
  have hdiv : p^(e+1)∣(u^2+1)^2 := by
    refine (pow_dvd_pow p (show e+1≤e*2 by omega)).trans ?_
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd hu 2
  have hc : (p^(e+1)).Coprime 4 :=
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left _).pow_right 2
  exact hc.dvd_of_dvd_mul_left (hid ▸ dvd_mul_of_dvd_left hdiv _)

lemma root {p : ℕ} (hp : p.Prime) (h4 : p%4=1) (e : ℕ) : ∃ r : ℕ, p^e ∣ r^2+1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega)
  have hbase : p∣u.val^2+1 := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    push_cast
    simp only [ZMod.natCast_zmod_val,pow_two,←hu,neg_add_cancel]
  cases e with
  | zero => exact ⟨0,by simp⟩
  | succ e =>
    induction e with
    | zero => exact ⟨u.val,by simpa using hbase⟩
    | succ e ih =>
      obtain ⟨x,hx⟩ := ih
      exact liftRoot hp (by omega) (by omega) hx

def G (n : ℕ) : GaussianInt := ∏ k ∈ range (n+1), (⟨1,k⟩ : GaussianInt)

lemma imag (n : ℕ) : OeisA105751.a n=(G n).im := by
  have hh : GaussianInt.toComplex (G n)=∏ k ∈ range (n+1), (1+(k : ℂ)*Complex.I) := by
    simp [G,map_prod,GaussianInt.toComplex_def']
  change ⌊(∏ k ∈ range (n+1), (1+(k : ℂ)*Complex.I)).im⌋=_
  rw [←hh]
  rw [←GaussianInt.intCast_im,Int.floor_intCast]

lemma eval_zero {m n : ℕ} [NeZero m] (hfac : m ∣ n.factorial) (r : ZMod m) (hr : r*r = -1) :
    ((G n).re : ZMod m) + (G n).im*r=0 := by
  let ev : GaussianInt →+* ZMod m := Zsqrtd.lift ⟨r,by simpa using hr⟩
  change ev (G n)=0
  rw [G,map_prod]
  have hf : ∀ k : ℕ, ev ⟨1,k⟩ = r*((k : ZMod m)-r) := by
    intro k
    change (1 : ℤ)+(k : ℤ)*r=_
    push_cast
    linear_combination hr
  simp_rw [hf,prod_mul_distrib]
  apply mul_eq_zero_of_right
  have hdiv := hfac.trans (Nat.factorial_dvd_factorial (Nat.le_succ n))
  obtain ⟨c,hc⟩ := (show (m:ℤ) ∣ ∏ i ∈ range (n+1), (-(r.val:ℤ)+i) from
    (show (m:ℤ) ∣ ((n+1).factorial:ℤ) by exact_mod_cast hdiv).trans
      (Nat.factorial_coe_dvd_prod (n+1) (-r.val)))
  have hh := congrArg (fun x : ℤ => (x : ZMod m)) hc
  push_cast at hh
  simpa [sub_eq_add_neg,add_comm] using hh

lemma main {p : ℕ} (hp : p.Prime) (h4 : p%4=1) (n : ℕ) :
    (p : ℤ)^padicValNat p n.factorial ∣ OeisA105751.a n := by
  have : Fact p.Prime := ⟨hp⟩
  let e := padicValNat p n.factorial
  let m := p^e
  have : NeZero m := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hfac : m ∣ n.factorial := pow_padicValNat_dvd
  obtain ⟨u,hu⟩ := root hp h4 e
  let r : ZMod m := u
  have hr : r*r = -1 := by
    have := (ZMod.natCast_eq_zero_iff (u^2+1) m).mpr hu
    push_cast at this
    dsimp [r]
    linear_combination this
  have h₁ := eval_zero hfac r hr
  have h₂ := eval_zero hfac (-r) (by simpa using hr)
  have h3 : (2 : ZMod m)*(G n).im=0 := by linear_combination (-r)*h₁+r*h₂+2*((G n).im : ZMod m)*hr
  have hc : Nat.Coprime 2 m := ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right _
  have hfour : IsUnit (2 : ZMod m) := by simpa using (ZMod.isUnit_iff_coprime 2 m).mpr hc
  have hi : ((G n).im : ZMod m)=0 := (hfour.mul_right_eq_zero).mp h3
  rw [imag]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hi

end OMA.Moll

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp h4 n
  exact OMA.Moll.main hp h4 n
