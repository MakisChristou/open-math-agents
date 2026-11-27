import FormalConjectures.OEIS.«111291»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The numbers 128*p*q have 32 divisors for distinct odd primes p and q.
Choose a fixed finite set of small odd primes with large reciprocal sum,
then count large primes q by Chebyshev's lower bound. Unique factorization
makes the resulting families disjoint. This gives the eventual estimate of
Colton, which also follows from Zelinsky's stronger theorem (2002). -/

namespace OMA.TauCount
open Finset Filter Real OeisA111291

lemma good {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h2 : 2 < p) (hlt : p < q) :
    (128*p*q).IsRefactorable := by
  have p2 : (128:ℕ).Coprime p := by
    change (2^7).Coprime p
    exact ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left _
  have q2 : (128:ℕ).Coprime q := by
    change (2^7).Coprime q
    exact ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left _
  have pq := (Nat.coprime_primes hp hq).mpr hlt.ne
  have pc := hp.divisors
  have qc := hq.divisors
  refine ⟨show 0 < 128*p*q from Nat.mul_pos (Nat.mul_pos (by decide) hp.pos) hq.pos, ?_⟩
  rw [Nat.Coprime.card_divisors_mul (q2.mul_left pq), Nat.Coprime.card_divisors_mul p2, pc, qc]
  have h128 : (128:ℕ).divisors.card = 8 := by decide
  simp [h128, Ne.symm hp.ne_one, Ne.symm hq.ne_one]
  exact ⟨4*p*q, by ring⟩

lemma mass : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 2 < p) ∧
    1024 ≤ ∑ p ∈ S, (1 / (p:ℝ)) := by
  classical
  have ub : ∃ T : Finset Nat.Primes, 1025 < ∑ p ∈ T, (1 / (p.val:ℝ)) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨T,ht⟩ := ub
  let U := T.image (fun p : Nat.Primes => p.val)
  have huge : 1025 < ∑ p ∈ U, (1 / (p:ℝ)) := by
    unfold U
    exact (Finset.sum_image (s:=T) (g:=fun p : Nat.Primes => p.val) (f:=fun x : ℕ => 1 / (x:ℝ)) (fun _ _ _ _ e => Subtype.ext e)).symm ▸ ht
  refine ⟨U.erase 2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hne,hp⟩ := Finset.mem_erase.mp hp
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q.property, lt_of_le_of_ne q.property.two_le hne.symm⟩
  · by_cases two : 2 ∈ U
    · have e := Finset.sum_erase_add U (fun p : ℕ => 1 / (p:ℝ)) two
      norm_num only [Nat.cast_ofNat] at e
      linarith
    · rw [Finset.erase_eq_of_notMem two]
      linarith

noncomputable def tail (K : ℕ) (y : ℝ) : Finset ℕ := (Nat.primesLE ⌊y⌋₊) \ (Nat.primesLE K)

lemma mem_tail {K q : ℕ} {y : ℝ} (h : q ∈ tail K y) :
    q.Prime ∧ K < q ∧ q ≤ ⌊y⌋₊ := by
  obtain ⟨hy,hK⟩ := Finset.mem_sdiff.mp h
  obtain ⟨hl,hp⟩ := Nat.mem_primesLE.mp hy
  exact ⟨hp, lt_of_not_ge (fun hk => hK (Nat.mem_primesLE.mpr ⟨hk,hp⟩)),hl⟩

lemma count (S : Finset ℕ) (K : ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ p ≤ K)
    {x : ℝ} (hx : 1 ≤ x) :
    ∑ p ∈ S, (tail K (x / (128*(p:ℝ)))).card ≤ countRefactorable x := by
  classical
  let T (p : ℕ) := tail K (x / (128*(p:ℝ)))
  rw [countRefactorable, dif_pos hx, Int.toNat_natCast]
  change ∑ p ∈ S, (T p).card ≤ ((Icc 1 ⌊x⌋₊).filter Nat.IsRefactorable).card
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun v : Sigma (fun _ : ℕ => ℕ) => 128*v.1*v.2)
  · rintro ⟨p,q⟩ h
    obtain ⟨hs,hq⟩ := Finset.mem_sigma.mp h
    obtain ⟨hp,h2,hK⟩ := hS p hs
    obtain ⟨prime,gt,hl⟩ := mem_tail hq
    have pos : 0 < 128*(p:ℝ) := by have := hp.pos; positivity
    have posY : 0 ≤ x / (128*(p:ℝ)) := div_nonneg (by linarith) pos.le
    have bound := (le_div_iff₀ pos).mp ((Nat.le_floor_iff posY).mp hl)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,good hp prime h2 (hK.trans_lt gt)⟩
    · exact Nat.mul_pos (Nat.mul_pos (by decide) hp.pos) prime.pos
    · apply Nat.le_floor_iff (by linarith : 0 ≤ x) |>.mpr
      push_cast
      linarith only [bound, show (128*(p:ℝ))*(q:ℝ) = q*(128*p) by ring]
  · rintro ⟨p,q⟩ ha ⟨r,s⟩ hb e
    obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hr,hs⟩ := Finset.mem_sigma.mp hb
    obtain ⟨pp,_,pk⟩ := hS p hp
    obtain ⟨pr,_,_⟩ := hS r hr
    obtain ⟨ps,sk,_⟩ := mem_tail hs
    change 128*p*q = 128*r*s at e
    have eq : p*q = r*s := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 128) (by simpa [Nat.mul_assoc] using e)
    have hdiv : p ∣ r*s := eq ▸ dvd_mul_right p q
    have same : p = r := by
      rcases pp.dvd_mul.mp hdiv with d | d
      · exact ((Nat.dvd_prime pr).mp d).resolve_left pp.ne_one
      · have := ((Nat.dvd_prime ps).mp d).resolve_left pp.ne_one
        omega
    subst r
    have : q = s := Nat.eq_of_mul_eq_mul_left pp.pos eq
    subst s
    rfl

lemma tail_lower (K : ℕ) : ∀ᶠ y : ℝ in atTop, y/(8*log y) ≤ ((tail K y).card:ℝ) := by
  have small := Real.isLittleO_log_id_atTop.bound (by norm_num : 0 < (1/16:ℝ))
  have shift : Tendsto (fun y : ℝ => y+2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have many := (Nat.tendsto_primeCounting.comp (tendsto_nat_floor_atTop (α := ℝ))).eventually
    (eventually_ge_atTop (2*K.primeCounting))
  filter_upwards [eventually_ge_atTop (4:ℝ), shift.eventually small, many] with y hy hs hm
  have hl : 0 < log y := log_pos (by linarith)
  have hs' : log (y+2) ≤ (y+2)/16 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by linarith : 1 ≤ y+2)),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y+2), div_eq_mul_inv, mul_comm] using hs
  have pi := (div_le_iff₀ hl).mp (Chebyshev.pi_ge' (by linarith : 1 < y))
  have half : y/4 ≤ (⌊y⌋₊.primeCounting:ℝ)*log y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ y-1) (show 0 ≤ log 2 - 1/2 by linarith [Real.log_two_gt_d9])]
  have hc : ⌊y⌋₊.primeCounting ≤ (tail K y).card + K.primeCounting := by
    simpa [tail, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_le_card_sdiff_add_card (s:= Nat.primesLE ⌊y⌋₊) (t:=Nat.primesLE K))
  change 2*K.primeCounting ≤ ⌊y⌋₊.primeCounting at hm
  have hc' : (⌊y⌋₊.primeCounting:ℝ) ≤ 2*(tail K y).card := by exact_mod_cast (show ⌊y⌋₊.primeCounting ≤ 2*(tail K y).card by omega)
  apply (div_le_iff₀ (show 0 < 8*log y by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right hc' hl.le]

lemma scaled (K p : ℕ) (hp : 0 < p) : ∀ᶠ x : ℝ in atTop,
    x / (1024 * log x) * (1 / (p:ℝ)) ≤ ((tail K (x/(128*(p:ℝ)))).card:ℝ) := by
  let d : ℝ := 128*p
  have pos : 0 < d := by dsimp [d]; positivity
  have hone : 1 ≤ d := by
    have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast hp
    dsimp [d]
    linarith
  have tend : Tendsto (fun x : ℝ => x/d) atTop atTop := (tendsto_div_const_atTop_of_pos pos).mpr tendsto_id
  filter_upwards [tend.eventually (tail_lower K), tend.eventually (eventually_gt_atTop (1:ℝ)),
    eventually_gt_atTop (1:ℝ)] with x h hbig hx
  apply le_trans _ h
  change _ ≤ (x/d)/(8*log (x/d))
  have hh : log (x/d) ≤ log x :=
    Real.log_le_log (by linarith) (div_le_self (by linarith) hone)
  have hxL := Real.log_pos hx
  have hdL := Real.log_pos hbig
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  calc
    x / (1024*log x) * (1/(p:ℝ)) = (x/d)/(8*log x) := by dsimp [d]; ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

end OMA.TauCount

open OMA.TauCount OeisA111291 Finset Filter Real in
theorem OMA.solution : type_of% @OeisA111291.conjecture := by
  obtain ⟨S,hS,hsum⟩ := mass
  let K := S.sup id
  have hK : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ p ≤ K := by
    intro p hp
    exact ⟨(hS p hp).1,(hS p hp).2,Finset.le_sup (f:=id) hp⟩
  have ev := (Filter.eventually_all_finset S).2 (fun p hp => scaled K p (hS p hp).1.pos)
  filter_upwards [ev,eventually_gt_atTop (1:ℝ)] with x h hx
  have hcount := count S K hK hx.le
  have e := Finset.sum_le_sum h
  rw [← Finset.mul_sum] at e
  have hcast : (∑ p ∈ S, ((tail K (x / (128*(p:ℝ)))).card:ℝ)) ≤ countRefactorable x := by
    exact_mod_cast hcount
  have logpos := Real.log_pos hx
  have xpos : 0 ≤ x/(1024*log x) := by positivity
  calc
    x/(2*log x) ≤ x/(1024*log x)*1024 := by
      field_simp
      linarith
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum xpos).trans (e.trans hcast)
