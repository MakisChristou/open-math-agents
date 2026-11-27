import FormalConjectures.Wikipedia.RefactorableNumber
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.PSeries

/-! Kennedy and Cooper (1990). A refactorable number having k prime divisors
of multiplicity one must be a multiple of 2^k. We find k such primes outside
a set of arbitrarily small upper density, using disjoint finite prime sets. -/

namespace OMA.KennedyCooper
open Finset Filter
open scoped Topology
noncomputable section

open scoped Classical in
def part (A : Set ℕ) (N : ℕ) : Finset ℕ := (range N).filter (· ∈ A)

lemma mem_part {A : Set ℕ} {N n : ℕ} : n ∈ part A N ↔ n < N ∧ n ∈ A := by
  classical
  simp [part]

def count (A : Set ℕ) (N : ℕ) : ℕ := (part A N).card

def Bound (A : Set ℕ) (d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, (count A N : ℝ) ≤ d*N + C

lemma Bound.mono {A B : Set ℕ} {a b : ℝ} (h : Bound B b) (hab : A ⊆ B) (hba : b ≤ a) :
    Bound A a := by
  classical
  obtain ⟨C,hC⟩ := h
  refine ⟨C,fun N => ?_⟩
  have cc : count A N ≤ count B N := by
    apply card_le_card
    intro n hn
    exact mem_part.mpr ⟨(mem_part.mp hn).1,hab (mem_part.mp hn).2⟩
  calc
    (count A N : ℝ) ≤ count B N := by exact_mod_cast cc
    _ ≤ b*N+C := hC N
    _ ≤ a*N+C := by gcongr

lemma Bound.union {A B : Set ℕ} {a b : ℝ} (ha : Bound A a) (hb : Bound B b) :
    Bound (A ∪ B) (a+b) := by
  classical
  obtain ⟨C,hC⟩ := ha
  obtain ⟨D,hD⟩ := hb
  refine ⟨C+D,fun N => ?_⟩
  have ab : count (A ∪ B) N ≤ count A N + count B N := by
    unfold count part
    convert card_union_le ((range N).filter (· ∈ A)) ((range N).filter (· ∈ B)) using 1
    congr 1
    ext n
    simp
    tauto
  have h : (count (A ∪ B) N : ℝ) ≤ count A N + count B N := by exact_mod_cast ab
  linarith [hC N,hD N]

lemma bound_empty : Bound ∅ 0 := by
  refine ⟨0,fun N => ?_⟩
  simp [count,part]

lemma bound_finite_union (S : Finset ℕ) (A : ℕ → Set ℕ) (d : ℕ → ℝ)
    (h : ∀ p ∈ S, Bound (A p) (d p)) :
    Bound {n | ∃ p ∈ S, n ∈ A p} (∑ p ∈ S, d p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using bound_empty
  | @insert p S hp ih =>
    rw [sum_insert hp]
    apply ((h p (mem_insert_self ..)).union (ih (fun q hq => h q (mem_insert_of_mem hq)))).mono _ le_rfl
    rintro n ⟨q,hq,hqn⟩
    rcases mem_insert.mp hq with rfl | hq
    · exact Or.inl hqn
    · exact Or.inr ⟨q,hq,hqn⟩

lemma bound_residues {m : ℕ} (_hm : 0 < m) (R : Finset ℕ) :
    Bound {n | n % m ∈ R} ((R.card : ℝ)/m) := by
  classical
  refine ⟨R.card,fun N => ?_⟩
  have hc : count {n | n % m ∈ R} N ≤ ((range (N/m+1)) ×ˢ R).card := by
    apply card_le_card_of_injOn (fun n : ℕ => (n/m,n%m))
    · intro n hn
      obtain ⟨hN,hR⟩ := mem_part.mp hn
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hN))),hR⟩
    · intro n hn k hk e
      have e₁ := congrArg Prod.fst e
      have e₂ := congrArg Prod.snd e
      change n/m = k/m at e₁
      change n%m = k%m at e₂
      calc
        n = n%m + m*(n/m) := (Nat.mod_add_div n m).symm
        _ = k%m + m*(k/m) := by rw [e₁,e₂]
        _ = k := Nat.mod_add_div k m
  rw [card_product,card_range] at hc
  have hc' : (count {n | n % m ∈ R} N : ℝ) ≤ ((N/m : ℕ) + 1 : ℝ)*R.card := by exact_mod_cast hc
  calc
    _ ≤ _ := hc'
    _ ≤ ((N:ℝ)/m+1)*R.card := by gcongr; exact Nat.cast_div_le
    _ = _ := by ring

lemma bound_mult {m : ℕ} (hm : 0 < m) : Bound {n | m ∣ n} (1/(m:ℝ)) := by
  apply (bound_residues hm {0}).mono
  · intro n hn
    exact mem_singleton.mpr (Nat.mod_eq_zero_of_dvd hn)
  · simp

lemma bound_coprime {m : ℕ} (hm : 0 < m) :
    Bound {n | m.Coprime n} ((m.totient:ℝ)/m) := by
  classical
  apply (bound_residues hm ((range m).filter (m.Coprime ·))).mono _ (by rw [Nat.totient_eq_card_coprime])
  intro n hn
  change n % m ∈ (range m).filter (m.Coprime ·)
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (Nat.mod_lt _ hm), ?_⟩
  change m.gcd (n % m) = 1
  rw [Nat.gcd_comm, ← Nat.gcd_rec]
  exact hn

lemma prime_mass (T : Finset ℕ) (K : ℝ) : ∃ S : Finset ℕ, Disjoint S T ∧
    (∀ p ∈ S, p.Prime) ∧ K < ∑ p ∈ S, (1/(p:ℝ)) := by
  classical
  let B := ∑ p ∈ T, (1/(p:ℝ))
  have ub : ∃ U : Finset Nat.Primes, K+B < ∑ p ∈ U, (1/(p.val:ℝ)) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨U,hu⟩ := ub
  let V := U.image (fun p : Nat.Primes => p.val)
  have big : K+B < ∑ p ∈ V, (1/(p:ℝ)) := by
    unfold V
    exact (Finset.sum_image (s:=U) (g:=fun p : Nat.Primes => p.val) (f:=fun x : ℕ => 1/(x:ℝ)) (fun _ _ _ _ e => Subtype.ext e)).symm ▸ hu
  refine ⟨V \ T, (Finset.disjoint_left.mpr fun _ h => (mem_sdiff.mp h).2), ?_, ?_⟩
  · intro p hp
    obtain ⟨q,_,rfl⟩ := mem_image.mp (mem_sdiff.mp hp).1
    exact q.property
  · have sub : ∑ p ∈ V ∩ T, (1/(p:ℝ)) ≤ B :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => by positivity)
    have e := sum_sdiff (f:=fun p : ℕ => 1/(p:ℝ)) (inter_subset_left (s₁:=V) (s₂:=T))
    have diff : V \ (V ∩ T) = V \ T := by ext; simp
    rw [diff] at e
    linarith


lemma prod_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1-1/(p:ℝ))) * (1+∑ p ∈ S, 1/(p:ℝ)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have primes := fun q hq => hS q (mem_insert_of_mem hq)
    have pp := (hS p (mem_insert_self ..)).one_le
    have nonneg : 0 ≤ ∏ q ∈ S, (1-1/(q:ℝ)) := by
      apply prod_nonneg
      intro q hq
      have h : (1:ℝ) ≤ q := by exact_mod_cast (primes q hq).one_le
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) h |>.trans (by norm_num))
    have mass : 0 ≤ ∑ q ∈ S, 1/(q:ℝ) := by positivity
    rw [prod_insert hp,sum_insert hp]
    refine le_trans ?_ (ih primes)
    let t := 1/(p:ℝ)
    let M := ∑ q ∈ S, 1/(q:ℝ)
    let V := ∏ q ∈ S, (1-1/(q:ℝ))
    change (1-t)*V*(1+(t+M)) ≤ V*(1+M)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hM : 0 ≤ M := mass
    have hV : 0 ≤ V := nonneg
    nlinarith [mul_nonneg hV (mul_nonneg ht hM), mul_nonneg hV (sq_nonneg t)]

lemma ratio_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    let m := ∏ p ∈ S, p
    ((m.totient : ℝ)/m) * (1+∑ p ∈ S, 1/(p:ℝ)) ≤ 1 := by
  classical
  dsimp only
  let m := ∏ p ∈ S, p
  have hm : 0 < m := prod_pos fun q hq => (hS q hq).pos
  have hq := Nat.totient_eq_mul_prod_factors m
  rw [show m.primeFactors = S from Nat.primeFactors_prod hS] at hq
  have hr : (m.totient:ℝ) = m * ∏ q ∈ S, (1-(q:ℝ)⁻¹) := by simpa using congrArg (fun x : ℚ => (x:ℝ)) hq
  change ((m.totient:ℝ)/m) * _ ≤ _
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hr,mul_div_cancel_left₀ _ hm']
  simpa [one_div] using prod_bound S hS

def simple (p n : ℕ) : Prop := p ∣ n ∧ ¬p^2 ∣ n

lemma block (T : Finset ℕ) {e : ℝ} (he : 0 < e) :
    ∃ S : Finset ℕ, Disjoint S T ∧ (∀ p ∈ S, p.Prime) ∧
      Bound {n | ¬ ∃ p ∈ S, simple p n} e := by
  classical
  have summ : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  obtain ⟨U,hU⟩ := summable_iff_vanishing_norm.mp summ (e/2) (by positivity)
  obtain ⟨S,hS,pr,mass⟩ := prime_mass (U ∪ T) (2/e)
  have disU : Disjoint S U := hS.mono_right subset_union_left
  have disT : Disjoint S T := hS.mono_right subset_union_right
  refine ⟨S,disT,pr,?_⟩
  let m := ∏ q ∈ S, q
  have hm : 0 < m := prod_pos fun q hq => (pr q hq).pos
  have hr := ratio_bound S pr
  change (m.totient:ℝ)/m * _ ≤ 1 at hr
  have rm : 0 ≤ (m.totient:ℝ)/m := by positivity
  have rt : (m.totient:ℝ)/m ≤ e/2 := by
    have hl : 2/e ≤ 1+∑ q ∈ S, 1/(q:ℝ) := by linarith
    have h := (mul_le_mul_of_nonneg_left hl rm).trans hr
    field_simp [he.ne'] at h
    apply (div_le_iff₀ (by exact_mod_cast hm : (0:ℝ) < m)).mpr
    linarith
  have hs : ∑ q ∈ S, 1/(q:ℝ)^2 ≤ e/2 := by
    have h := hU S disU
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.le
  have sq := bound_finite_union S (fun q => {n | q^2 ∣ n}) (fun q => 1/(q:ℝ)^2)
    (fun q hq => by simpa using bound_mult (pow_pos (pr q hq).pos 2))
  apply ((bound_coprime hm).union sq).mono _ (by linarith)
  intro n hn
  by_cases hc : m.Coprime n
  · exact Or.inl hc
  · right
    change ¬ (∏ q ∈ S, q).Coprime n at hc
    rw [Nat.coprime_prod_left_iff] at hc
    push Not at hc
    obtain ⟨q,hq,hc⟩ := hc
    have hd : q ∣ n := by
      by_contra nope
      exact hc ((pr q hq).coprime_iff_not_dvd.mpr nope)
    exact ⟨q,hq,by by_contra no; exact hn ⟨q,hq,hd,no⟩⟩


def good (S : Finset ℕ) (k n : ℕ) : Prop :=
  ∃ V : Finset ℕ, V ⊆ S ∧ k ≤ V.card ∧ ∀ q ∈ V, simple q n

lemma many (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ Bound {n | ¬ good S k n} e := by
  classical
  induction k generalizing e with
  | zero =>
    refine ⟨∅,by simp,bound_empty.mono (fun n hn => ?_) he.le⟩
    exact False.elim (hn ⟨∅,by simp,by simp,by simp⟩)
  | succ k ih =>
    obtain ⟨S,pr,hS⟩ := ih (show 0 < e/2 by positivity)
    obtain ⟨T,dis,prT,hT⟩ := block S (show 0 < e/2 by positivity)
    refine ⟨S ∪ T,fun q hq => (mem_union.mp hq).elim (pr q) (prT q), (hS.union hT).mono ?_ (by linarith)⟩
    intro n hn
    by_cases h : good S k n
    · right
      rintro ⟨p,hp,hs⟩
      obtain ⟨V,hV,hk,hvs⟩ := h
      have hpV : p ∉ V := fun hh => (Finset.disjoint_left.mp dis hp) (hV hh)
      apply hn
      refine ⟨insert p V, ?_, ?_, ?_⟩
      · intro q hq
        rcases mem_insert.mp hq with rfl | hh
        · exact mem_union_right _ hp
        · exact mem_union_left _ (hV hh)
      · rw [card_insert_of_notMem hpV]
        omega
      · intro q hq
        exact (mem_insert.mp hq).elim (fun eq => eq ▸ hs) (hvs q)
    · exact Or.inl h

lemma divides {n k : ℕ} {S : Finset ℕ} (hn : n ≠ 0) (pr : ∀ q ∈ S, q.Prime)
    (h : good S k n) : 2^k ∣ n.divisors.card := by
  classical
  obtain ⟨V,hV,hk,hs⟩ := h
  have hpr (q) (hq : q ∈ V) := pr q (hV hq)
  have one (q) (hq : q ∈ V) : n.factorization q = 1 := by
    obtain ⟨hd,hn2⟩ := hs q hq
    have hp := hpr q hq
    have lo : 1 ≤ n.factorization q := hp.pow_dvd_iff_le_factorization hn |>.mp (by simpa using hd)
    have hi : ¬ 2 ≤ n.factorization q := fun h => hn2 ((hp.pow_dvd_iff_le_factorization hn).mpr h)
    omega
  rw [Nat.card_divisors hn]
  apply (Nat.pow_dvd_pow 2 hk).trans
  have sub : V ⊆ n.primeFactors := fun q hq => Nat.mem_primeFactors.mpr ⟨hpr q hq,(hs q hq).1,hn⟩
  have eq : (∏ q ∈ V, (n.factorization q + 1)) = 2^V.card := by simp [prod_congr rfl (fun q hq => congrArg (·+1) (one q hq))]
  exact eq ▸ prod_dvd_prod_of_subset V n.primeFactors (fun q => n.factorization q + 1) sub

lemma arbitrarily_small {e : ℝ} (he : 0 < e) : Bound {n | n.IsRefactorable} e := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (2/e)
  obtain ⟨S,pr,ex⟩ := many k (show 0 < e/2 by positivity)
  have hm : 0 < 2^k := by positivity
  have hl : 2/e < (2^k : ℕ) := hk.trans (by exact_mod_cast (Nat.lt_two_pow_self : k < 2^k))
  have small : 1/((2^k:ℕ):ℝ) ≤ e/2 := by
    rw [div_le_iff₀ (by exact_mod_cast hm : (0:ℝ) < (2^k:ℕ))]
    have h := (div_lt_iff₀ he).mp hl
    linarith
  apply (ex.union (bound_mult hm)).mono _ (by linarith)
  intro n hn
  by_cases h : good S k n
  · exact Or.inr ((divides (by have := hn.1; omega) pr h).trans hn.2)
  · exact Or.inl h

lemma density (A : Set ℕ) (h : ∀ e > (0:ℝ), Bound A e) : A.HasDensity 0 := by
  classical
  have pd (n : ℕ) : A.partialDensity Set.univ n = (count A n : ℝ)/n := by
    have eq : A ∩ Set.Iio n = (part A n : Set ℕ) := by
      ext k
      simp [mem_part, and_comm]
    simp [Set.partialDensity,eq,count]
  rw [Set.HasDensity,Metric.tendsto_nhds]
  intro e he
  obtain ⟨C,hC⟩ := h (e/2) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (max 0 (2*C/e))
  filter_upwards [eventually_ge_atTop K] with n hn
  have hN : (K:ℝ) ≤ n := by exact_mod_cast hn
  have pn : 0 < (n:ℝ) := lt_of_lt_of_le ((le_max_left _ _).trans_lt hK) hN
  have cut := (div_lt_iff₀ he).mp (lt_of_lt_of_le ((le_max_right _ _).trans_lt hK) hN)
  rw [pd,Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ pn]
  linarith [hC n]

end
end OMA.KennedyCooper

theorem OMA.solution : type_of% @RefactorableNumber.refactorable_hasDensity_zero :=
  OMA.KennedyCooper.density _ fun _ he => OMA.KennedyCooper.arbitrarily_small he
