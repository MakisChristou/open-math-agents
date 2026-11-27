import FormalConjectures.Wikipedia.SierpinskiEgyptianFractionConjecture
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Squarefree

/-! A prime divisor p congruent to −1 modulo five gives a two-term
expansion of 5/p. Scale it to the desired denominator and split one term.
The exceptional integers therefore avoid this entire prime progression.
The simple pole of the von Mangoldt series gives divergence of the
ordinary prime reciprocal sum by dominated convergence. -/

namespace OMA.EgyptianDensity
open Finset Filter ArithmeticFunction ArithmeticFunction.vonMangoldt Real
open scoped Topology
noncomputable section

def primeWeight {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n:ZMod q) = a then 1/(n:ℝ) else 0

lemma reciprocal_progression {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (primeWeight a) := by
  intro hs
  let f (t : ℝ) (n : ℕ) := t * (residueClass a n / (n:ℝ)^(1+t))
  let g (n : ℕ) := primeWeight a n + (if n.Prime then 0 else residueClass a n)/(n:ℝ)
  have hg : Summable g := hs.add (summable_residueClass_non_primes_div a)
  have hb {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (n : ℕ) : ‖f t n‖ ≤ g n := by
    by_cases hn : n = 0
    · subst n; simp [f,g,primeWeight]
    have pn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have on : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have rp : (n:ℝ)^(1+t) = n * (n:ℝ)^t := by rw [rpow_add pn,rpow_one]
    have pp : (0:ℝ) < (n:ℝ)^t := rpow_pos_of_pos pn _
    have htpow : 1 ≤ (n:ℝ)^t := one_le_rpow on ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ f t n by exact mul_nonneg ht.le (div_nonneg (residueClass_nonneg _ _) (rpow_nonneg pn.le _)))]
    dsimp [f,g]
    rw [rp]
    by_cases hpr : n.Prime
    · simp only [hpr,if_true,zero_div,add_zero,primeWeight,true_and]
      by_cases hna : (n:ZMod q) = a
      · rw [if_pos hna, show residueClass a n = Real.log n by simp [residueClass,hna,vonMangoldt_apply_prime hpr]]
        have ex : t*log (n:ℝ) ≤ (n:ℝ)^t := by
          rw [Real.rpow_def_of_pos pn]
          linarith [Real.add_one_le_exp (log (n:ℝ)*t)]
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right ex pn.le]
      · simp [residueClass,hna]
    · simp only [primeWeight,hpr,false_and,if_false,zero_add]
      have non := residueClass_nonneg a n
      have htq := ht'.trans htpow
      apply (le_div_iff₀ pn).mpr
      calc
        _ = (t * residueClass a n) / (n:ℝ)^t := by field_simp
        _ ≤ _ := (div_le_iff₀ pp).mpr (by simpa [mul_comm] using mul_le_mul_of_nonneg_right htq non)
  have lim (n : ℕ) : Tendsto (fun t : ℝ => f t n) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    by_cases hn : n = 0
    · subst n; simp [f]
    have pn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have c : ContinuousAt (fun t : ℝ => t * (residueClass a n / (n:ℝ)^(1+t))) 0 := by
      fun_prop (disch := positivity)
    simpa [f] using (c.continuousWithinAt (s:=Set.Ioi 0)).tendsto
  have event : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioc (0:ℝ) 1 :=
    Ioc_mem_nhdsGT (by norm_num)
  have conv := tendsto_tsum_of_dominated_convergence (f:=f) (g:=fun _ => (0:ℝ))
    hg lim (event.mono (fun t ht n => hb ht.1 ht.2 n))
  simp only [tsum_zero] at conv
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound ha
  have lower : ∀ᶠ t : ℝ in 𝓝[>] 0, (q.totient:ℝ)⁻¹-t*C ≤ ∑' n, f t n := by
    filter_upwards [event] with t ht
    have h := hC (x:=1+t) (show 1+t ∈ Set.Ioc 1 2 by constructor <;> linarith [ht.1,ht.2])
    rw [Set.mem_Ioc] at ht
    have hh := mul_le_mul_of_nonneg_left h ht.1.le
    rw [show 1+t-1=t by ring] at hh
    simpa [f,tsum_mul_left,mul_sub,ht.1.ne',mul_comm t ((q.totient:ℝ)⁻¹ / t)] using hh
  have limit : Tendsto (fun t : ℝ => (q.totient:ℝ)⁻¹-t*C) (𝓝[>] 0) (𝓝 (q.totient:ℝ)⁻¹) := by
    have h : ContinuousAt (fun t : ℝ => (q.totient:ℝ)⁻¹-t*C) 0 := by fun_prop
    simpa using (h.continuousWithinAt (s:=Set.Ioi 0)).tendsto
  have absurd := le_of_tendsto_of_tendsto limit conv lower
  have qp : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  exact (by positivity : 0 < (q.totient:ℝ)⁻¹).not_ge absurd

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


lemma mass (K : ℝ) : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p:ZMod 5) = -1) ∧
    K < ∑ p ∈ S, 1/(p:ℝ) := by
  classical
  have div := reciprocal_progression (q:=5) (a:=-1) (by simp)
  have ub : ∃ U : Finset ℕ, K < ∑ p ∈ U, primeWeight (-1:ZMod 5) p := by
    by_contra! h
    exact div (summable_of_sum_le (fun n => by unfold primeWeight; split <;> positivity) h)
  obtain ⟨U,hU⟩ := ub
  refine ⟨U.filter (fun p => p.Prime ∧ (p:ZMod 5) = -1),fun _ h => (mem_filter.mp h).2,?_⟩
  simpa [sum_filter,primeWeight] using hU

lemma egyptian {p n : ℕ} (hp : p.Prime) (hc : (p:ZMod 5) = -1) (hn : n ≠ 0) (hd : p ∣ n) :
    SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition n := by
  have hz : ((p+1:ℕ):ZMod 5) = 0 := by push_cast; rw [hc]; ring
  obtain ⟨t,ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hz
  obtain ⟨v,rfl⟩ := hd
  have ht' : 0 < t := by omega
  have hv : 0 < v := by by_contra! H; simp [show v=0 by omega] at hn
  have htq : (p:ℚ)+1 = 5*t := by exact_mod_cast ht
  have hpr : (0:ℚ) < p := by exact_mod_cast hp.pos
  have hvq : (0:ℚ) < v := by exact_mod_cast hv
  have htq' : (0:ℚ) < t := by exact_mod_cast ht'
  refine ⟨v*t,2*v*t*p,2*v*t*p,Nat.mul_pos hv ht',Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hv) ht') hp.pos,Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hv) ht') hp.pos,?_⟩
  push_cast
  field_simp
  nlinarith [htq]

lemma bound_one : Bound ({0}:Set ℕ) 0 := by
  refine ⟨1,fun N => ?_⟩
  have h : part ({0}:Set ℕ) N ⊆ {0} := by
    intro k hk; simpa using (mem_part.mp hk).2
  have hc : count ({0}:Set ℕ) N ≤ 1 := by simpa [count] using card_le_card h
  simpa using (show (count ({0}:Set ℕ) N:ℝ) ≤ 1 by exact_mod_cast hc)

lemma exceptionalBound {e : ℝ} (he : 0 < e) :
    Bound {n | ¬ SierpinskiEgyptianFractionConjecture.HasSierpinskiDecomposition n} e := by
  classical
  obtain ⟨S,hS,big⟩ := mass (1/e)
  let m := ∏ p ∈ S, p
  have hm : 0 < m := prod_pos fun q hq => (hS q hq).1.pos
  have hr := ratio_bound S (fun q hq => (hS q hq).1)
  change (m.totient:ℝ)/m * _ ≤ 1 at hr
  have rate : 0 + (m.totient:ℝ)/m ≤ e := by
    have hl : 1/e ≤ 1+∑ q ∈ S, 1/(q:ℝ) := by linarith
    have h := (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (m.totient:ℝ)/m)).trans hr
    rw [mul_one_div] at h
    have hb := (div_le_iff₀ he).mp h
    linarith
  apply (bound_one.union (bound_coprime hm)).mono _ rate
  intro n hn
  by_cases h : n = 0
  · exact Or.inl h
  · right
    exact Nat.coprime_prod_left_iff.mpr fun q hq => (hS q hq).1.coprime_iff_not_dvd.mpr
      (fun hd => hn (egyptian (hS q hq).1 (hS q hq).2 h hd))

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
end OMA.EgyptianDensity

theorem OMA.solution : type_of% @SierpinskiEgyptianFractionConjecture.sierpinski_counterexamples_hasDensity_zero :=
  OMA.EgyptianDensity.density _ fun _ he => OMA.EgyptianDensity.exceptionalBound he
