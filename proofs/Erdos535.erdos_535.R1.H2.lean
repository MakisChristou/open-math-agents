import OMAReductions.R_Erdos535_erdos_535_R1

/-! Separate the factors smaller than the cutoff, then select a largest fiber
of their exponent vector and the number of remaining prime factors. -/

open Finset Erdos535

private theorem pow_card_bound (t : Multiset ℕ) (m : ℕ) (h : ∀ a ∈ t, m ≤ a) :
    m ^ t.card ≤ t.prod := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, Nat.mul_comm]
    exact Nat.mul_le_mul (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem prime_prod_omega (t : Multiset ℕ) (h : ∀ a ∈ t, Nat.Prime a) :
    0 < t.prod ∧ ArithmeticFunction.cardFactors t.prod = t.card := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha := h a (by simp)
    obtain ⟨hp, hc⟩ := ih (fun b hb => h b (by simp [hb]))
    rw [Multiset.prod_cons, Multiset.card_cons, ArithmeticFunction.cardFactors_mul ha.ne_zero hp.ne',
      ArithmeticFunction.cardFactors_apply_prime ha, hc]
    exact ⟨Nat.mul_pos ha.pos hp, Nat.add_comm ..⟩

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  classical
  intro N y L K hy hL hK A hA
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, ∅, by decide, Nat.zero_le _, by simp [AllBigOmega], by simp, by simp⟩
  let P (a : A) : Multiset ℕ := a.val.primeFactorsList
  let small (a : A) := (P a).filter (· < y)
  let big (a : A) := (P a).filter (fun p => ¬ p < y)
  have prime (a : A) (p : ℕ) (hp : p ∈ P a) : Nat.Prime p := Nat.prime_of_mem_primeFactorsList hp
  have prod (a : A) : (P a).prod = a.val :=
    Nat.prod_primeFactorsList (by have := (mem_Icc.mp (hA a.2)).1; omega)
  have split (a : A) : (small a).prod * (big a).prod = a.val :=
    (Multiset.prod_filter_mul_prod_filter_not (s := P a) (· < y)).trans (prod a)
  have spos (a : A) : 0 < (small a).prod :=
    (prime_prod_omega _ (fun p h => prime a p (Multiset.mem_filter.mp h).1)).1
  have binfo (a : A) : 0 < (big a).prod ∧ ArithmeticFunction.cardFactors (big a).prod = (big a).card :=
    prime_prod_omega _ (fun p h => prime a p (Multiset.mem_filter.mp h).1)
  have sBound (a : A) : (small a).card ≤ L := by
    have hp := pow_card_bound (P a) 2 (fun p h => (prime a p h).two_le)
    rw [prod] at hp
    have hlt := lt_of_le_of_lt (hp.trans (mem_Icc.mp (hA a.2)).2) hL
    have hc := Multiset.card_le_card (Multiset.filter_le (· < y) (P a))
    exact hc.trans (le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt))
  have bBound (a : A) : (big a).card ≤ K := by
    have hp := pow_card_bound (big a) y (fun p h => le_of_not_gt (Multiset.mem_filter.mp h).2)
    have hle : (big a).prod ≤ a.val := by
      rw [← split a]
      simpa using Nat.mul_le_mul_right (big a).prod (spos a)
    have hlt := lt_of_le_of_lt ((hp.trans hle).trans (mem_Icc.mp (hA a.2)).2) hK
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right (by omega : 1 < y)).mp hlt)
  let Key := (Fin y → Fin (L+1)) × Fin (K+1)
  let key (a : A) : Key :=
    ⟨fun i => ⟨(small a).count i.val, Nat.lt_succ_of_le ((Multiset.count_le_card ..).trans (sBound a))⟩,
      ⟨(big a).card, Nat.lt_succ_of_le (bBound a)⟩⟩
  let fiber (v : Key) := univ.filter (fun a : A => key a = v)
  obtain ⟨v, hv, hmax⟩ := univ.exists_max_image (fun v : Key => (fiber v).card) univ_nonempty
  have hc : A.card ≤ (L+1)^y * (K+1) * (fiber v).card := calc
    A.card = ∑ w : Key, (fiber w).card := by
      simpa [fiber] using (card_eq_sum_card_fiberwise (s := (univ : Finset A))
        (t := (univ : Finset Key)) (f := key) (by simp))
    _ ≤ ∑ _w : Key, (fiber v).card := sum_le_sum hmax
    _ = _ := by simp [Key]
  have hf : (fiber v).Nonempty := by
    by_contra! he
    rw [he, card_empty, Nat.mul_zero] at hc
    exact Nat.not_lt_of_ge hc (Finset.card_pos.mpr hne)
  obtain ⟨a₀, ha₀⟩ := hf
  have same (a : A) (ha : a ∈ fiber v) : small a = small a₀ := by
    have eq := (mem_filter.mp ha).2.trans (mem_filter.mp ha₀).2.symm
    apply Multiset.ext.mpr
    intro p
    by_cases hp : p < y
    · exact congrArg Fin.val (congrFun (congrArg Prod.fst eq) ⟨p,hp⟩)
    · simp only [small, Multiset.count_filter, if_neg hp]
  let B := (fiber v).image (fun a => (big a).prod)
  have inj : Set.InjOn (fun a : A => (big a).prod) (↑(fiber v) : Set A) := by
    intro a ha b hb eq
    change (big a).prod = (big b).prod at eq
    apply Subtype.ext
    rw [← split a, ← split b, same a ha, same b hb, eq]
  refine ⟨(small a₀).prod, v.2.val, B, spos a₀, Nat.le_of_lt_succ v.2.isLt, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    exact ⟨(binfo a).1, (binfo a).2.trans (congrArg (fun w : Key => w.2.val) (mem_filter.mp ha).2)⟩
  · simpa [B, card_image_of_injOn inj] using hc
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    rw [← same a ha, split]
    exact a.2
