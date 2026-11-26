import FormalConjectures.ErdosProblems.«141»
import Mathlib.NumberTheory.LucasPrimality

/-! The progression of Dubner, Forbes, Lygeros, Mizony, Nelson and Zimmermann
was found by Manfred Toplic. It has ten consecutive primes with common difference 210 (Math. Comp. 71, 2002).
We certify the ten primalities by Lucas's criterion and the intervening
composites by divisors or modular exponentiation. -/

namespace OMA.ConsecutivePrimes

-- Binary modular exponentiation with a bound on the number of bits.
def modExp (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _ => acc % m
  | bits + 1, acc, b, e =>
    if e = 0 then acc % m else
      modExp m bits (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2)

lemma cast_modExp (m bits acc b e : ℕ) (h : e < 2 ^ bits) :
    (modExp m bits acc b e : ZMod m) = (acc : ZMod m) * (b : ZMod m) ^ e := by
  induction bits generalizing acc b e with
  | zero =>
    simp only [pow_zero] at h
    have : e = 0 := by omega
    simp [this, modExp, ZMod.natCast_mod]
  | succ bits ih =>
    have h' : e / 2 < 2 ^ bits := by rw [pow_succ] at h; omega
    by_cases hz : e = 0
    · simp [hz, modExp, ZMod.natCast_mod]
    rw [modExp, if_neg hz, ih _ _ _ h']
    simp only [ZMod.natCast_mod, Nat.cast_mul]
    have hpow : (b : ZMod m) ^ e =
        ((b : ZMod m) * b) ^ (e / 2) * (b : ZMod m) ^ (e % 2) := by
      rw [← pow_two, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [hpow]
    split_ifs with hodd
    · simp [hodd, ZMod.natCast_mod, mul_assoc, mul_comm]
    · have heven : e % 2 = 0 := by omega
      simp [heven]

def product (factors : List (ℕ × ℕ)) := (factors.map (fun t => t.1 ^ t.2)).prod

lemma mem_factors {q : ℕ} (hq : q.Prime) {L : List (ℕ × ℕ)}
    (hprimes : ∀ t ∈ L, Nat.Prime t.1) (hdiv : q ∣ product L) : ∃ t ∈ L, q = t.1 := by
  induction L with
  | nil => exact (hq.not_dvd_one hdiv).elim
  | cons t L ih =>
    change q ∣ t.1 ^ t.2 * product L at hdiv
    rcases hq.dvd_mul.mp hdiv with ht | hL
    · exact ⟨t, List.mem_cons_self, (Nat.prime_dvd_prime_iff_eq hq (hprimes t List.mem_cons_self)).mp (hq.dvd_of_dvd_pow ht)⟩
    · obtain ⟨u, hu, rfl⟩ := ih (fun u hu => hprimes u (List.mem_cons_of_mem _ hu)) hL
      exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩

lemma certify (p a : ℕ) (L : List (ℕ × ℕ)) (hsize : p - 1 < 2 ^ 320)
    (hprod : product L = p - 1) (hprimes : ∀ t ∈ L, Nat.Prime t.1)
    (hfull : (modExp p 320 1 a (p-1) : ZMod p) = 1)
    (htests : L.all (fun t => decide ((modExp p 320 1 a ((p-1)/t.1) : ZMod p) ≠ 1)) = true) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · simpa only [cast_modExp _ _ _ _ _ hsize, Nat.cast_one, one_mul] using hfull
  · intro q hq hdiv
    obtain ⟨t, ht, rfl⟩ := mem_factors hq hprimes (hprod ▸ hdiv)
    have hsmall : (p-1) / t.1 < 2 ^ 320 := (Nat.div_le_self _ _).trans_lt hsize
    simpa only [decide_eq_true_eq, cast_modExp _ _ _ _ _ hsmall, Nat.cast_one, one_mul]
      using List.all_eq_true.mp htests t ht

-- A composite witness is a proper divisor or, when d is zero, a failed
-- Fermat congruence to base two.
def checkComposite (n d : ℕ) : Bool :=
  if d = 0 then decide (n < 2 ^ 320 ∧ (modExp n 320 1 2 n : ZMod n) ≠ 2)
  else decide (1 < d ∧ d < n ∧ n % d = 0)

lemma not_prime_of_check (n d : ℕ) (h : checkComposite n d = true) : ¬ n.Prime := by
  intro hp
  unfold checkComposite at h
  split at h
  · obtain ⟨hsize, hne⟩ := of_decide_eq_true h
    have : Fact n.Prime := ⟨hp⟩
    apply hne
    rw [cast_modExp _ _ _ _ _ hsize]
    simp [ZMod.pow_card]
  · obtain ⟨hd, hdn, hz⟩ := of_decide_eq_true h
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hz) with h | h <;> omega

def checkGap (x : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => checkComposite x d && checkGap (x + 1) ds

lemma gap_sound {x : ℕ} {ds : List ℕ} (h : checkGap x ds = true)
    (j : ℕ) (hj : j < ds.length) : ¬ (x + j).Prime := by
  induction ds generalizing x j with
  | nil => simp at hj
  | cons d ds ih =>
    obtain ⟨hd, ht⟩ := Bool.and_eq_true_iff.mp h
    cases j with
    | zero => simpa using not_prime_of_check x d hd
    | succ j =>
      simpa only [Nat.add_succ, Nat.succ_add] using (ih ht j (by simpa using hj))

lemma count_gap (x y : ℕ) (hxy : x < y) (hx : x.Prime)
    (hn : ∀ z, x < z → z < y → ¬ z.Prime) : Nat.count Nat.Prime y = Nat.count Nat.Prime x + 1 := by
  have h1 := Nat.count_succ_eq_succ_count hx
  have h2 := Nat.count_monotone Nat.Prime (show x+1 ≤ y by omega)
  by_contra h
  obtain ⟨z, hz, hp⟩ := Nat.exists_of_count_lt_count (p := Nat.Prime)
    (show Nat.count Nat.Prime (x+1) < Nat.count Nat.Prime y by omega)
  exact hn _ hz.1 hz.2 hp

lemma progressions (start : ℕ) (primes : ∀ i < 10, Nat.Prime (start + i * 210))
    (gaps : ∀ i < 9, ∀ j < 209, ¬ Nat.Prime (start + i * 210 + 1 + j))
    (k : ℕ) (hk : k ≤ 10) : ∃ s : Set ℕ, Erdos141.Set.IsAPAndPrimeProgressionOfLength s k := by
  have counts (i : ℕ) (hi : i < 10) :
      Nat.count Nat.Prime (start + i * 210) = Nat.count Nat.Prime start + i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← Nat.add_assoc, ← ih (by omega)]
      apply count_gap _ _ (by omega) (primes i (by omega))
      intro z hx hy
      have := gaps i (by omega) (z - (start + i * 210 + 1)) (by omega)
      simpa only [show start + i * 210 + 1 + (z - (start + i * 210 + 1)) = z by omega] using this
  have nths (i : ℕ) (hi : i < 10) :
      Nat.nth Nat.Prime (Nat.count Nat.Prime start + i) = start + i * 210 := by
    rw [← counts i hi, Nat.nth_count (primes i hi)]
  let f (i : Fin k) := start + i.val * 210
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    dsimp [f] at hij
    omega
  have hc : ENat.card (Set.range f) = k := by
    calc
      ENat.card (Set.range f) = ENat.card (Fin k) := (ENat.card_congr (Equiv.ofInjective f hf)).symm
      _ = k := by simp
  refine ⟨Set.range f, ⟨start, 210, hc, ?_⟩, Nat.count Nat.Prime start, hc, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by simp [f]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by exact_mod_cast hi⟩, by simp [f]⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, nths i.val (lt_of_lt_of_le i.isLt hk)⟩
    · rintro ⟨i, hi, rfl⟩
      have hik : i < k := by exact_mod_cast hi
      exact ⟨⟨i, hik⟩, (nths i (lt_of_lt_of_le hik hk)).symm⟩

private theorem prime_1567 : Nat.Prime 1567 := by
  apply certify _ 3 [(2, 1), (3, 3), (29, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1597 : Nat.Prime 1597 := by
  apply certify _ 11 [(2, 2), (3, 1), (7, 1), (19, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1777 : Nat.Prime 1777 := by
  apply certify _ 5 [(2, 4), (3, 1), (37, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1787 : Nat.Prime 1787 := by
  apply certify _ 2 [(2, 1), (19, 1), (47, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1831 : Nat.Prime 1831 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (61, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1993 : Nat.Prime 1993 := by
  apply certify _ 5 [(2, 3), (3, 1), (83, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2017 : Nat.Prime 2017 := by
  apply certify _ 5 [(2, 5), (3, 2), (7, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2309 : Nat.Prime 2309 := by
  apply certify _ 2 [(2, 2), (577, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2347 : Nat.Prime 2347 := by
  apply certify _ 3 [(2, 1), (3, 1), (17, 1), (23, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2351 : Nat.Prime 2351 := by
  apply certify _ 13 [(2, 1), (5, 2), (47, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2521 : Nat.Prime 2521 := by
  apply certify _ 17 [(2, 3), (3, 2), (5, 1), (7, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2689 : Nat.Prime 2689 := by
  apply certify _ 19 [(2, 7), (3, 1), (7, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2729 : Nat.Prime 2729 := by
  apply certify _ 3 [(2, 3), (11, 1), (31, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2741 : Nat.Prime 2741 := by
  apply certify _ 2 [(2, 2), (5, 1), (137, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2879 : Nat.Prime 2879 := by
  apply certify _ 7 [(2, 1), (1439, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2971 : Nat.Prime 2971 := by
  apply certify _ 10 [(2, 1), (3, 3), (5, 1), (11, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_3061 : Nat.Prime 3061 := by
  apply certify _ 6 [(2, 2), (3, 2), (5, 1), (17, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_3331 : Nat.Prime 3331 := by
  apply certify _ 3 [(2, 1), (3, 2), (5, 1), (37, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_3533 : Nat.Prime 3533 := by
  apply certify _ 2 [(2, 2), (883, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_3541 : Nat.Prime 3541 := by
  apply certify _ 7 [(2, 2), (3, 1), (5, 1), (59, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_3637 : Nat.Prime 3637 := by
  apply certify _ 2 [(2, 2), (3, 2), (101, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_4483 : Nat.Prime 4483 := by
  apply certify _ 2 [(2, 1), (3, 3), (83, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_4597 : Nat.Prime 4597 := by
  apply certify _ 5 [(2, 2), (3, 1), (383, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_4703 : Nat.Prime 4703 := by
  apply certify _ 5 [(2, 1), (2351, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_2351
  · decide +kernel
  · decide +kernel

private theorem prime_4783 : Nat.Prime 4783 := by
  apply certify _ 6 [(2, 1), (3, 1), (797, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_4931 : Nat.Prime 4931 := by
  apply certify _ 6 [(2, 1), (5, 1), (17, 1), (29, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_4937 : Nat.Prime 4937 := by
  apply certify _ 3 [(2, 3), (617, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5023 : Nat.Prime 5023 := by
  apply certify _ 3 [(2, 1), (3, 4), (31, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5441 : Nat.Prime 5441 := by
  apply certify _ 3 [(2, 6), (5, 1), (17, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5557 : Nat.Prime 5557 := by
  apply certify _ 2 [(2, 2), (3, 1), (463, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5839 : Nat.Prime 5839 := by
  apply certify _ 6 [(2, 1), (3, 1), (7, 1), (139, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5849 : Nat.Prime 5849 := by
  apply certify _ 3 [(2, 3), (17, 1), (43, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_6037 : Nat.Prime 6037 := by
  apply certify _ 5 [(2, 2), (3, 1), (503, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_6131 : Nat.Prime 6131 := by
  apply certify _ 2 [(2, 1), (5, 1), (613, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_6397 : Nat.Prime 6397 := by
  apply certify _ 2 [(2, 2), (3, 1), (13, 1), (41, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_6917 : Nat.Prime 6917 := by
  apply certify _ 2 [(2, 2), (7, 1), (13, 1), (19, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_7027 : Nat.Prime 7027 := by
  apply certify _ 2 [(2, 1), (3, 1), (1171, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_7057 : Nat.Prime 7057 := by
  apply certify _ 5 [(2, 4), (3, 2), (7, 2)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_7243 : Nat.Prime 7243 := by
  apply certify _ 2 [(2, 1), (3, 1), (17, 1), (71, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_7919 : Nat.Prime 7919 := by
  apply certify _ 7 [(2, 1), (37, 1), (107, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_8537 : Nat.Prime 8537 := by
  apply certify _ 3 [(2, 3), (11, 1), (97, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_8951 : Nat.Prime 8951 := by
  apply certify _ 13 [(2, 1), (5, 2), (179, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9011 : Nat.Prime 9011 := by
  apply certify _ 2 [(2, 1), (5, 1), (17, 1), (53, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9239 : Nat.Prime 9239 := by
  apply certify _ 19 [(2, 1), (31, 1), (149, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9277 : Nat.Prime 9277 := by
  apply certify _ 5 [(2, 2), (3, 1), (773, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9689 : Nat.Prime 9689 := by
  apply certify _ 3 [(2, 3), (7, 1), (173, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9829 : Nat.Prime 9829 := by
  apply certify _ 10 [(2, 2), (3, 3), (7, 1), (13, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_9931 : Nat.Prime 9931 := by
  apply certify _ 10 [(2, 1), (3, 1), (5, 1), (331, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_10301 : Nat.Prime 10301 := by
  apply certify _ 2 [(2, 2), (5, 2), (103, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_10597 : Nat.Prime 10597 := by
  apply certify _ 5 [(2, 2), (3, 1), (883, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_10883 : Nat.Prime 10883 := by
  apply certify _ 2 [(2, 1), (5441, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_5441
  · decide +kernel
  · decide +kernel

private theorem prime_11657 : Nat.Prime 11657 := by
  apply certify _ 3 [(2, 3), (31, 1), (47, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_11927 : Nat.Prime 11927 := by
  apply certify _ 5 [(2, 1), (67, 1), (89, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_12263 : Nat.Prime 12263 := by
  apply certify _ 5 [(2, 1), (6131, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_6131
  · decide +kernel
  · decide +kernel

private theorem prime_12373 : Nat.Prime 12373 := by
  apply certify _ 2 [(2, 2), (3, 1), (1031, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_13309 : Nat.Prime 13309 := by
  apply certify _ 6 [(2, 2), (3, 1), (1109, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_13313 : Nat.Prime 13313 := by
  apply certify _ 3 [(2, 10), (13, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_15443 : Nat.Prime 15443 := by
  apply certify _ 2 [(2, 1), (7, 1), (1103, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_16069 : Nat.Prime 16069 := by
  apply certify _ 2 [(2, 2), (3, 1), (13, 1), (103, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_16421 : Nat.Prime 16421 := by
  apply certify _ 2 [(2, 2), (5, 1), (821, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_17203 : Nat.Prime 17203 := by
  apply certify _ 2 [(2, 1), (3, 1), (47, 1), (61, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_18047 : Nat.Prime 18047 := by
  apply certify _ 5 [(2, 1), (7, 1), (1289, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_23671 : Nat.Prime 23671 := by
  apply certify _ 3 [(2, 1), (3, 2), (5, 1), (263, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_23767 : Nat.Prime 23767 := by
  apply certify _ 3 [(2, 1), (3, 1), (17, 1), (233, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_23971 : Nat.Prime 23971 := by
  apply certify _ 10 [(2, 1), (3, 1), (5, 1), (17, 1), (47, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_24509 : Nat.Prime 24509 := by
  apply certify _ 2 [(2, 2), (11, 1), (557, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_26417 : Nat.Prime 26417 := by
  apply certify _ 3 [(2, 4), (13, 1), (127, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_28591 : Nat.Prime 28591 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (953, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_28837 : Nat.Prime 28837 := by
  apply certify _ 2 [(2, 2), (3, 4), (89, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_30071 : Nat.Prime 30071 := by
  apply certify _ 13 [(2, 1), (5, 1), (31, 1), (97, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_32843 : Nat.Prime 32843 := by
  apply certify _ 2 [(2, 1), (16421, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_16421
  · decide +kernel
  · decide +kernel

private theorem prime_34127 : Nat.Prime 34127 := by
  apply certify _ 5 [(2, 1), (113, 1), (151, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_37003 : Nat.Prime 37003 := by
  apply certify _ 2 [(2, 1), (3, 1), (7, 1), (881, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_37337 : Nat.Prime 37337 := by
  apply certify _ 3 [(2, 3), (13, 1), (359, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_37489 : Nat.Prime 37489 := by
  apply certify _ 19 [(2, 4), (3, 1), (11, 1), (71, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_40627 : Nat.Prime 40627 := by
  apply certify _ 2 [(2, 1), (3, 2), (37, 1), (61, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_41681 : Nat.Prime 41681 := by
  apply certify _ 3 [(2, 4), (5, 1), (521, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_47809 : Nat.Prime 47809 := by
  apply certify _ 7 [(2, 6), (3, 2), (83, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_49019 : Nat.Prime 49019 := by
  apply certify _ 2 [(2, 1), (24509, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_24509
  · decide +kernel
  · decide +kernel

private theorem prime_55697 : Nat.Prime 55697 := by
  apply certify _ 3 [(2, 4), (59, 2)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_58193 : Nat.Prime 58193 := by
  apply certify _ 3 [(2, 4), (3637, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_3637
  · decide +kernel
  · decide +kernel

private theorem prime_59791 : Nat.Prime 59791 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (1993, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1993
  · decide +kernel
  · decide +kernel

private theorem prime_63617 : Nat.Prime 63617 := by
  apply certify _ 3 [(2, 7), (7, 1), (71, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_64853 : Nat.Prime 64853 := by
  apply certify _ 2 [(2, 2), (31, 1), (523, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_66109 : Nat.Prime 66109 := by
  apply certify _ 2 [(2, 2), (3, 1), (7, 1), (787, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_73553 : Nat.Prime 73553 := by
  apply certify _ 3 [(2, 4), (4597, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_4597
  · decide +kernel
  · decide +kernel

private theorem prime_74761 : Nat.Prime 74761 := by
  apply certify _ 19 [(2, 3), (3, 1), (5, 1), (7, 1), (89, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_77513 : Nat.Prime 77513 := by
  apply certify _ 3 [(2, 3), (9689, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_9689
  · decide +kernel
  · decide +kernel

private theorem prime_82217 : Nat.Prime 82217 := by
  apply certify _ 3 [(2, 3), (43, 1), (239, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_84827 : Nat.Prime 84827 := by
  apply certify _ 2 [(2, 1), (7, 1), (73, 1), (83, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_90073 : Nat.Prime 90073 := by
  apply certify _ 10 [(2, 3), (3, 4), (139, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_92269 : Nat.Prime 92269 := by
  apply certify _ 10 [(2, 2), (3, 2), (11, 1), (233, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_93257 : Nat.Prime 93257 := by
  apply certify _ 3 [(2, 3), (11657, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_11657
  · decide +kernel
  · decide +kernel

private theorem prime_111341 : Nat.Prime 111341 := by
  apply certify _ 3 [(2, 2), (5, 1), (19, 1), (293, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_114649 : Nat.Prime 114649 := by
  apply certify _ 7 [(2, 3), (3, 1), (17, 1), (281, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_116959 : Nat.Prime 116959 := by
  apply certify _ 3 [(2, 1), (3, 1), (101, 1), (193, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_123731 : Nat.Prime 123731 := by
  apply certify _ 2 [(2, 1), (5, 1), (12373, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_12373
  · decide +kernel
  · decide +kernel

private theorem prime_129707 : Nat.Prime 129707 := by
  apply certify _ 2 [(2, 1), (64853, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_64853
  · decide +kernel
  · decide +kernel

private theorem prime_133241 : Nat.Prime 133241 := by
  apply certify _ 6 [(2, 3), (5, 1), (3331, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_3331
  · decide +kernel
  · decide +kernel

private theorem prime_157351 : Nat.Prime 157351 := by
  apply certify _ 21 [(2, 1), (3, 1), (5, 2), (1049, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_161779 : Nat.Prime 161779 := by
  apply certify _ 2 [(2, 1), (3, 1), (59, 1), (457, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_169199 : Nat.Prime 169199 := by
  apply certify _ 7 [(2, 1), (31, 1), (2729, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2729
  · decide +kernel
  · decide +kernel

private theorem prime_169943 : Nat.Prime 169943 := by
  apply certify _ 5 [(2, 1), (31, 1), (2741, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2741
  · decide +kernel
  · decide +kernel

private theorem prime_185821 : Nat.Prime 185821 := by
  apply certify _ 10 [(2, 2), (3, 1), (5, 1), (19, 1), (163, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_217661 : Nat.Prime 217661 := by
  apply certify _ 3 [(2, 2), (5, 1), (10883, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_10883
  · decide +kernel
  · decide +kernel

private theorem prime_229939 : Nat.Prime 229939 := by
  apply certify _ 2 [(2, 1), (3, 1), (19, 1), (2017, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2017
  · decide +kernel
  · decide +kernel

private theorem prime_248827 : Nat.Prime 248827 := by
  apply certify _ 2 [(2, 1), (3, 1), (113, 1), (367, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_275491 : Nat.Prime 275491 := by
  apply certify _ 10 [(2, 1), (3, 2), (5, 1), (3061, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_3061
  · decide +kernel
  · decide +kernel

private theorem prime_312553 : Nat.Prime 312553 := by
  apply certify _ 7 [(2, 3), (3, 3), (1447, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_318691 : Nat.Prime 318691 := by
  apply certify _ 3 [(2, 1), (3, 2), (5, 1), (3541, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_3541
  · decide +kernel
  · decide +kernel

private theorem prime_337969 : Nat.Prime 337969 := by
  apply certify _ 13 [(2, 4), (3, 2), (2347, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2347
  · decide +kernel
  · decide +kernel

private theorem prime_339887 : Nat.Prime 339887 := by
  apply certify _ 5 [(2, 1), (169943, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_169943
  · decide +kernel
  · decide +kernel

private theorem prime_360293 : Nat.Prime 360293 := by
  apply certify _ 2 [(2, 2), (90073, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_90073
  · decide +kernel
  · decide +kernel

private theorem prime_403061 : Nat.Prime 403061 := by
  apply certify _ 3 [(2, 2), (5, 1), (7, 1), (2879, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2879
  · decide +kernel
  · decide +kernel

private theorem prime_440239 : Nat.Prime 440239 := by
  apply certify _ 3 [(2, 1), (3, 1), (239, 1), (307, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_471313 : Nat.Prime 471313 := by
  apply certify _ 5 [(2, 4), (3, 3), (1091, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_475141 : Nat.Prime 475141 := by
  apply certify _ 2 [(2, 2), (3, 1), (5, 1), (7919, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_7919
  · decide +kernel
  · decide +kernel

private theorem prime_492673 : Nat.Prime 492673 := by
  apply certify _ 5 [(2, 7), (3, 1), (1283, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_695171 : Nat.Prime 695171 := by
  apply certify _ 2 [(2, 1), (5, 1), (7, 1), (9931, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_9931
  · decide +kernel
  · decide +kernel

private theorem prime_720653 : Nat.Prime 720653 := by
  apply certify _ 2 [(2, 2), (67, 1), (2689, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2689
  · decide +kernel
  · decide +kernel

private theorem prime_771233 : Nat.Prime 771233 := by
  apply certify _ 3 [(2, 5), (7, 1), (11, 1), (313, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_930157 : Nat.Prime 930157 := by
  apply certify _ 2 [(2, 2), (3, 1), (77513, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_77513
  · decide +kernel
  · decide +kernel

private theorem prime_952111 : Nat.Prime 952111 := by
  apply certify _ 3 [(2, 1), (3, 2), (5, 1), (71, 1), (149, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_965357 : Nat.Prime 965357 := by
  apply certify _ 3 [(2, 2), (7, 1), (23, 1), (1499, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_1083707 : Nat.Prime 1083707 := by
  apply certify _ 2 [(2, 1), (13, 1), (41681, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_41681
  · decide +kernel
  · decide +kernel

private theorem prime_1305599 : Nat.Prime 1305599 := by
  apply certify _ 11 [(2, 1), (7, 1), (93257, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_93257
  · decide +kernel
  · decide +kernel

private theorem prime_1652947 : Nat.Prime 1652947 := by
  apply certify _ 2 [(2, 1), (3, 1), (275491, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_275491
  · decide +kernel
  · decide +kernel

private theorem prime_1858211 : Nat.Prime 1858211 := by
  apply certify _ 10 [(2, 1), (5, 1), (185821, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_185821
  · decide +kernel
  · decide +kernel

private theorem prime_2018591 : Nat.Prime 2018591 := by
  apply certify _ 7 [(2, 1), (5, 1), (7, 1), (28837, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_28837
  · decide +kernel
  · decide +kernel

private theorem prime_2161759 : Nat.Prime 2161759 := by
  apply certify _ 3 [(2, 1), (3, 1), (360293, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_360293
  · decide +kernel
  · decide +kernel

private theorem prime_2380463 : Nat.Prime 2380463 := by
  apply certify _ 5 [(2, 1), (7, 1), (193, 1), (881, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2544811 : Nat.Prime 2544811 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (84827, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_84827
  · decide +kernel
  · decide +kernel

private theorem prime_2591189 : Nat.Prime 2591189 := by
  apply certify _ 2 [(2, 2), (659, 1), (983, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_2611199 : Nat.Prime 2611199 := by
  apply certify _ 13 [(2, 1), (1305599, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_1305599
  · decide +kernel
  · decide +kernel

private theorem prime_4037183 : Nat.Prime 4037183 := by
  apply certify _ 5 [(2, 1), (2018591, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_2018591
  · decide +kernel
  · decide +kernel

private theorem prime_4062701 : Nat.Prime 4062701 := by
  apply certify _ 2 [(2, 2), (5, 2), (40627, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_40627
  · decide +kernel
  · decide +kernel

private theorem prime_4676323 : Nat.Prime 4676323 := by
  apply certify _ 3 [(2, 1), (3, 1), (7, 1), (111341, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_111341
  · decide +kernel
  · decide +kernel

private theorem prime_4975823 : Nat.Prime 4975823 := by
  apply certify _ 5 [(2, 1), (67, 1), (71, 1), (523, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_5182379 : Nat.Prime 5182379 := by
  apply certify _ 2 [(2, 1), (2591189, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_2591189
  · decide +kernel
  · decide +kernel

private theorem prime_7152083 : Nat.Prime 7152083 := by
  apply certify _ 2 [(2, 1), (7, 1), (487, 1), (1049, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_15982339 : Nat.Prime 15982339 := by
  apply certify _ 2 [(2, 1), (3, 1), (1499, 1), (1777, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1777
  · decide +kernel
  · decide +kernel

private theorem prime_16467721 : Nat.Prime 16467721 := by
  apply certify _ 11 [(2, 3), (3, 1), (5, 1), (109, 1), (1259, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_18675439 : Nat.Prime 18675439 := by
  apply certify _ 3 [(2, 1), (3, 1), (881, 1), (3533, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_3533
  · decide +kernel
  · decide +kernel

private theorem prime_19189553 : Nat.Prime 19189553 := by
  apply certify _ 3 [(2, 4), (751, 1), (1597, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_1597
  · decide +kernel
  · decide +kernel

private theorem prime_21651121 : Nat.Prime 21651121 := by
  apply certify _ 13 [(2, 4), (3, 2), (5, 1), (30071, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_30071
  · decide +kernel
  · decide +kernel

private theorem prime_26360903 : Nat.Prime 26360903 := by
  apply certify _ 5 [(2, 1), (461, 1), (28591, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_28591
  · decide +kernel
  · decide +kernel

private theorem prime_30164033 : Nat.Prime 30164033 := by
  apply certify _ 3 [(2, 6), (471313, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_471313
  · decide +kernel
  · decide +kernel

private theorem prime_31569287 : Nat.Prime 31569287 := by
  apply certify _ 5 [(2, 1), (7, 1), (503, 1), (4483, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4483
  · decide +kernel
  · decide +kernel

private theorem prime_37937261 : Nat.Prime 37937261 := by
  apply certify _ 2 [(2, 2), (5, 1), (179, 1), (10597, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_10597
  · decide +kernel
  · decide +kernel

private theorem prime_43243117 : Nat.Prime 43243117 := by
  apply certify _ 2 [(2, 2), (3, 1), (7, 1), (587, 1), (877, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_46694521 : Nat.Prime 46694521 := by
  apply certify _ 14 [(2, 3), (3, 2), (5, 1), (129707, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_129707
  · decide +kernel
  · decide +kernel

private theorem prime_56784023 : Nat.Prime 56784023 := by
  apply certify _ 5 [(2, 1), (4703, 1), (6037, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · exact prime_4703
    · exact prime_6037
  · decide +kernel
  · decide +kernel

private theorem prime_60534853 : Nat.Prime 60534853 := by
  apply certify _ 2 [(2, 2), (3, 1), (7, 1), (720653, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_720653
  · decide +kernel
  · decide +kernel

private theorem prime_60703897 : Nat.Prime 60703897 := by
  apply certify _ 5 [(2, 3), (3, 1), (11, 1), (229939, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_229939
  · decide +kernel
  · decide +kernel

private theorem prime_79944847 : Nat.Prime 79944847 := by
  apply certify _ 5 [(2, 1), (3, 1), (17, 1), (31, 1), (131, 1), (193, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_97169879 : Nat.Prime 97169879 := by
  apply certify _ 7 [(2, 1), (13, 1), (101, 1), (37003, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_37003
  · decide +kernel
  · decide +kernel

private theorem prime_183577111 : Nat.Prime 183577111 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (499, 1), (12263, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_12263
  · decide +kernel
  · decide +kernel

private theorem prime_238771427 : Nat.Prime 238771427 := by
  apply certify _ 2 [(2, 1), (17, 1), (757, 1), (9277, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_9277
  · decide +kernel
  · decide +kernel

private theorem prime_247956283 : Nat.Prime 247956283 := by
  apply certify _ 2 [(2, 1), (3, 3), (7, 1), (71, 1), (9239, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_9239
  · decide +kernel
  · decide +kernel

private theorem prime_319779389 : Nat.Prime 319779389 := by
  apply certify _ 2 [(2, 2), (79944847, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_79944847
  · decide +kernel
  · decide +kernel

private theorem prime_329668739 : Nat.Prime 329668739 := by
  apply certify _ 2 [(2, 1), (7, 1), (79, 1), (347, 1), (859, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · decide +kernel

private theorem prime_335730821 : Nat.Prime 335730821 := by
  apply certify _ 2 [(2, 2), (5, 1), (1087, 1), (15443, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_15443
  · decide +kernel
  · decide +kernel

private theorem prime_357852113 : Nat.Prime 357852113 := by
  apply certify _ 5 [(2, 4), (29, 1), (771233, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_771233
  · decide +kernel
  · decide +kernel

private theorem prime_461096189 : Nat.Prime 461096189 := by
  apply certify _ 10 [(2, 2), (7, 1), (16467721, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_16467721
  · decide +kernel
  · decide +kernel

private theorem prime_1058408119 : Nat.Prime 1058408119 := by
  apply certify _ 3 [(2, 1), (3, 2), (173, 1), (339887, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_339887
  · decide +kernel
  · decide +kernel

private theorem prime_1081539587 : Nat.Prime 1081539587 := by
  apply certify _ 2 [(2, 1), (499, 1), (1083707, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_1083707
  · decide +kernel
  · decide +kernel

private theorem prime_1110031619 : Nat.Prime 1110031619 := by
  apply certify _ 2 [(2, 1), (47, 1), (103, 1), (114649, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_114649
  · decide +kernel
  · decide +kernel

private theorem prime_1625900707 : Nat.Prime 1625900707 := by
  apply certify _ 5 [(2, 1), (3, 2), (17, 2), (312553, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_312553
  · decide +kernel
  · decide +kernel

private theorem prime_2109160373 : Nat.Prime 2109160373 := by
  apply certify _ 2 [(2, 2), (11, 1), (29, 1), (1652947, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1652947
  · decide +kernel
  · decide +kernel

private theorem prime_2695073261 : Nat.Prime 2695073261 := by
  apply certify _ 3 [(2, 2), (5, 1), (11, 1), (149, 1), (82217, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_82217
  · decide +kernel
  · decide +kernel

private theorem prime_2854582189 : Nat.Prime 2854582189 := by
  apply certify _ 2 [(2, 2), (3, 1), (7243, 1), (32843, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_7243
    · exact prime_32843
  · decide +kernel
  · decide +kernel

private theorem prime_3262224011 : Nat.Prime 3262224011 := by
  apply certify _ 6 [(2, 1), (5, 1), (17, 1), (19189553, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_19189553
  · decide +kernel
  · decide +kernel

private theorem prime_3308813021 : Nat.Prime 3308813021 := by
  apply certify _ 3 [(2, 2), (5, 1), (17, 2), (43, 1), (13313, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_13313
  · decide +kernel
  · decide +kernel

private theorem prime_5390146523 : Nat.Prime 5390146523 := by
  apply certify _ 2 [(2, 1), (2695073261, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · norm_num
    · exact prime_2695073261
  · decide +kernel
  · decide +kernel

private theorem prime_6823638763 : Nat.Prime 6823638763 := by
  apply certify _ 2 [(2, 1), (3, 1), (17203, 1), (66109, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_17203
    · exact prime_66109
  · decide +kernel
  · decide +kernel

private theorem prime_9135179189 : Nat.Prime 9135179189 := by
  apply certify _ 2 [(2, 2), (307, 1), (313, 1), (23767, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_23767
  · decide +kernel
  · decide +kernel

private theorem prime_11197579487 : Nat.Prime 11197579487 := by
  apply certify _ 5 [(2, 1), (23, 1), (131, 1), (1858211, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1858211
  · decide +kernel
  · decide +kernel

private theorem prime_12231997963 : Nat.Prime 12231997963 := by
  apply certify _ 2 [(2, 1), (3, 1), (6397, 1), (318691, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_6397
    · exact prime_318691
  · decide +kernel
  · decide +kernel

private theorem prime_12882676069 : Nat.Prime 12882676069 := by
  apply certify _ 2 [(2, 2), (3, 2), (357852113, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_357852113
  · decide +kernel
  · decide +kernel

private theorem prime_16174127069 : Nat.Prime 16174127069 := by
  apply certify _ 2 [(2, 2), (11, 1), (23, 1), (15982339, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_15982339
  · decide +kernel
  · decide +kernel

private theorem prime_22829695829 : Nat.Prime 22829695829 := by
  apply certify _ 2 [(2, 2), (17, 1), (335730821, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_335730821
  · decide +kernel
  · decide +kernel

private theorem prime_27565782029 : Nat.Prime 27565782029 := by
  apply certify _ 2 [(2, 2), (55697, 1), (123731, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · exact prime_55697
    · exact prime_123731
  · decide +kernel
  · decide +kernel

private theorem prime_37907731723 : Nat.Prime 37907731723 := by
  apply certify _ 2 [(2, 1), (3, 1), (7, 2), (797, 1), (161779, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_161779
  · decide +kernel
  · decide +kernel

private theorem prime_47053325621 : Nat.Prime 47053325621 := by
  apply certify _ 2 [(2, 2), (5, 1), (7, 1), (353, 1), (952111, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_952111
  · decide +kernel
  · decide +kernel

private theorem prime_102678983629 : Nat.Prime 102678983629 := by
  apply certify _ 6 [(2, 2), (3, 1), (13, 1), (23, 1), (71, 1), (403061, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_403061
  · decide +kernel
  · decide +kernel

private theorem prime_146783975557 : Nat.Prime 146783975557 := by
  apply certify _ 2 [(2, 2), (3, 1), (12231997963, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_12231997963
  · decide +kernel
  · decide +kernel

private theorem prime_164433225403 : Nat.Prime 164433225403 := by
  apply certify _ 3 [(2, 1), (3, 2), (9135179189, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_9135179189
  · decide +kernel
  · decide +kernel

private theorem prime_198528781261 : Nat.Prime 198528781261 := by
  apply certify _ 7 [(2, 2), (3, 1), (5, 1), (3308813021, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_3308813021
  · decide +kernel
  · decide +kernel

private theorem prime_218447926987 : Nat.Prime 218447926987 := by
  apply certify _ 2 [(2, 1), (3, 1), (17, 1), (71, 1), (30164033, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_30164033
  · decide +kernel
  · decide +kernel

private theorem prime_248692063469 : Nat.Prime 248692063469 := by
  apply certify _ 2 [(2, 2), (19, 1), (31, 1), (5849, 1), (18047, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_5849
    · exact prime_18047
  · decide +kernel
  · decide +kernel

private theorem prime_327757380757 : Nat.Prime 327757380757 := by
  apply certify _ 14 [(2, 2), (3, 1), (13, 1), (37, 1), (56784023, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_56784023
  · decide +kernel
  · decide +kernel

private theorem prime_528124563007 : Nat.Prime 528124563007 := by
  apply certify _ 5 [(2, 1), (3, 1), (23, 1), (31, 1), (37, 1), (89, 1), (37489, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_37489
  · decide +kernel
  · decide +kernel

private theorem prime_582536588861 : Nat.Prime 582536588861 := by
  apply certify _ 2 [(2, 2), (5, 1), (617, 1), (1787, 1), (26417, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1787
    · exact prime_26417
  · decide +kernel
  · decide +kernel

private theorem prime_804992177299 : Nat.Prime 804992177299 := by
  apply certify _ 2 [(2, 1), (3, 1), (47, 1), (2854582189, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2854582189
  · decide +kernel
  · decide +kernel

private theorem prime_2653541220611 : Nat.Prime 2653541220611 := by
  apply certify _ 2 [(2, 1), (5, 1), (7, 1), (37907731723, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_37907731723
  · decide +kernel
  · decide +kernel

private theorem prime_3339337037807 : Nat.Prime 3339337037807 := by
  apply certify _ 5 [(2, 1), (7, 1), (11, 1), (131, 1), (10301, 1), (16069, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_10301
    · exact prime_16069
  · decide +kernel
  · decide +kernel

private theorem prime_3495219533167 : Nat.Prime 3495219533167 := by
  apply certify _ 5 [(2, 1), (3, 1), (582536588861, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_582536588861
  · decide +kernel
  · decide +kernel

private theorem prime_5357493895483 : Nat.Prime 5357493895483 := by
  apply certify _ 3 [(2, 1), (3, 2), (116959, 1), (2544811, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_116959
    · exact prime_2544811
  · decide +kernel
  · decide +kernel

private theorem prime_9052516320917 : Nat.Prime 9052516320917 := by
  apply certify _ 2 [(2, 2), (29, 1), (37, 1), (2109160373, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2109160373
  · decide +kernel
  · decide +kernel

private theorem prime_14134419850597 : Nat.Prime 14134419850597 := by
  apply certify _ 2 [(2, 2), (3, 1), (101, 1), (23671, 1), (492673, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_23671
    · exact prime_492673
  · decide +kernel
  · decide +kernel

private theorem prime_15427219380457 : Nat.Prime 15427219380457 := by
  apply certify _ 7 [(2, 3), (3, 1), (13, 1), (17, 1), (53, 1), (59, 1), (930157, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_930157
  · decide +kernel
  · decide +kernel

private theorem prime_69955944598277 : Nat.Prime 69955944598277 := by
  apply certify _ 2 [(2, 2), (11, 1), (233, 1), (6823638763, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_6823638763
  · decide +kernel
  · decide +kernel

private theorem prime_544896287951143 : Nat.Prime 544896287951143 := by
  apply certify _ 3 [(2, 1), (3, 1), (41, 1), (53, 1), (131, 1), (13309, 1), (23971, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_13309
    · exact prime_23971
  · decide +kernel
  · decide +kernel

private theorem prime_631331429277859 : Nat.Prime 631331429277859 := by
  apply certify _ 2 [(2, 1), (3, 1), (271, 1), (359, 1), (1081539587, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1081539587
  · decide +kernel
  · decide +kernel

private theorem prime_1165527773351003 : Nat.Prime 1165527773351003 := by
  apply certify _ 2 [(2, 1), (643, 1), (4937, 1), (183577111, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_4937
    · exact prime_183577111
  · decide +kernel
  · decide +kernel

private theorem prime_2575135369222133 : Nat.Prime 2575135369222133 := by
  apply certify _ 2 [(2, 2), (23, 1), (53, 1), (528124563007, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_528124563007
  · decide +kernel
  · decide +kernel

private theorem prime_3585642171096043 : Nat.Prime 3585642171096043 := by
  apply certify _ 3 [(2, 1), (3, 4), (89, 1), (248692063469, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_248692063469
  · decide +kernel
  · decide +kernel

private theorem prime_4859376605767591 : Nat.Prime 4859376605767591 := by
  apply certify _ 12 [(2, 1), (3, 1), (5, 1), (29, 1), (92269, 1), (60534853, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_92269
    · exact prime_60534853
  · decide +kernel
  · decide +kernel

private theorem prime_6065932345248247 : Nat.Prime 6065932345248247 := by
  apply certify _ 3 [(2, 1), (3, 1), (21651121, 1), (46694521, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_21651121
    · exact prime_46694521
  · decide +kernel
  · decide +kernel

private theorem prime_6708178025567341 : Nat.Prime 6708178025567341 := by
  apply certify _ 6 [(2, 2), (3, 1), (5, 1), (7, 1), (167, 1), (2521, 1), (37937261, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2521
    · exact prime_37937261
  · decide +kernel
  · decide +kernel

private theorem prime_21437605762796233 : Nat.Prime 21437605762796233 := by
  apply certify _ 5 [(2, 3), (3, 2), (29, 1), (47, 1), (218447926987, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_218447926987
  · decide +kernel
  · decide +kernel

private theorem prime_27598490420822947 : Nat.Prime 27598490420822947 := by
  apply certify _ 2 [(2, 1), (3, 2), (19, 1), (337969, 1), (238771427, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_337969
    · exact prime_238771427
  · decide +kernel
  · decide +kernel

private theorem prime_36336800512160839 : Nat.Prime 36336800512160839 := by
  apply certify _ 3 [(2, 1), (3, 2), (223, 1), (9052516320917, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_9052516320917
  · decide +kernel
  · decide +kernel

private theorem prime_58312519269211093 : Nat.Prime 58312519269211093 := by
  apply certify _ 2 [(2, 2), (3, 1), (4859376605767591, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_4859376605767591
  · decide +kernel
  · decide +kernel

private theorem prime_106906181114016397 : Nat.Prime 106906181114016397 := by
  apply certify _ 22 [(2, 2), (3, 2), (7, 1), (17, 1), (31, 1), (804992177299, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_804992177299
  · decide +kernel
  · decide +kernel

private theorem prime_118505370149481239 : Nat.Prime 118505370149481239 := by
  apply certify _ 11 [(2, 1), (7, 1), (11, 2), (69955944598277, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_69955944598277
  · decide +kernel
  · decide +kernel

private theorem prime_178448335245923551 : Nat.Prime 178448335245923551 := by
  apply certify _ 6 [(2, 1), (3, 1), (5, 2), (73553, 1), (16174127069, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_73553
    · exact prime_16174127069
  · decide +kernel
  · decide +kernel

private theorem prime_1039454884912343621 : Nat.Prime 1039454884912343621 := by
  apply certify _ 2 [(2, 2), (5, 1), (7, 1), (127, 1), (8951, 1), (49019, 1), (133241, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_8951
    · exact prime_49019
    · exact prime_133241
  · decide +kernel
  · decide +kernel

private theorem prime_1863545304792909061 : Nat.Prime 1863545304792909061 := by
  apply certify _ 6 [(2, 2), (3, 2), (5, 1), (19, 1), (544896287951143, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_544896287951143
  · decide +kernel
  · decide +kernel

private theorem prime_5022872233605666871 : Nat.Prime 5022872233605666871 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (1093, 1), (5557, 1), (27565782029, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_5557
    · exact prime_27565782029
  · decide +kernel
  · decide +kernel

private theorem prime_14648913693107146357 : Nat.Prime 14648913693107146357 := by
  apply certify _ 2 [(2, 2), (3, 1), (61, 1), (60703897, 1), (329668739, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_60703897
    · exact prime_329668739
  · decide +kernel
  · decide +kernel

private theorem prime_299051868215083704971 : Nat.Prime 299051868215083704971 := by
  apply certify _ 6 [(2, 1), (5, 1), (823, 1), (36336800512160839, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_36336800512160839
  · decide +kernel
  · decide +kernel

private theorem prime_353729277480602391317 : Nat.Prime 353729277480602391317 := by
  apply certify _ 2 [(2, 2), (13, 1), (601, 1), (1831, 1), (63617, 1), (97169879, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1831
    · exact prime_63617
    · exact prime_97169879
  · decide +kernel
  · decide +kernel

private theorem prime_614789822365154359909 : Nat.Prime 614789822365154359909 := by
  apply certify _ 6 [(2, 2), (3, 1), (101, 1), (439, 1), (7027, 1), (164433225403, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_7027
    · exact prime_164433225403
  · decide +kernel
  · decide +kernel

private theorem prime_974736250413007345943 : Nat.Prime 974736250413007345943 := by
  apply certify _ 7 [(2, 1), (7, 1), (577, 1), (8537, 1), (14134419850597, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_8537
    · exact prime_14134419850597
  · decide +kernel
  · decide +kernel

private theorem prime_1975395304598545436017 : Nat.Prime 1975395304598545436017 := by
  apply certify _ 10 [(2, 4), (3, 1), (440239, 1), (2161759, 1), (43243117, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_440239
    · exact prime_2161759
    · exact prime_43243117
  · decide +kernel
  · decide +kernel

private theorem prime_4440908034265130232169 : Nat.Prime 4440908034265130232169 := by
  apply certify _ 11 [(2, 3), (3, 1), (7, 1), (13, 1), (137, 1), (74761, 1), (198528781261, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_74761
    · exact prime_198528781261
  · decide +kernel
  · decide +kernel

private theorem prime_55993568495231890452157 : Nat.Prime 55993568495231890452157 := by
  apply certify _ 2 [(2, 2), (3, 1), (217661, 1), (21437605762796233, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_217661
    · exact prime_21437605762796233
  · decide +kernel
  · decide +kernel

private theorem prime_1310045520555081872947393 : Nat.Prime 1310045520555081872947393 := by
  apply certify _ 10 [(2, 6), (3, 1), (7, 1), (974736250413007345943, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_974736250413007345943
  · decide +kernel
  · decide +kernel

private theorem prime_1339318016517813805619527 : Nat.Prime 1339318016517813805619527 := by
  apply certify _ 5 [(2, 1), (3, 1), (113, 1), (1975395304598545436017, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1975395304598545436017
  · decide +kernel
  · decide +kernel

private theorem prime_5160441010808557806518429 : Nat.Prime 5160441010808557806518429 := by
  apply certify _ 3 [(2, 2), (11, 1), (29, 1), (34127, 1), (118505370149481239, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_34127
    · exact prime_118505370149481239
  · decide +kernel
  · decide +kernel

private theorem prime_14731071218372842851056069 : Nat.Prime 14731071218372842851056069 := by
  apply certify _ 2 [(2, 2), (169199, 1), (4062701, 1), (5357493895483, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · exact prime_169199
    · exact prime_4062701
    · exact prime_5357493895483
  · decide +kernel
  · decide +kernel

private theorem prime_72246174151319809291258007 : Nat.Prime 72246174151319809291258007 := by
  apply certify _ 5 [(2, 1), (7, 1), (5160441010808557806518429, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_5160441010808557806518429
  · decide +kernel
  · decide +kernel

private theorem prime_81467999847607904321136377 : Nat.Prime 81467999847607904321136377 := by
  apply certify _ 3 [(2, 3), (695171, 1), (14648913693107146357, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · exact prime_695171
    · exact prime_14648913693107146357
  · decide +kernel
  · decide +kernel

private theorem prime_553143617296955601932204753 : Nat.Prime 553143617296955601932204753 := by
  apply certify _ 3 [(2, 4), (53, 1), (1061, 1), (614789822365154359909, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_614789822365154359909
  · decide +kernel
  · decide +kernel

private theorem prime_6053413019594444547884628917 : Nat.Prime 6053413019594444547884628917 := by
  apply certify _ 2 [(2, 2), (311, 1), (2611199, 1), (1863545304792909061, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2611199
    · exact prime_1863545304792909061
  · decide +kernel
  · decide +kernel

private theorem prime_148303579333636000036955565587 : Nat.Prime 148303579333636000036955565587 := by
  apply certify _ 2 [(2, 1), (247956283, 1), (299051868215083704971, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · exact prime_247956283
    · exact prime_299051868215083704971
  · decide +kernel
  · decide +kernel

private theorem prime_232921665463855065155015814569 : Nat.Prime 232921665463855065155015814569 := by
  apply certify _ 3 [(2, 3), (13, 1), (31, 1), (72246174151319809291258007, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_72246174151319809291258007
  · decide +kernel
  · decide +kernel

private theorem prime_90778245483882153483569567724259 : Nat.Prime 90778245483882153483569567724259 := by
  apply certify _ 3 [(2, 1), (3, 1), (7, 1), (13, 1), (37337, 1), (59791, 1), (3262224011, 1), (22829695829, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_37337
    · exact prime_59791
    · exact prime_3262224011
    · exact prime_22829695829
  · decide +kernel
  · decide +kernel

private theorem prime_265457494880237509401972762941993 : Nat.Prime 265457494880237509401972762941993 := by
  apply certify _ 3 [(2, 3), (5023, 1), (18675439, 1), (353729277480602391317, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · exact prime_5023
    · exact prime_18675439
    · exact prime_353729277480602391317
  · decide +kernel
  · decide +kernel

private theorem prime_19386837104810232468830979355794989 : Nat.Prime 19386837104810232468830979355794989 := by
  apply certify _ 2 [(2, 2), (11, 1), (2971, 1), (148303579333636000036955565587, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2971
    · exact prime_148303579333636000036955565587
  · decide +kernel
  · decide +kernel

private theorem prime_282789059470568586463609095534188131 : Nat.Prime 282789059470568586463609095534188131 := by
  apply certify _ 15 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (37, 1), (102678983629, 1), (1039454884912343621, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_102678983629
    · exact prime_1039454884912343621
  · decide +kernel
  · decide +kernel

private theorem prime_23567721955657194776649723510218140673 : Nat.Prime 23567721955657194776649723510218140673 := by
  apply certify _ 3 [(2, 10), (937, 1), (2729, 1), (3495219533167, 1), (2575135369222133, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2729
    · exact prime_3495219533167
    · exact prime_2575135369222133
  · decide +kernel
  · decide +kernel

private theorem prime_410716897908682995496769866714903337573 : Nat.Prime 410716897908682995496769866714903337573 := by
  apply certify _ 2 [(2, 2), (17, 1), (61, 1), (373, 1), (265457494880237509401972762941993, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_265457494880237509401972762941993
  · decide +kernel
  · decide +kernel

private theorem prime_31260942106937851086988820434353782113597 : Nat.Prime 31260942106937851086988820434353782113597 := by
  apply certify _ 2 [(2, 2), (3, 2), (7, 1), (5182379, 1), (5390146523, 1), (4440908034265130232169, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_5182379
    · exact prime_5390146523
    · exact prime_4440908034265130232169
  · decide +kernel
  · decide +kernel

private theorem prime_2567189623092244449323981439041677545536149 : Nat.Prime 2567189623092244449323981439041677545536149 := by
  apply certify _ 2 [(2, 2), (3, 1), (13, 1), (58193, 1), (282789059470568586463609095534188131, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_58193
    · exact prime_282789059470568586463609095534188131
  · decide +kernel
  · decide +kernel

private theorem prime_8373094558265845827516770230329627536146799 : Nat.Prime 8373094558265845827516770230329627536146799 := by
  apply certify _ 7 [(2, 1), (5839, 1), (47809, 1), (11197579487, 1), (1339318016517813805619527, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · exact prime_5839
    · exact prime_47809
    · exact prime_11197579487
    · exact prime_1339318016517813805619527
  · decide +kernel
  · decide +kernel

private theorem prime_165337136995061861490728657086431249608356451 : Nat.Prime 165337136995061861490728657086431249608356451 := by
  apply certify _ 2 [(2, 1), (5, 2), (79, 1), (461096189, 1), (90778245483882153483569567724259, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_461096189
    · exact prime_90778245483882153483569567724259
  · decide +kernel
  · decide +kernel

private theorem prime_334130122469124376448502703576854973706716799 : Nat.Prime 334130122469124376448502703576854973706716799 := by
  apply certify _ 17 [(2, 1), (27598490420822947, 1), (6053413019594444547884628917, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · norm_num
    · exact prime_27598490420822947
    · exact prime_6053413019594444547884628917
  · decide +kernel
  · decide +kernel

private theorem prime_472362132581542660756039516449996870043763098571 : Nat.Prime 472362132581542660756039516449996870043763098571 := by
  apply certify _ 2 [(2, 1), (5, 1), (2309, 1), (4676323, 1), (3339337037807, 1), (1310045520555081872947393, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_2309
    · exact prime_4676323
    · exact prime_3339337037807
    · exact prime_1310045520555081872947393
  · decide +kernel
  · decide +kernel

private theorem prime_166537906346951949512555048980432872272371711730863 : Nat.Prime 166537906346951949512555048980432872272371711730863 := by
  apply certify _ 5 [(2, 1), (3, 1), (47, 1), (53, 1), (139, 1), (6917, 1), (12882676069, 1), (15427219380457, 1), (58312519269211093, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_6917
    · exact prime_12882676069
    · exact prime_15427219380457
    · exact prime_58312519269211093
  · decide +kernel
  · decide +kernel

private theorem prime_7605097443758365136139127684454071607399120106122204869 : Nat.Prime 7605097443758365136139127684454071607399120106122204869 := by
  apply certify _ 11 [(2, 2), (3, 1), (7, 1), (4931, 1), (7152083, 1), (2567189623092244449323981439041677545536149, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4931
    · exact prime_7152083
    · exact prime_2567189623092244449323981439041677545536149
  · decide +kernel
  · decide +kernel

private theorem prime_172065054976772107675581285529480503164616022973170886021 : Nat.Prime 172065054976772107675581285529480503164616022973170886021 := by
  apply certify _ 2 [(2, 2), (5, 1), (7, 1), (146783975557, 1), (8373094558265845827516770230329627536146799, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_146783975557
    · exact prime_8373094558265845827516770230329627536146799
  · decide +kernel
  · decide +kernel

private theorem prime_297944641350014385275436610378443430138886610872100450151 : Nat.Prime 297944641350014385275436610378443430138886610872100450151 := by
  apply certify _ 21 [(2, 1), (3, 1), (5, 2), (11927, 1), (166537906346951949512555048980432872272371711730863, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_11927
    · exact prime_166537906346951949512555048980432872272371711730863
  · decide +kernel
  · decide +kernel

private theorem prime_273555355051988393946924422809812955718146350217215709137931 : Nat.Prime 273555355051988393946924422809812955718146350217215709137931 := by
  apply certify _ 3 [(2, 1), (3, 1), (5, 1), (11, 1), (109, 1), (7605097443758365136139127684454071607399120106122204869, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_7605097443758365136139127684454071607399120106122204869
  · decide +kernel
  · decide +kernel

private theorem prime_40687297931583212434454439521483153605327032354191178561100493 : Nat.Prime 40687297931583212434454439521483153605327032354191178561100493 := by
  apply certify _ 2 [(2, 2), (4037183, 1), (106906181114016397, 1), (23567721955657194776649723510218140673, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · norm_num
    · exact prime_4037183
    · exact prime_106906181114016397
    · exact prime_23567721955657194776649723510218140673
  · decide +kernel
  · decide +kernel

private theorem prime_6297297448939257420492825692420433831955731153612194642748437393 : Nat.Prime 6297297448939257420492825692420433831955731153612194642748437393 := by
  apply certify _ 5 [(2, 4), (7, 1), (31, 1), (83, 1), (127, 1), (172065054976772107675581285529480503164616022973170886021, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_172065054976772107675581285529480503164616022973170886021
  · decide +kernel
  · decide +kernel

private theorem prime_30463286638653519166134094991866993173323371437334932151335007280987 : Nat.Prime 30463286638653519166134094991866993173323371437334932151335007280987 := by
  apply certify _ 2 [(2, 1), (691, 1), (7057, 1), (2380463, 1), (31569287, 1), (178448335245923551, 1), (232921665463855065155015814569, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_7057
    · exact prime_2380463
    · exact prime_31569287
    · exact prime_178448335245923551
    · exact prime_232921665463855065155015814569
  · decide +kernel
  · decide +kernel

private theorem prime_61471288489178400502227511463990027154771532183167217954139642300211427949197 : Nat.Prime 61471288489178400502227511463990027154771532183167217954139642300211427949197 := by
  apply certify _ 2 [(2, 2), (3, 4), (569, 1), (26360903, 1), (1625900707, 1), (47053325621, 1), (165337136995061861490728657086431249608356451, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_26360903
    · exact prime_1625900707
    · exact prime_47053325621
    · exact prime_165337136995061861490728657086431249608356451
  · decide +kernel
  · decide +kernel

private theorem prime_446092199703710200243488189611814726284358184224501445344992905869145850914339049 : Nat.Prime 446092199703710200243488189611814726284358184224501445344992905869145850914339049 := by
  apply certify _ 3 [(2, 3), (19, 1), (653, 1), (2653541220611, 1), (3585642171096043, 1), (472362132581542660756039516449996870043763098571, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2653541220611
    · exact prime_3585642171096043
    · exact prime_472362132581542660756039516449996870043763098571
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 := by
  apply certify _ 3 [(2, 1), (3, 1), (11, 1), (409, 1), (9011, 1), (9829, 1), (6708178025567341, 1), (6297297448939257420492825692420433831955731153612194642748437393, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_9011
    · exact prime_9829
    · exact prime_6708178025567341
    · exact prime_6297297448939257420492825692420433831955731153612194642748437393
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 := by
  apply certify _ 7 [(2, 3), (3, 1), (17, 1), (1567, 1), (14731071218372842851056069, 1), (553143617296955601932204753, 1), (19386837104810232468830979355794989, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1567
    · exact prime_14731071218372842851056069
    · exact prime_553143617296955601932204753
    · exact prime_19386837104810232468830979355794989
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 := by
  apply certify _ 2 [(2, 1), (3, 2), (929, 1), (248827, 1), (81467999847607904321136377, 1), (297944641350014385275436610378443430138886610872100450151, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_248827
    · exact prime_81467999847607904321136377
    · exact prime_297944641350014385275436610378443430138886610872100450151
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 := by
  apply certify _ 2 [(2, 2), (3, 1), (31, 1), (991, 1), (1110031619, 1), (6065932345248247, 1), (40687297931583212434454439521483153605327032354191178561100493, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1110031619
    · exact prime_6065932345248247
    · exact prime_40687297931583212434454439521483153605327032354191178561100493
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 := by
  apply certify _ 3 [(2, 1), (3, 1), (23, 1), (4783, 1), (5022872233605666871, 1), (30463286638653519166134094991866993173323371437334932151335007280987, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4783
    · exact prime_5022872233605666871
    · exact prime_30463286638653519166134094991866993173323371437334932151335007280987
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 := by
  apply certify _ 7 [(2, 4), (3, 3), (97, 1), (157351, 1), (55993568495231890452157, 1), (273555355051988393946924422809812955718146350217215709137931, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_157351
    · exact prime_55993568495231890452157
    · exact prime_273555355051988393946924422809812955718146350217215709137931
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 := by
  apply certify _ 3 [(2, 1), (3, 1), (13, 1), (4975823, 1), (1058408119, 1), (631331429277859, 1), (1165527773351003, 1), (334130122469124376448502703576854973706716799, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_4975823
    · exact prime_1058408119
    · exact prime_631331429277859
    · exact prime_1165527773351003
    · exact prime_334130122469124376448502703576854973706716799
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 := by
  apply certify _ 7 [(2, 2), (3, 1), (59, 1), (319779389, 1), (446092199703710200243488189611814726284358184224501445344992905869145850914339049, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_319779389
    · exact prime_446092199703710200243488189611814726284358184224501445344992905869145850914339049
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 := by
  apply certify _ 3 [(2, 1), (3, 2), (199, 1), (475141, 1), (965357, 1), (61471288489178400502227511463990027154771532183167217954139642300211427949197, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_475141
    · exact prime_965357
    · exact prime_61471288489178400502227511463990027154771532183167217954139642300211427949197
  · decide +kernel
  · decide +kernel

private theorem prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 := by
  apply certify _ 7 [(2, 3), (3, 1), (327757380757, 1), (410716897908682995496769866714903337573, 1), (31260942106937851086988820434353782113597, 1)]
  · decide +kernel
  · decide +kernel
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_327757380757
    · exact prime_410716897908682995496769866714903337573
    · exact prime_31260942106937851086988820434353782113597
  · decide +kernel
  · decide +kernel

private def first : ℕ := 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719

private def divisors0 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 61, 2, 3, 2, 17,
   2, 13, 2, 3, 2, 137, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 73, 2, 3,
   2, 5, 2, 19, 2, 3, 2, 41, 2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 103, 2, 5,
   2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 43, 2, 71, 2, 3, 2, 67,
   2, 17, 2, 3, 2, 139, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 151, 2, 3,
   2, 59, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 89, 2, 0,
   2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 37, 2, 3, 2, 179, 2, 127, 2, 3, 2, 13,
   2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 163, 2, 3,
   2, 0, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2, 17, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 173, 2, 149, 2, 3, 2, 11, 2]

private lemma gap0 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 0 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors0) (by decide +kernel) j hj

private def divisors1 : List ℕ :=
  [2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 4271, 2, 3, 2, 13,
   2, 29, 2, 3, 2, 19, 2, 7, 2, 3, 2, 601, 2, 5, 2, 3, 2, 263, 2, 11, 2, 3,
   2, 5, 2, 13, 2, 3, 2, 61, 2, 23, 2, 3, 2, 7, 2, 103, 2, 3, 2, 11, 2, 5,
   2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 29, 2, 17, 2, 3, 2, 41,
   2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 251, 2, 3, 2, 5, 2, 11, 2, 3,
   2, 0, 2, 7, 2, 3, 2, 17, 2, 53, 2, 3, 2, 73, 2, 5, 2, 3, 2, 11, 2, 167,
   2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 157, 2, 47, 2, 3, 2, 563,
   2, 5, 2, 3, 2, 97, 2, 139, 2, 3, 2, 5, 2, 181, 2, 3, 2, 113, 2, 11, 2, 3,
   2, 13, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 223, 2, 23, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 31, 2, 13, 2, 3, 2, 191, 2]

private lemma gap1 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 1 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors1) (by decide +kernel) j hj

private def divisors2 : List ℕ :=
  [2, 3, 2, 367, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 487,
   2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 2741, 2, 41, 2, 3,
   2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 73, 2, 3, 2, 3329, 2, 5,
   2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 149, 2, 19, 2, 3, 2, 0,
   2, 71, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 107, 2, 3,
   2, 17, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 241, 2, 739,
   2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0,
   2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 193, 2, 0, 2, 3,
   2, 31, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 613, 2, 0, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 13, 2, 67, 2, 3, 2, 61, 2]

private lemma gap2 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 2 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors2) (by decide +kernel) j hj

private def divisors3 : List ℕ :=
  [2, 3, 2, 17, 2, 5, 2, 3, 2, 29, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 71,
   2, 0, 2, 3, 2, 127, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 11, 2, 157, 2, 3,
   2, 5, 2, 23, 2, 3, 2, 103, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5,
   2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 151, 2, 11, 2, 3, 2, 4679,
   2, 313, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3,
   2, 107, 2, 7, 2, 3, 2, 2347, 2, 61, 2, 3, 2, 53, 2, 5, 2, 3, 2, 281, 2, 0,
   2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 11, 2, 3, 2, 31,
   2, 5, 2, 3, 2, 41, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3,
   2, 19, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 0, 2, 113, 2, 3, 2, 17, 2]

private lemma gap3 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 3 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors3) (by decide +kernel) j hj

private def divisors4 : List ℕ :=
  [2, 3, 2, 109, 2, 5, 2, 3, 2, 137, 2, 937, 2, 3, 2, 5, 2, 227, 2, 3, 2, 23,
   2, 179, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3,
   2, 5, 2, 103, 2, 3, 2, 67, 2, 173, 2, 3, 2, 7, 2, 3499, 2, 3, 2, 1009, 2, 5,
   2, 3, 2, 269, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 47, 2, 3, 2, 139,
   2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3,
   2, 97, 2, 7, 2, 3, 2, 37, 2, 13, 2, 3, 2, 4871, 2, 5, 2, 3, 2, 31, 2, 2699,
   2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 397, 2, 3, 2, 61,
   2, 5, 2, 3, 2, 11, 2, 101, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 151, 2, 3,
   2, 47, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 17, 2, 11, 2, 3, 2, 431, 2]

private lemma gap4 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 4 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors4) (by decide +kernel) j hj

private def divisors5 : List ℕ :=
  [2, 3, 2, 131, 2, 5, 2, 3, 2, 113, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53,
   2, 19, 2, 3, 2, 71, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3,
   2, 5, 2, 149, 2, 3, 2, 181, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 43, 2, 5,
   2, 3, 2, 3253, 2, 7, 2, 3, 2, 5, 2, 331, 2, 3, 2, 11, 2, 83, 2, 3, 2, 23,
   2, 2693, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 163, 2, 3, 2, 5, 2, 367, 2, 3,
   2, 29, 2, 7, 2, 3, 2, 13, 2, 107, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 191,
   2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 101,
   2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 179, 2, 1949, 2, 3,
   2, 79, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 11, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2]

private lemma gap5 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 5 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors5) (by decide +kernel) j hj

private def divisors6 : List ℕ :=
  [2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 41,
   2, 53, 2, 3, 2, 0, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3,
   2, 5, 2, 11, 2, 3, 2, 227, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5,
   2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 31, 2, 167, 2, 3, 2, 17,
   2, 13, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 23, 2, 3,
   2, 43, 2, 7, 2, 3, 2, 19, 2, 2389, 2, 3, 2, 107, 2, 5, 2, 3, 2, 53, 2, 0,
   2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 59, 2, 3, 2, 23,
   2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 631, 2, 3,
   2, 257, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 11, 2, 181, 2, 3, 2, 503, 2]

private lemma gap6 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 6 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors6) (by decide +kernel) j hj

private def divisors7 : List ℕ :=
  [2, 3, 2, 4603, 2, 5, 2, 3, 2, 13, 2, 61, 2, 3, 2, 5, 2, 47, 2, 3, 2, 19,
   2, 0, 2, 3, 2, 109, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 29, 2, 113, 2, 3,
   2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 19, 2, 3, 2, 97, 2, 5,
   2, 3, 2, 311, 2, 7, 2, 3, 2, 5, 2, 317, 2, 3, 2, 17, 2, 89, 2, 3, 2, 13,
   2, 0, 2, 3, 2, 191, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 131, 2, 3,
   2, 47, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 53,
   2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 157, 2, 3, 2, 151, 2, 17, 2, 3, 2, 37,
   2, 5, 2, 3, 2, 43, 2, 83, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3,
   2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 137, 2, 127, 2, 3, 2, 167, 2]

private lemma gap7 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 7 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors7) (by decide +kernel) j hj

private def divisors8 : List ℕ :=
  [2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 37, 2, 3, 2, 79,
   2, 11, 2, 3, 2, 53, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3,
   2, 5, 2, 97, 2, 3, 2, 89, 2, 907, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5,
   2, 3, 2, 193, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 139, 2, 59, 2, 3, 2, 0,
   2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 71, 2, 3,
   2, 11, 2, 7, 2, 3, 2, 83, 2, 29, 2, 3, 2, 163, 2, 5, 2, 3, 2, 101, 2, 107,
   2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 67, 2, 3, 2, 19,
   2, 5, 2, 3, 2, 131, 2, 1933, 2, 3, 2, 5, 2, 61, 2, 3, 2, 5779, 2, 521, 2, 3,
   2, 11, 2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 7,
   2, 3, 2, 59, 2, 281, 2, 3, 2, 43, 2]

private lemma gap8 (j : ℕ) (hj : j < 209) :
    ¬ Nat.Prime (first + 8 * 210 + 1 + j) := by
  exact gap_sound (ds := divisors8) (by decide +kernel) j hj

end OMA.ConsecutivePrimes

open OMA.ConsecutivePrimes in
theorem OMA.solution : type_of% @Erdos141.erdos_141.variants.first_cases := by
  intro k _ hk
  apply progressions first _ _ k hk
  · intro i hi
    interval_cases i
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399
    · exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609
  · intro i hi
    interval_cases i
    · exact gap0
    · exact gap1
    · exact gap2
    · exact gap3
    · exact gap4
    · exact gap5
    · exact gap6
    · exact gap7
    · exact gap8
