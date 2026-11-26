import FormalConjectures.OEIS.«100475»
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting

/-! Reversing the decimal digits of a prime preserves its length. For every
power of ten from 100000 onward, fewer than one tenth as many integers up to
that power are prime. The corresponding prime-index map therefore strictly
increases digit length for primes of at least five digits.

For the first three bounds we count integers avoiding a finite set of primes
by Legendre's sieve recurrence. Induction extends the bound using the
primorial estimate. For smaller primes a secondary rank, checked on the
complete finite transition graph, increases within a fixed digit length. -/

namespace OMA.ReversePrime

open Finset

def phi : List ℕ → ℕ → ℕ
  | [], n => n
  | p :: ps, n => if n ≤ 1 then n else phi ps n - phi ps (n / p)

def survivors (ps : List ℕ) (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun k => ∀ p ∈ ps, ¬ p ∣ k)

lemma mem_survivors {ps : List ℕ} {n x : ℕ} :
    x ∈ survivors ps n ↔ (1 ≤ x ∧ x ≤ n) ∧ ∀ q ∈ ps, ¬ q ∣ x := by
  simp [survivors]

lemma phi_card (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ps.Nodup) (n : ℕ) :
    phi ps n = (survivors ps n).card := by
  induction ps generalizing n with
  | nil => simp [phi, survivors]
  | cons p ps ih =>
    have pp := hp p (by simp)
    have hps : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (by simp [hq])
    obtain ⟨hnmem, hd'⟩ := List.nodup_cons.mp hd
    rw [phi]
    split_ifs with small
    · interval_cases n
      · simp [survivors]
      · have noOne : ∀ q ∈ p::ps, ¬q ∣ 1 := fun q hq h => (hp q hq).ne_one (Nat.dvd_one.mp h)
        unfold survivors
        rw [show Icc 1 1 = {1} by decide, Finset.filter_singleton]
        simp only [if_pos noOne, Finset.card_singleton]
    · let A := survivors ps n
      have ha : survivors (p::ps) n = A.filter (fun x => ¬ p ∣ x) := by
        ext k
        simp only [Finset.mem_filter, A, mem_survivors, List.forall_mem_cons]
        tauto
      have hb : A.filter (fun x => p ∣ x) = (survivors ps (n/p)).image (p * ·) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image, A, mem_survivors]
        constructor
        · rintro ⟨⟨⟨hx,hxn⟩,hs⟩, k, rfl⟩
          refine ⟨k, ⟨⟨?_, (Nat.le_div_iff_mul_le pp.pos).2 (by simpa [mul_comm] using hxn)⟩, ?_⟩, rfl⟩
          · by_contra! h
            have : k = 0 := by omega
            simp [this] at hx
          · exact fun q hq hk => hs q hq (dvd_mul_of_dvd_right hk p)
        · rintro ⟨k, ⟨⟨hk,hkn⟩,hs⟩, rfl⟩
          refine ⟨⟨⟨Nat.mul_pos pp.pos hk, ?_⟩, ?_⟩, dvd_mul_right p k⟩
          · simpa [mul_comm] using (Nat.le_div_iff_mul_le pp.pos).1 hkn
          · intro q hq hdiv
            rcases (hps q hq).dvd_mul.mp hdiv with h | h
            · exact hnmem (((Nat.dvd_prime pp).mp h).resolve_left (hps q hq).ne_one ▸ hq)
            · exact hs q hq h
      have hc := card_filter_add_card_filter_not (s := A) (fun x => p ∣ x)
      rw [hb, card_image_of_injective _ (mul_right_injective₀ pp.ne_zero)] at hc
      rw [ha, ih hps hd' n, ih hps hd' (n / p)]
      change A.card - _ = _
      omega

lemma count_bound (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ps.Nodup) (n : ℕ) :
    n.primeCounting ≤ phi ps n + ps.length := by
  have sub : n.primesLE ⊆ survivors ps n ∪ ps.toFinset := by
    intro k hk
    obtain ⟨hkn,hk'⟩ := Nat.mem_primesLE.mp hk
    by_cases h : k ∈ ps
    · exact mem_union_right _ (by simpa using h)
    · refine mem_union_left _ (mem_survivors.mpr ⟨⟨hk'.pos,hkn⟩, ?_⟩)
      intro q hq hdiv
      have eq := ((Nat.dvd_prime hk').mp hdiv).resolve_left (hp q hq).ne_one
      exact h (eq ▸ hq)
  rw [← Nat.primesLE_card_eq_primeCounting, phi_card ps hp hd, ← List.toFinset_card_of_nodup hd]
  exact (card_le_card sub).trans (card_union_le _ _)


def primes5 : List ℕ := [199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma small_pi5 : Nat.primeCounting 100000 < 10000 := by
  have h := count_bound primes5 (by decide +kernel) (by decide +kernel) 100000
  exact lt_of_le_of_lt h (by decide +kernel)

def primes6 : List ℕ := [239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma small_pi6 : Nat.primeCounting 1000000 < 100000 := by
  have h := count_bound primes6 (by decide +kernel) (by decide +kernel) 1000000
  exact lt_of_le_of_lt h (by decide +kernel)

def primes7 : List ℕ := [269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma small_pi7 : Nat.primeCounting 10000000 < 1000000 := by
  have h := count_bound primes7 (by decide +kernel) (by decide +kernel) 10000000
  exact lt_of_le_of_lt h (by decide +kernel)

open Finset

lemma prime_step (t : ℕ) (ht : 1000000 ≤ t) (h : (10*t).primeCounting < t) :
    (100*t).primeCounting < 10*t := by
  by_contra! bad
  let B := (100*t).primesLE \ (10*t).primesLE
  have sub := Nat.primesLE_mono (show 10*t ≤ 100*t by omega)
  have card : 9*t ≤ B.card := by
    dsimp [B]
    rw [card_sdiff_of_subset sub, Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
    omega
  have lo : ∀ p ∈ B, 10^7 ≤ p := by
    intro p hp
    obtain ⟨hi, no⟩ := mem_sdiff.mp hp
    have prime := Nat.prime_of_mem_primesLE hi
    have : ¬ p ≤ 10*t := fun hp => no (Nat.mem_primesLE.mpr ⟨hp,prime⟩)
    norm_num
    omega
  have lower : (10^7 : ℕ) ^ (9*t) ≤ primorial (100*t) := calc
    _ ≤ (10^7 : ℕ)^B.card := Nat.pow_le_pow_right (by decide) card
    _ = ∏ _p ∈ B, (10^7 : ℕ) := by simp
    _ ≤ ∏ p ∈ B, p := Finset.prod_le_prod' lo
    _ ≤ ∏ p ∈ (100*t).primesLE, p := Finset.prod_le_prod_of_subset_of_one_le'
      (by exact sdiff_subset) (fun p hp _ => (Nat.prime_of_mem_primesLE hp).one_le)
    _ = _ := rfl
  have upper := primorial_lt_four_pow (100*t) (by omega)
  rw [pow_mul] at lower upper
  exact (Nat.pow_le_pow_left (by decide : 4^100 ≤ (10^7 : ℕ)^9) t).not_gt
    (lt_of_le_of_lt lower upper)
lemma all_pi (d : ℕ) (hd : 4 ≤ d) : (10^(d+1)).primeCounting < 10^d := by
  by_cases h4 : d = 4
  · subst d; exact small_pi5
  by_cases h5 : d = 5
  · subst d; exact small_pi6
  have h6 : 6 ≤ d := by omega
  clear hd h4 h5
  induction d, h6 using Nat.le_induction with
  | base => exact small_pi7
  | succ d hd ih =>
    have ht : 10^6 ≤ (10:ℕ)^d := Nat.pow_le_pow_right (by decide) hd
    have prior : (10*10^d).primeCounting < 10^d := by simpa only [pow_succ, mul_comm] using ih
    rw [show 10^(d+1+1) = 100*10^d by ring, show 10^(d+1) = 10*10^d by ring]
    exact prime_step _ ht prior

open OeisA100475

def phase (n : ℕ) : ℕ :=
  if n = 1020 then 0
  else if n ∈ ([1, 11, 1118] : List ℕ) then 1
  else if n ∈ ([2, 13, 18, 20, 100, 110, 115, 116, 121, 126, 133, 135, 141, 142, 156, 160, 1009, 1019, 1031, 1043, 1060, 1120, 1143, 1152, 1178, 1185, 1210, 1221] : List ℕ) then 2
  else if n ≤ 4 ∨ (10 ≤ n ∧ n ≤ 25) ∨ (100 ≤ n ∧ n ≤ 168) ∨ (1000 ≤ n ∧ n ≤ 1229) then 3 else 4

def score (n : ℕ) := 5 * (Nat.digits 10 n).length + phase n

lemma phase_le (n : ℕ) : phase n ≤ 4 := by unfold phase; split_ifs <;> decide

lemma score_lt_of_digits {a b : ℕ} (h : (Nat.digits 10 a).length < (Nat.digits 10 b).length) :
    score a < score b := by
  have ha := phase_le a
  unfold score
  omega

def trial (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (Nat.sqrt p - 1)).all fun j => p % j != 0

lemma trial_iff (p : ℕ) : trial p = true ↔ p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [trial, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1, bne_iff_ne, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun m hm hmp => h m ⟨hm, by omega⟩⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun m ⟨hm, hmp⟩ => h m hm (by omega)⟩

/-- Verify every prime transition in a block and its final prime count. -/
def scan : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, c, e => c == e
  | k + 1, p, c, e =>
    if trial p then decide (score (c + 1) < score (reverseDigits p)) && scan k (p + 1) (c + 1) e
    else scan k (p + 1) c e

def State (p c : ℕ) : Prop :=
  p.primeCounting' = c ∧ ∀ q < p, q.Prime → score (q.primeCounting' + 1) < score (reverseDigits q)

lemma advance (k p c e : ℕ) (s : State p c) (h : scan k p c e = true) : State (p+k) e := by
  induction k generalizing p c with
  | zero =>
    have he : c = e := by simpa [scan] using h
    simpa [he] using s
  | succ k ih =>
    rcases s with ⟨hc, before⟩
    rw [scan] at h
    by_cases hp : p.Prime
    · rw [if_pos ((trial_iff p).mpr hp), Bool.and_eq_true] at h
      have next : State (p+1) (c+1) := by
        refine ⟨?_, ?_⟩
        · simpa only [Nat.primeCounting', Nat.count_succ, if_pos hp] using congrArg (·+1) hc
        · intro q hq hprime
          rcases lt_or_eq_of_le (by omega : q ≤ p) with lt | rfl
          · exact before q lt hprime
          · rw [hc]
            exact of_decide_eq_true h.1
      simpa only [Nat.add_right_comm, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k]
        using ih (p+1) (c+1) next h.2
    · rw [if_neg (fun e => hp ((trial_iff p).mp e))] at h
      have next : State (p+1) c := by
        refine ⟨?_, ?_⟩
        · simpa only [Nat.primeCounting', Nat.count_succ, if_neg hp, Nat.add_zero] using hc
        · intro q hq hprime
          have hne : q ≠ p := fun h => hp (h ▸ hprime)
          exact before q (by omega) hprime
      simpa only [Nat.add_right_comm, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k]
        using ih (p+1) c next h

lemma state0 : State 0 0 := ⟨rfl, fun q h => (Nat.not_lt_zero q h).elim⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state200 : State 200 46 :=
  advance 200 0 0 46 state0 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state400 : State 400 78 :=
  advance 200 200 46 78 state200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state600 : State 600 109 :=
  advance 200 400 78 109 state400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state800 : State 800 139 :=
  advance 200 600 109 139 state600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state1000 : State 1000 168 :=
  advance 200 800 139 168 state800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state1200 : State 1200 196 :=
  advance 200 1000 168 196 state1000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state1400 : State 1400 222 :=
  advance 200 1200 196 222 state1200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state1600 : State 1600 251 :=
  advance 200 1400 222 251 state1400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state1800 : State 1800 278 :=
  advance 200 1600 251 278 state1600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state2000 : State 2000 303 :=
  advance 200 1800 278 303 state1800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state2200 : State 2200 327 :=
  advance 200 2000 303 327 state2000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state2400 : State 2400 357 :=
  advance 200 2200 327 357 state2200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state2600 : State 2600 378 :=
  advance 200 2400 357 378 state2400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state2800 : State 2800 407 :=
  advance 200 2600 378 407 state2600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state3000 : State 3000 430 :=
  advance 200 2800 407 430 state2800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state3200 : State 3200 452 :=
  advance 200 3000 430 452 state3000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state3400 : State 3400 478 :=
  advance 200 3200 452 478 state3200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state3600 : State 3600 503 :=
  advance 200 3400 478 503 state3400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state3800 : State 3800 528 :=
  advance 200 3600 503 528 state3600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state4000 : State 4000 550 :=
  advance 200 3800 528 550 state3800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state4200 : State 4200 574 :=
  advance 200 4000 550 574 state4000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state4400 : State 4400 599 :=
  advance 200 4200 574 599 state4200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state4600 : State 4600 622 :=
  advance 200 4400 599 622 state4400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state4800 : State 4800 646 :=
  advance 200 4600 622 646 state4600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state5000 : State 5000 669 :=
  advance 200 4800 646 669 state4800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state5200 : State 5200 692 :=
  advance 200 5000 669 692 state5000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state5400 : State 5400 712 :=
  advance 200 5200 692 712 state5200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state5600 : State 5600 738 :=
  advance 200 5400 712 738 state5400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state5800 : State 5800 760 :=
  advance 200 5600 738 760 state5600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state6000 : State 6000 783 :=
  advance 200 5800 760 783 state5800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state6200 : State 6200 806 :=
  advance 200 6000 783 806 state6000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state6400 : State 6400 834 :=
  advance 200 6200 806 834 state6200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state6600 : State 6600 853 :=
  advance 200 6400 834 853 state6400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state6800 : State 6800 875 :=
  advance 200 6600 853 875 state6600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state7000 : State 7000 900 :=
  advance 200 6800 875 900 state6800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state7200 : State 7200 919 :=
  advance 200 7000 900 919 state7000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state7400 : State 7400 939 :=
  advance 200 7200 919 939 state7200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state7600 : State 7600 965 :=
  advance 200 7400 939 965 state7400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state7800 : State 7800 987 :=
  advance 200 7600 965 987 state7600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state8000 : State 8000 1007 :=
  advance 200 7800 987 1007 state7800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state8200 : State 8200 1028 :=
  advance 200 8000 1007 1028 state8000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state8400 : State 8400 1051 :=
  advance 200 8200 1028 1051 state8200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state8600 : State 8600 1071 :=
  advance 200 8400 1051 1071 state8400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state8800 : State 8800 1095 :=
  advance 200 8600 1071 1095 state8600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state9000 : State 9000 1117 :=
  advance 200 8800 1095 1117 state8800 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state9200 : State 9200 1140 :=
  advance 200 9000 1117 1140 state9000 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state9400 : State 9400 1162 :=
  advance 200 9200 1140 1162 state9200 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state9600 : State 9600 1184 :=
  advance 200 9400 1162 1184 state9400 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state9800 : State 9800 1208 :=
  advance 200 9600 1184 1208 state9600 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma state10000 : State 10000 1229 :=
  advance 200 9800 1208 1229 state9800 (by decide +kernel)

lemma rank_small (p : ℕ) (hp : p.Prime) (hlt : p < 10000) :
    score (p.primeCounting' + 1) < score (reverseDigits p) :=
  state10000.2 p hlt hp

lemma reversed_length (p : ℕ) (hp : p.Prime) :
    (Nat.digits 10 (reverseDigits p)).length = (Nat.digits 10 p).length := by
  have last : p % 10 ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h) with h | h
    · omega
    · exact (by decide : ¬ Nat.Prime 10) (h ▸ hp)
  have head := Nat.head!_digits (n := p) (by decide : 10 ≠ 1)
  have good : ∀ h : (Nat.digits 10 p).reverse ≠ [], (Nat.digits 10 p).reverse.getLast h ≠ 0 := by
    intro h
    rw [List.getLast_reverse]
    have compat (l : List ℕ) (hl : l ≠ []) : l.head hl = l.head! := by
      cases l with
      | nil => contradiction
      | cons a as => rfl
    rw [compat]
    exact head.trans_ne last
  unfold reverseDigits
  rw [Nat.digits_ofDigits 10 (by decide) _ (fun a ha =>
    Nat.digits_lt_base (by decide : 1 < 10) (List.mem_reverse.mp ha)) good, List.length_reverse]

noncomputable def nextTerm (n : ℕ) := reverseDigits (Nat.nth Nat.Prime (n-1))

lemma next_pos (n : ℕ) : 0 < nextTerm n := by
  let p := Nat.nth Nat.Prime (n-1)
  have hp : p.Prime := Nat.prime_nth_prime _
  have hd := reversed_length p hp
  change 0 < reverseDigits p
  by_contra! h
  have h0 : reverseDigits p = 0 := by omega
  have hne : (Nat.digits 10 p).length ≠ 0 := by
    simpa [Nat.digits_eq_nil_iff_eq_zero] using hp.ne_zero
  simp [h0] at hd
  omega

lemma step_increases
    (big : ∀ d : ℕ, 4 ≤ d → (10^(d+1)).primeCounting < 10^d)
    (small : ∀ p : ℕ, p.Prime → p < 10000 → score (p.primeCounting' + 1) < score (reverseDigits p))
    (n : ℕ) (hn : 0 < n) : score n < score (nextTerm n) := by
  let p := Nat.nth Nat.Prime (n-1)
  have hp : p.Prime := Nat.prime_nth_prime _
  have rank : p.primeCounting' + 1 = n := by simp [p]; omega
  change score n < score (reverseDigits p)
  by_cases hs : p < 10000
  · exact rank ▸ small p hp hs
  · apply score_lt_of_digits
    rw [reversed_length p hp]
    let d := (Nat.digits 10 p).length - 1
    have plen : (Nat.digits 10 p).length = d+1 := by
      have : (Nat.digits 10 p).length ≠ 0 := by
        simpa [Nat.digits_eq_nil_iff_eq_zero] using hp.ne_zero
      dsimp [d]
      omega
    have d4 : 4 ≤ d := by
      have hh := (Nat.lt_digits_length_iff (b := 10) (k := 4) (by decide) p).2
        (show 10^4 ≤ p by norm_num; omega)
      omega
    have ub : p < 10^(d+1) := plen ▸ Nat.lt_base_pow_length_digits (m := p) (by decide : 1 < 10)
    have rank_le : n ≤ (10^(d+1)).primeCounting := by
      rw [← rank, Nat.primeCounting, Nat.primeCounting']
      have hh := Nat.count_monotone Nat.Prime (show p+1 ≤ 10^(d+1)+1 by omega)
      simpa [Nat.count_succ (p := Nat.Prime) p, hp, Nat.primeCounting'] using hh
    have len_n := (Nat.digits_length_le_iff (b := 10) (k := d) (by decide) n).2
      (lt_of_le_of_lt rank_le (big d d4))
    omega

lemma no_loop
    (increases : ∀ n : ℕ, 0 < n → score n < score (nextTerm n)) (x : ℕ) (hx : 0 < x) :
    ¬ IsUltimatelyPeriodic (aStartAt x) := by
  have pos (n : ℕ) : 0 < aStartAt x n := by
    induction n with
    | zero => exact hx
    | succ n ih => simpa only [nextTerm, aStartAt, if_neg ih.ne'] using next_pos (aStartAt x n)
  have inc : StrictMono (fun k => score (aStartAt x k)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa only [nextTerm, aStartAt, if_neg (pos n).ne'] using increases (aStartAt x n) (pos n)
  rintro ⟨N,P,hp,hloop⟩
  have h := inc (show N < N+P by omega)
  change score (aStartAt x N) < score (aStartAt x (N+P)) at h
  rw [hloop N le_rfl] at h
  exact h.false

end OMA.ReversePrime

open OMA.ReversePrime in
theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) := by
  rintro ⟨x, hx, _, loop⟩
  exact no_loop (step_increases all_pi rank_small) x hx loop
