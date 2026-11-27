import FormalConjectures.OEIS.«108864»
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! The odd number 815634435 has ordinary deficiency six, as recorded in
OEIS A141548. Its proper divisors have sum 815634429, so the greedy
algorithm accepts every one of them and leaves the same remainder. -/

namespace OMA.OddDeficiency
open Finset OeisA108864

def pref (n k : ℕ) := ∑ d ∈ range k, if d∣n then d else 0

lemma foldPrefix (n k m : ℕ) (h : pref n k ≤ m) :
    (List.range k).foldl (fun r d => if d∣n ∧ d≤r then r-d else r) m=m-pref n k := by
  induction k with
  | zero => simp [pref]
  | succ k ih =>
    have hs : pref n (k+1)=pref n k+(if k∣n then k else 0) := by simp [pref,sum_range_succ]
    rw [hs] at h ⊢
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih (by omega)]
    by_cases hd : k∣n
    · simp only [hd,if_true] at h ⊢
      have hle : k ≤ m - pref n k := by omega
      simp [hle]; omega
    · simp [hd]

lemma pref_self (n : ℕ) : pref n n=∑ d∈n.properDivisors,d := by
  unfold pref
  rw [←sum_filter]
  have he : ((range n).filter fun d => d∣n)=n.properDivisors := by
    ext d
    simp only [mem_filter,mem_range,Nat.mem_properDivisors,and_comm]
  rw [he]

lemma deficiency_eq {n s : ℕ} (hs : (∑ d∈n.properDivisors,d)=s) (hle : s≤n) (hpos : 0<s) :
    perfectDeficiency n=n-s := by
  rw [perfectDeficiency,List.range_succ,List.foldl_append]
  have he := (pref_self n).trans hs
  rw [foldPrefix n n n (by omega),he]
  simp [show ¬n≤n-s by omega]

lemma witness_sum : (∑ d∈(815634435:ℕ).divisors,d)=1631268864 := by
  have factor : (815634435:ℕ) = 3*5*7*11*547*1291 := by decide
  rw [factor]
  repeat rw [Nat.Coprime.sum_divisors_mul (by decide)]
  rw [(by norm_num : Nat.Prime 3).divisors,(by norm_num : Nat.Prime 5).divisors,
    (by norm_num : Nat.Prime 7).divisors,(by norm_num : Nat.Prime 11).divisors,
    (by norm_num : Nat.Prime 547).divisors,(by norm_num : Nat.Prime 1291).divisors]
  decide

lemma witness : A 815634435 := by
  refine ⟨by decide,?_⟩
  have hs := witness_sum
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hs
  have hproper : (∑ d∈(815634435:ℕ).properDivisors,d)=815634429 := Nat.eq_sub_of_add_eq hs
  rw [deficiency_eq hproper (by decide +kernel) (by decide +kernel)]
  decide

def early : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,21,22,24,26,28,30,32,40,42,
  44,50,52,60,64,68,72,110,120,126,128,130,136,144,150,152,180,184,204,228,256,315,462,496,
  512,528,592,656,750,884,1012,1024,1155]

set_option maxRecDepth 100000 in
lemma earlyValid : early.all (fun k => decide (k<815634435 ∧ A k)) = true := by decide +kernel

lemma countLower : 59 ≤ Nat.count A 815634435 := by
  rw [Nat.count_eq_card_filter_range]
  have inc : early.toFinset ⊆ (range 815634435).filter A := by
    intro k hk
    have h := of_decide_eq_true (List.all_eq_true.mp earlyValid k (List.mem_toFinset.mp hk))
    exact mem_filter.mpr ⟨mem_range.mpr h.1,h.2⟩
  exact (show 59=early.toFinset.card by decide).le.trans (card_le_card inc)

end OMA.OddDeficiency

theorem OMA.disproof : ¬ (type_of% @OeisA108864.conjecture) := by
  intro h
  have hh := h (Nat.count OeisA108864.A 815634435) OMA.OddDeficiency.countLower
  unfold OeisA108864.a at hh
  rw [Nat.nth_count OMA.OddDeficiency.witness] at hh
  exact (by decide +kernel : ¬Even (815634435:ℕ)) hh
