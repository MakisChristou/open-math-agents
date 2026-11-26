import FormalConjectures.ErdosProblems.«878»

/-! Barreto's counterexample at 210. The three pairwise coprime numbers
125, 128 and 189 give a sum of 442, above the maximum of the prime-power sum. -/

open Erdos878 Finset

namespace OMA.Barreto

def witness : Finset ℕ := {125, 128, 189}

lemma in_interval : witness ⊆ Icc 2 210 := by decide

lemma common_primes : ∀ a ∈ witness, Nat.primeFactors a ⊆ Nat.primeFactors 210 := by
  decide +kernel

lemma coprime : (witness : Set ℕ).Pairwise Nat.Coprime := by
  intro a ha b hb hab
  change a ∈ ({125, 128, 189} : Finset ℕ) at ha
  change b ∈ ({125, 128, 189} : Finset ℕ) at hb
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first | contradiction | decide

lemma lower_bound : 442 ≤ F 210 := by
  classical
  unfold F
  apply Finset.le_sup_of_le (b := witness)
  · refine mem_filter.mpr ⟨mem_powerset.mpr in_interval, in_interval, coprime, ?_⟩
    intro a ha p hp hpa
    have hpos := (mem_Icc.mp (in_interval ha)).1
    exact Nat.dvd_of_mem_primeFactors (common_primes a ha (Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩))
  · decide

end OMA.Barreto

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem OMA.solution : type_of% @Erdos878.erdos_878.parts.iii_all := by
  intro h
  have hmax : maxUpTo f 210 = 383 := by decide +kernel
  have hmem : 210 ∈ range (210 + 1) := by decide
  have hbound : F 210 ≤ maxUpTo F 210 := Finset.le_sup (f := F) hmem
  have hlower := OMA.Barreto.lower_bound
  rw [← h 210, hmax] at hbound
  omega
