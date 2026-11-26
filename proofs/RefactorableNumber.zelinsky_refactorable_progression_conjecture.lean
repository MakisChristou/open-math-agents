import FormalConjectures.Wikipedia.RefactorableNumber
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! For a refactorable number n, adjoin the prime power p^(p-1), choosing
p larger than n and congruent to 1 modulo the progression modulus.
The new prime power has exactly p divisors and is itself divisible by p. -/

theorem OMA.solution : type_of% @RefactorableNumber.zelinsky_refactorable_progression_conjecture := by
  intro m n hm hn
  obtain ⟨p, hp, hnp, hmod⟩ := Nat.exists_prime_gt_modEq_one n (by omega : m ≠ 0)
  have hpos := hn.pos
  have htwo := hp.two_le
  have hexp : p - 1 ≠ 0 := by omega
  have hcop : n.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun h => hnp.not_ge (Nat.le_of_dvd hpos h))).symm
  refine ⟨n * p ^ (p - 1), ?_, ⟨?_, ?_⟩, ?_⟩
  · simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow' hp.one_lt hexp) hpos
  · exact Nat.mul_pos hpos (pow_pos hp.pos _)
  · rw [Nat.Coprime.card_divisors_mul (hcop.pow_right _), Nat.divisors_prime_pow hp,
      Finset.card_map, Finset.card_range, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact Nat.mul_dvd_mul hn.2 (dvd_pow_self p hexp)
  · simpa using (Nat.ModEq.refl n).mul (hmod.pow (p - 1))
