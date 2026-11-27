import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R1

/-! Prescribe a class which is 5 modulo 8 and 1 modulo all the specified odd
primes. Dirichlet gives an arbitrarily large prime in the class. Quadratic
reciprocity transfers the trivial square class at each odd prime. -/

open Finset

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R1.H1 := by
  intro M B
  let S := (range (M+1)).filter (fun q => Nat.Prime q ∧ Odd q)
  let P := ∏ q ∈ S, q
  have oddprod (T : Finset ℕ) (h : ∀ q ∈ T, Odd q) : Odd (∏ q ∈ T, q) := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih =>
      rw [prod_insert ha]
      exact (h a (by simp)).mul (ih (fun q hq => h q (by simp [hq])))
  have hP : Odd P := oddprod S (fun q hq => (mem_filter.mp hq).2.2)
  have hPpos : 0 < P := prod_pos (fun q hq => (mem_filter.mp hq).2.1.pos)
  let a := 1+4*P
  have ha8 : a % 8 = 5 := by obtain ⟨j,hj⟩ := hP; dsimp [a]; omega
  have ha : a.Coprime (8*P) := by
    apply Nat.Coprime.mul_right
    · rw [show 8=2^3 by decide]
      apply Nat.Coprime.pow_right
      exact Nat.coprime_two_right.mpr (by dsimp [a]; exact ⟨2*P,by omega⟩)
    · exact (Nat.coprime_add_mul_right_left 1 P 4).mpr (Nat.coprime_one_left _)
  obtain ⟨p,hpB,hp,hm⟩ := Nat.forall_exists_prime_gt_and_modEq (max B M) (by positivity : 8*P≠0) ha
  let _ : Fact p.Prime := ⟨hp⟩
  have hp8 : p%8=5 := (show p % 8 = a % 8 from hm.of_dvd (dvd_mul_right 8 P)).trans ha8
  refine ⟨p,lt_of_le_of_lt (le_max_left ..) hpB,hp,?_,?_⟩
  · rintro ⟨x,hx⟩
    have hs : IsSquare (2 : ZMod p) := ⟨x,by simpa [pow_two] using hx.symm⟩
    have := (ZMod.exists_sq_eq_two_iff (by omega : p≠2)).mp hs
    omega
  · intro q hq ho hM
    let _ : Fact q.Prime := ⟨hq⟩
    have hqS : q∈S := mem_filter.mpr ⟨mem_range.mpr (by omega),hq,ho⟩
    have dvdP : q ∣ P := Finset.dvd_prod_of_mem (fun i => i) hqS
    have e : p ≡ 1 [MOD q] := (hm.of_dvd (dvd_mul_of_dvd_right dvdP 8)).trans (by
      have := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right dvdP 4)
      simpa [a] using this.add_left 1)
    have ez : (p : ℤ) ≡ 1 [ZMOD (q:ℤ)] := by exact_mod_cast (Int.natCast_modEq_iff.mpr e)
    have hq2 : q≠2 := by obtain ⟨j,hj⟩ := ho; omega
    have pgt : q<p := hM.trans_lt ((le_max_right ..).trans_lt hpB)
    have hn : (q:ZMod p) ≠ 0 := by
      intro h
      exact (not_le_of_gt pgt) (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff q p).mp h))
    have leg : legendreSym p q=1 := by
      rw [← legendreSym.quadratic_reciprocity_one_mod_four (p:=p) (q:=q) (by omega) hq2,
        legendreSym.mod q (p:ℤ), show (p:ℤ) % (q:ℤ) = 1 % (q:ℤ) from ez,
        ← legendreSym.mod q 1,legendreSym.at_one]
    obtain ⟨x,hx⟩ := (legendreSym.eq_one_iff' p hn).mp leg
    exact ⟨x,by simpa [pow_two] using hx.symm⟩
