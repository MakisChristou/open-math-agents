import OMAReductions.R_OeisA108129_conjecture_R1

/-! The six divisors in Riesel's covering for 509203 cover a full period of
24 exponents. Each divides the corresponding term for every exponent in
its residue class. -/

namespace OMA.Riesel

def divisor (r : ℕ) : ℕ :=
  if r % 2 = 0 then 3 else if r % 4 = 1 then 5
  else if r % 12 = 11 then 7 else if r % 12 = 7 then 13
  else if r = 15 then 17 else 241

lemma cover : ∀ r : Fin 24, let d := divisor r
    2 ≤ d ∧ d ≤ 241 ∧ 2^24 ≡ 1 [MOD d] ∧ 509203*2^r.val ≡ 1 [MOD d] := by
  decide

lemma composite (m : ℕ) : ¬(509203*2^m-1).Prime := by
  let r : Fin 24 := ⟨m%24, Nat.mod_lt _ (by decide)⟩
  let d := divisor r
  obtain ⟨hd,hsmall,period,base⟩ := cover r
  have periodic : 2^(24*(m/24)) ≡ 1 [MOD d] := by
    simpa [pow_mul,d] using period.pow (m/24)
  have ht : 509203*2^m ≡ 1 [MOD d] := calc
    509203*2^m = 509203*2^r.val*2^(24*(m/24)) := by
      rw [mul_assoc,←pow_add]
      congr 2
      dsimp [r]
      omega
    _ ≡ 1*1 [MOD d] := base.mul periodic
    _ = 1 := by decide
  have hpos : 0 < 2^m := by positivity
  apply Nat.not_prime_of_dvd_of_lt _ hd (by dsimp [d] at *; omega)
  exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ 509203*2^m)).mp ht.symm

end OMA.Riesel

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  classical
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by decide),dif_neg]
  rintro ⟨m, _, hp⟩
  exact OMA.Riesel.composite m hp
