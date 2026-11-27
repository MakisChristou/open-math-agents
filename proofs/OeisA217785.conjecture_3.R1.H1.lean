import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Taylor

/-! Translating the polynomial by one gives an Eisenstein polynomial at n+2
whenever n+2 is prime. The coefficient of degree j is (j+1) times a binomial. -/
namespace OMA.NeighborPolynomial
open Finset Polynomial OeisA217785

lemma coeff_orig (n j : ℕ) : (polyS n).coeff j = if j≤n then (j+1:ℤ) else 0 := by
  simp only [polyS,finsetSum_coeff,coeff_C_mul_X_pow]
  simp [mem_range]

lemma size (n : ℕ) : (polyS n).natDegree=n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj; simp [coeff_orig,hj.not_ge]
  · simp [coeff_orig]; omega

lemma prim (n : ℕ) : (polyS n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro c hc
  have hh := (C_dvd_iff_dvd_coeff c _).mp hc 0
  simpa [coeff_orig] using (isUnit_of_dvd_one (show c ∣ 1 by simpa [coeff_orig] using hh))

noncomputable def shifted (n : ℕ) := Polynomial.taylor (1:ℤ) (polyS n)

lemma shifted_coeff (n j : ℕ) : (shifted n).coeff j = ((j+1:ℕ) * (n+2).choose (j+2) : ℕ) := by
  induction n with
  | zero =>
    cases j with
    | zero => norm_num [shifted,polyS,taylor_C]
    | succ j =>
      rw [Nat.choose_eq_zero_of_lt (by omega : 2<j+1+2)]
      simp [shifted,polyS,coeff_one]
  | succ n ih =>
    have he : polyS (n+1) = polyS n + C (↑(n+1:ℕ)+1 : ℤ)*X^(n+1) := by
      unfold polyS; rw [sum_range_succ]
    rw [shifted,he,map_add,taylor_mul,taylor_C,taylor_X_pow,coeff_add,coeff_C_mul,C_1,coeff_X_add_one_pow]
    change (shifted n).coeff j + _ = _
    rw [ih]
    have hx := Nat.add_one_mul_choose_eq (n+1) j
    have add := Nat.choose_succ_succ (n+2) (j+1)
    change (n+2+1).choose (j+2) = _ at add
    rw [show n+1+2=n+2+1 by omega,add]
    zify at hx ⊢
    linear_combination hx

lemma prim_shifted (n : ℕ) : (shifted n).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  rintro c ⟨f,hf⟩
  have he := congrArg (fun g : ℤ[X] => g.eval (-1)) hf
  have hz : (shifted n).eval (-1) = 1 := by
    rw [shifted,taylor_eval]; norm_num only [neg_add_cancel]; rw [← coeff_zero_eq_eval_zero]; simp [coeff_orig]
  rw [hz,eval_mul,eval_C] at he
  exact isUnit_of_dvd_one ⟨_,he⟩

lemma prime_square_not_dvd (p : ℕ) (hp : p.Prime) (h : 2<p) : ¬ p^2 ∣ p.choose 2 := by
  intro hd
  have h₀ := Nat.add_one_mul_choose_eq (p-1) 1
  rw [show p-1+1=p by omega,Nat.choose_one_right] at h₀
  change p*(p-1)=p.choose 2*2 at h₀
  have hh : p^2 ∣ p*(p-1) := h₀ ▸ dvd_mul_of_dvd_left hd 2
  rw [pow_two] at hh
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) (Nat.dvd_of_mul_dvd_mul_left hp.pos hh)

lemma shifted_irred (n : ℕ) (hn : 1≤n) (hp : (n+2).Prime) : Irreducible (shifted n) := by
  let p := n+2
  let J := Ideal.span ({(p:ℤ)} : Set ℤ)
  have hprime : J.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  have sd : (shifted n).natDegree=n := by simp [shifted,natDegree_taylor,size]
  apply irreducible_of_eisenstein_criterion (P:=J) hprime
  · rw [leadingCoeff,sd,shifted_coeff,Nat.choose_self,mul_one,Ideal.mem_span_singleton]
    exact_mod_cast Nat.not_dvd_of_pos_of_lt (by omega : 0 < n+1) (by dsimp [p]; omega : n+1 < p)
  · intro k hk
    have hs : k<n := by simpa [sd] using (coe_lt_degree.mp hk)
    rw [shifted_coeff,Ideal.mem_span_singleton]
    exact_mod_cast dvd_mul_of_dvd_right (hp.dvd_choose (a:=k+2) (b:=n+2) (by omega) (by omega) le_rfl) (k+1)
  · apply natDegree_pos_iff_degree_pos.mp
    omega
  · rw [shifted_coeff,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    simpa [p] using (show ¬ ((n+2:ℕ):ℤ)^2 ∣ ((n+2).choose 2:ℤ) by
      exact_mod_cast prime_square_not_dvd (n+2) hp (by omega))
  · exact prim_shifted n

end OMA.NeighborPolynomial

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (OMA.NeighborPolynomial.prim n)).mp
  exact (MulEquiv.irreducible_iff (Polynomial.taylorEquiv (1:ℤ))).mp
    (OMA.NeighborPolynomial.shifted_irred n hn hp)
