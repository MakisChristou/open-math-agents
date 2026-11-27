import OMAReductions.R_Erdos384_erdos_384_R1

/-! For n > k² choose an even factor from each consecutive pair in the
descending factorial. Each chosen factor exceeds the product of the corresponding
two factors in k!. A prime divisor of an even factor is at most half of n. -/

namespace OMA.EcklundLarge

lemma even_coprime {n k e : ℕ} (large : 4≤n) (he : Even e) (ep : 0<e) (en : e≤n)
    (no : ∀ p : ℕ, p.Prime → p ∣ n.choose k → ¬2*p≤n) : e.Coprime (n.choose k) := by
  by_contra h
  obtain ⟨p,hp,hd,hc⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  obtain ⟨v,hv⟩ := he
  have hd' : p ∣ 2*v := by simpa [two_mul,← hv] using hd
  rcases hp.dvd_mul.mp hd' with htwo|hrest
  · have hle := Nat.le_of_dvd (by decide : 0<2) htwo
    exact no p hp hc (by omega)
  · have hle := Nat.le_of_dvd (show 0<v by omega) hrest
    exact no p hp hc (by omega)

lemma even_product {n k : ℕ} (hk : 4≤k) (hn : k*k<n)
    (no : ∀ p : ℕ, p.Prime → p ∣ n.choose k → ¬2*p≤n) (j : ℕ) (hj : j≤k) :
    ∃ A : ℕ, A ∣ n.descFactorial j ∧ A.Coprime (n.choose k) ∧
      j.factorial ≤ A ∧ (2≤j → j.factorial < A) := by
  induction j using Nat.twoStepInduction with
  | zero => exact ⟨1,one_dvd _,by simp,by decide,by omega⟩
  | one => exact ⟨1,one_dvd _,by simp,by decide,by omega⟩
  | more j ih _ =>
    obtain ⟨A,hA,hC,hL,_⟩ := ih (by omega)
    have hbound : (j+2)*(j+1)<n-(j+1) := by
      have sq : (j+2)*(j+2) ≤ k*k := Nat.mul_le_mul hj hj
      have expand : (j+2)*(j+2) = (j+2)*(j+1)+(j+2) := by ring
      omega
    have hpair : ∃ e : ℕ, (e=n-(j+1) ∨ e=n-j) ∧ Even e := by
      by_cases h : (n-j)%2=0
      · exact ⟨n-j,Or.inr rfl,Nat.even_iff.mpr h⟩
      · exact ⟨n-(j+1),Or.inl rfl,Nat.even_iff.mpr (by omega)⟩
    obtain ⟨e,he,hev⟩ := hpair
    have hlt : (j+2)*(j+1)<e := by rcases he with h|h <;> omega
    have hen : e≤n := by rcases he with h|h <;> omega
    have hed : e ∣ (n-(j+1))*(n-j) := by
      rcases he with rfl|rfl
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    have hc := even_coprime (n:=n) (k:=k) (by nlinarith) hev (by omega) hen no
    have hprod : (j+2).factorial < e*A := calc
      (j+2).factorial = ((j+2)*(j+1))*j.factorial := by rw [Nat.factorial_succ,Nat.factorial_succ,mul_assoc]
      _ < e * j.factorial := Nat.mul_lt_mul_of_pos_right hlt j.factorial_pos
      _ ≤ e*A := Nat.mul_le_mul_left _ hL
    refine ⟨e*A,?_,hc.mul_left hC,hprod.le,fun _ => hprod⟩
    rw [Nat.descFactorial_succ,Nat.descFactorial_succ,← mul_assoc]
    exact Nat.mul_dvd_mul hed hA

end OMA.EcklundLarge

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H1 := by
  intro n k hk hn
  by_contra! no
  obtain ⟨A,hdiv,hcop,_,hgt⟩ := OMA.EcklundLarge.even_product hk hn (by
    intro p hp hd hle
    exact (not_lt_of_ge hle) (no p hp hd)) k le_rfl
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdiv
  have hf := hcop.dvd_of_dvd_mul_right hdiv
  exact (not_lt_of_ge (Nat.le_of_dvd k.factorial_pos hf)) (hgt (by omega))
