import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1
import Mathlib.FieldTheory.Finite.Basic

/-! The block power sum in a prime field gives both necessary
divisibilities for a counterexample to Giuga's primality criterion. -/

namespace OMA.GiugaBounds
open AgohGiuga Finset
noncomputable section

lemma blocks (p d k : ℕ) :
    (∑ i ∈ range (d*p), (i:ZMod p)^k) = (d:ZMod p) * ∑ i ∈ range p, (i:ZMod p)^k := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    push_cast
    simp [add_mul]

lemma field_sum {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (∑ i ∈ range p, (i:ZMod p)^k) = if p-1 ∣ k then -1 else 0 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hf : (∑ i ∈ range p, (i:ZMod p)^k) = ∑ x : ZMod p, x^k := by
    rw [← Fin.sum_univ_eq_sum_range]
    have h (x : Fin p) : (x.val : ZMod p) = ZMod.finEquiv p x := by
      cases p with
      | zero => exact (Nat.not_prime_zero hp).elim
      | succ p => exact ZMod.natCast_zmod_val (n := p+1) x
    simp only [h]
    exact (ZMod.finEquiv p).toEquiv.sum_comp (fun x => x^k)
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨Units.val,Units.val_injective⟩
  have himg : univ.map emb = univ \ {(0:ZMod p)} := by
    ext x
    simp only [mem_map,mem_univ,true_and,mem_sdiff,mem_singleton,emb,Function.Embedding.coeFn_mk]
    exact isUnit_iff_ne_zero
  calc
    _ = ∑ x : ZMod p, x^k := hf
    _ = ∑ x ∈ univ \ {(0:ZMod p)}, x^k := by
      rw [← sum_sdiff ({0}:Finset (ZMod p)).subset_univ (f := fun x => x^k)]
      simp [hk]
    _ = ∑ x : (ZMod p)ˣ, (x:ZMod p)^k := by rw [← himg, sum_map]; rfl
    _ = _ := by simpa using FiniteField.sum_pow_units (ZMod p) k

lemma local_conditions {n : ℕ} (hh : IsStrongGiuga n) {p : ℕ} (hp : p.Prime) (hd : p ∣ n) :
    (p-1 ∣ n-1) ∧ (p ∣ n/p-1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hn : 1 < n := hh.1.1
  have hk : n-1 ≠ 0 := by omega
  have he : (Ioo 0 n) = (range n).erase 0 := by ext i; simp; omega
  have hs : (∑ i ∈ Ioo 0 n, i^(n-1)) = ∑ i ∈ range n, i^(n-1) := by
    rw [he]
    have hz := add_sum_erase (range n) (fun i => i^(n-1)) (mem_range.mpr (by omega : 0<n))
    simpa [zero_pow hk] using hz
  have hsum := hd.trans hh.2
  rw [hs,← ZMod.natCast_eq_zero_iff, Nat.cast_add,Nat.cast_one,Nat.cast_sum] at hsum
  push_cast at hsum
  have hblock := blocks p (n/p) (n-1)
  rw [Nat.div_mul_cancel hd,field_sum hp hk] at hblock
  rw [hblock] at hsum
  split_ifs at hsum with hc
  · refine ⟨hc,?_⟩
    have hpos : 1 ≤ n/p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    rw [← ZMod.natCast_eq_zero_iff,Nat.cast_sub hpos,Nat.cast_one]
    linear_combination -hsum
  · simp at hsum

lemma squarefree {n : ℕ} (h : IsStrongGiuga n) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hp0 := hp.pos
  obtain ⟨k,hk⟩ := hd
  have hd' : p ∣ n := ⟨p*k,by rw [hk];ring⟩
  have hq := (local_conditions h hp hd').2
  have hdiv : n/p = p*k := by rw [hk,mul_assoc,Nat.mul_div_cancel_left _ hp0]
  rw [hdiv] at hq
  have hn : 1<n := h.1.1
  have hpos : 1 ≤ p*k := by rw [← hdiv]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hd') hp0
  have heq : 1 + (p*k-1) = p*k := by omega
  have h01 : p ∣ 1 := (Nat.dvd_add_left hq).mp (heq.symm ▸ dvd_mul_right p k)
  exact hp.not_dvd_one h01

lemma carmichael {n : ℕ} (h : IsStrongGiuga n) : IsCarmichael n := by
  exact (korselts_criterion n h.1).mpr ⟨squarefree h,fun _ hp hd => (local_conditions h hp hd).1⟩

end
end OMA.GiugaBounds

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  exact fun _ h => OMA.GiugaBounds.carmichael h
