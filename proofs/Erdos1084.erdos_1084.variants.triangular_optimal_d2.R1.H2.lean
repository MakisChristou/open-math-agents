import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

/-! Count adjacent pairs along one axial direction, then transport them to the
other two directions by lattice symmetries. The resulting unordered pairs are distinct. -/

open Finset
open scoped EuclideanGeometry

namespace OMA.HexContacts

private theorem symmetric_sum (f : ℤ → ℤ) (n : ℕ) :
    ∑ x ∈ Icc (-(n:ℤ)) n, f x = f 0 + ∑ j ∈ range n, (f ((j:ℤ)+1) + f (-(j:ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have eq : Icc (-((n+1:ℕ):ℤ)) ((n+1:ℕ):ℤ) =
        insert ((n:ℤ)+1) (insert (-(n:ℤ)-1) (Icc (-(n:ℤ)) n)) := by
      ext j
      simp only [mem_Icc,mem_insert, Nat.cast_add_one]
      omega
    rw [eq, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ]
    ring

private def interval (n : ℕ) := Icc (-(n:ℤ)) n
private def patch (n : ℕ) := ((interval n) ×ˢ (interval n)).filter (fun p => p.1+p.2 ∈ interval n)
private def starts (n : ℕ) := ((interval n) ×ˢ (interval n)).filter
  (fun p => p.1+p.2 ∈ interval n ∧ p.2+1 ∈ interval n ∧ p.1+p.2+1 ∈ interval n)
private theorem countStarts (n : ℕ) : (starts n).card = 3*n^2+n := by
  classical
  let I := Icc (-(n:ℤ)) n
  let row (x : ℤ) := I.filter (fun y => x+y ∈ I ∧ y+1 ∈ I ∧ x+y+1 ∈ I)
  have count (x : ℤ) : row x = Icc (max (-(n:ℤ)) (-n-x)) (min ((n:ℤ)-1) (n-x-1)) := by
    ext y
    simp only [row,I,mem_filter,mem_Icc,max_le_iff,le_min_iff]
    omega
  have right (x : ℤ) (hx : 0 ≤ x) (hb : x ≤ n) : ((row x).card : ℤ) = 2*n-x := by
    rw [count, max_eq_left (by omega), min_eq_right (by omega), Int.card_Icc]
    omega
  have left (x : ℤ) (hx : x ≤ 0) (hb : -(n:ℤ) ≤ x) : ((row x).card : ℤ) = 2*n+x := by
    rw [count, max_eq_right (by omega), min_eq_left (by omega), Int.card_Icc]
    omega
  have rows : ((I ×ˢ I).filter (fun p => p.1+p.2 ∈ I ∧ p.2+1 ∈ I ∧ p.1+p.2+1 ∈ I)).card = ∑ x ∈ I, (row x).card := by
    simp only [row,card_filter,sum_product]
  change ((I ×ˢ I).filter (fun p => p.1+p.2 ∈ I ∧ p.2+1 ∈ I ∧ p.1+p.2+1 ∈ I)).card = _
  apply Int.ofNat_inj.mp
  rw [rows, Nat.cast_sum]
  change ∑ x ∈ Icc (-(n:ℤ)) n, ((row x).card : ℤ) = _
  rw [symmetric_sum,right 0 (by omega) (by omega)]
  have eq : (∑ j ∈ range n, (((row ((j:ℤ)+1)).card : ℤ) + (row (-(j:ℤ)-1)).card)) =
      ∑ j ∈ range n, ((4*(n:ℤ)-2) - 2*j) := by
    apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    rw [right _ (by omega) (by omega),left _ (by omega) (by omega)]
    ring
  rw [eq, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have h : (∑ j ∈ range n, (j:ℤ))*2 = (n:ℤ)*(n-1) := by
    cases n with
    | zero => simp
    | succ n =>
      have he := congrArg (fun v : ℕ => (v:ℤ)) (Finset.sum_range_id_mul_two (n+1))
      simp only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,Nat.cast_add_one] at he
      simpa using he
  push_cast
  nlinarith

private def up (a : ℤ × ℤ) : ℤ × ℤ := (a.1,a.2+1)
private def tr (i : Fin 3) (a : ℤ × ℤ) : ℤ × ℤ :=
  if i=0 then a else if i=1 then (a.2,a.1) else (-a.2,a.1+a.2)

private noncomputable def pt (a : ℤ × ℤ) : ℝ² :=
  !₂[(a.1:ℝ)+a.2/2, Real.sqrt 3*a.2/2]

private theorem point_inj : Function.Injective pt := by
  intro a b h
  by_contra hn
  have e := OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.lattice_sep a b hn
  change 1 ≤ dist (pt a) (pt b) at e
  rw [h,dist_self] at e
  norm_num at e

private noncomputable def edge (v : Fin 3 × (ℤ × ℤ)) : Sym2 ℝ² :=
  s(pt (tr v.1 v.2), pt (tr v.1 (up v.2)))

private theorem inj : Function.Injective edge := by
  rintro ⟨i,x,y⟩ ⟨j,a,b⟩ he
  rcases Sym2.eq_iff.mp he with h|h <;>
    obtain ⟨h₁,h₂⟩ := h <;> replace h₁ := point_inj h₁ <;> replace h₂ := point_inj h₂ <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [tr,up,Prod.ext_iff] at h₁ h₂ ⊢ <;> omega

private theorem intr {n : ℕ} {a : ℤ × ℤ} (i : Fin 3) (ha : a ∈ patch n) : tr i a ∈ patch n := by
  fin_cases i <;> simp [tr,patch,interval] at ha ⊢ <;> omega

private theorem step_dist (i : Fin 3) (a : ℤ × ℤ) : dist (pt (tr i a)) (pt (tr i (up a)))=1 := by
  rw [dist_eq_norm]
  have h : ‖pt (tr i a) - pt (tr i (up a))‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change ((tr i a).1 + ((tr i a).2 : ℝ)/2 - ((tr i (up a)).1 + ((tr i (up a)).2 : ℝ)/2))^2 +
      (Real.sqrt 3*((tr i a).2 : ℝ)/2 - Real.sqrt 3*((tr i (up a)).2 : ℝ)/2)^2 = 1
    fin_cases i <;> norm_num [tr,up] <;> ring_nf <;> norm_num [Real.sq_sqrt]
  nlinarith [norm_nonneg (pt (tr i a)-pt (tr i (up a)))]

private theorem out_dist (a b : ℝ²) (h : dist a b=1) : dist (s(a,b)).out.1 (s(a,b)).out.2=1 := by
  have eq : s((s(a,b)).out.1, (s(a,b)).out.2) = s(a,b) := (s(a,b)).out_eq
  rcases Sym2.eq_iff.mp eq with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rwa [h₁,h₂]
  · rwa [h₁,h₂,dist_comm]

theorem result : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H2 := by
  classical
  intro n
  change 9*n^2+3*n ≤ unitDistNum ((patch n).image pt)
  let E := (univ : Finset (Fin 3)) ×ˢ (starts n)
  have sub : E.image edge ⊆ (((patch n).image pt).sym2.filter fun e => dist e.out.1 e.out.2=1) := by
    intro e he
    obtain ⟨⟨i,a⟩,ha,rfl⟩ := mem_image.mp he
    have hh := (mem_product.mp ha).2
    have h₁ : a ∈ patch n := by simp [starts,patch,interval] at hh ⊢; omega
    have h₂ : up a ∈ patch n := by simp [starts,patch,interval,up] at hh ⊢; omega
    refine mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨mem_image_of_mem _ (intr i h₁),mem_image_of_mem _ (intr i h₂)⟩,?_⟩
    exact out_dist _ _ (step_dist i a)
  have hc := card_le_card sub
  rw [card_image_of_injective _ inj,show E.card=3*(3*n^2+n) by simp [E,countStarts]] at hc
  exact (show 9*n^2+3*n = 3*(3*n^2+n) by ring) ▸ hc

end OMA.HexContacts

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H2 := OMA.HexContacts.result
