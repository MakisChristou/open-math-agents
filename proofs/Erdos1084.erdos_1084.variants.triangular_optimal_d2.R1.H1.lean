import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

/-! Each axial row of the hexagon is an integer interval. Opposite rows have
equal lengths, decreasing by one at each step away from the central row. -/

open Finset

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

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H1 := by
  classical
  intro n
  let I := Icc (-(n:ℤ)) n
  let row (x : ℤ) := I.filter (fun y => x+y ∈ I)
  have count (x : ℤ) : row x = Icc (max (-(n:ℤ)) (-n-x)) (min (n:ℤ) (n-x)) := by
    ext y
    simp only [row,I,mem_filter,mem_Icc,max_le_iff,le_min_iff]
    omega
  have right (x : ℤ) (hx : 0 ≤ x) (hb : x ≤ n) : ((row x).card : ℤ) = 2*n+1-x := by
    rw [count, max_eq_left (by omega), min_eq_right (by omega), Int.card_Icc]
    omega
  have left (x : ℤ) (hx : x ≤ 0) (hb : -(n:ℤ) ≤ x) : ((row x).card : ℤ) = 2*n+1+x := by
    rw [count, max_eq_right (by omega), min_eq_left (by omega), Int.card_Icc]
    omega
  have rows : ((I ×ˢ I).filter (fun p => p.1+p.2 ∈ I)).card = ∑ x ∈ I, (row x).card := by
    simp only [row,card_filter,sum_product]
  change ((I ×ˢ I).filter (fun p => p.1+p.2 ∈ I)).card = _
  apply Int.ofNat_inj.mp
  rw [rows, Nat.cast_sum]
  change ∑ x ∈ Icc (-(n:ℤ)) n, ((row x).card : ℤ) = _
  rw [symmetric_sum,right 0 (by omega) (by omega)]
  have eq : (∑ j ∈ range n, (((row ((j:ℤ)+1)).card : ℤ) + (row (-(j:ℤ)-1)).card)) =
      ∑ j ∈ range n, (4*(n:ℤ) - 2*j) := by
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
  rw [← Finset.mul_sum]
  nlinarith
