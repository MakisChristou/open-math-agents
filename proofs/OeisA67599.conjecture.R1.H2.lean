import OMAReductions.R_OeisA67599_conjecture_R1

/-! The decimal factorization encoding of 7⁴ times a larger prime. -/

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have h7 : Nat.Prime 7 := by decide
  have hne : q ≠ 7 := by omega
  have prod : [7,7,7,7,q].prod = 2401*q := by simp; ring
  have prime (p) (h : p ∈ [7,7,7,7,q]) : Nat.Prime p := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl <;> assumption
  have sorted : [7,7,7,7,q].Pairwise (· ≤ ·) := by simp [hq.le]
  have eq := (Nat.primeFactorsList_unique prod prime).eq_of_pairwise' sorted (Nat.primeFactorsList_sorted _).pairwise
  have hcond : ¬2401*q < 2 := by omega
  simp [OeisA67599.a,hcond,←eq,List.dedup_cons_of_mem,List.dedup_cons_of_notMem,hne,Ne.symm hne,
    OeisA67599.concatenateNats]
  ring
