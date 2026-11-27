import OMAReductions.R_OeisA182126_conjecture3_R1

namespace OMA.GapCheck

/-- The first 63 primes fit below 310. Their counts certify every index. -/
def table (i : ℕ) : ℕ := ((List.range 310).filter Nat.Prime)[i]?.getD 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem table_spec : ∀ i : Fin 63, (table i).Prime ∧ Nat.count Nat.Prime (table i) = i.val := by
  decide +kernel

theorem nth_eq {i : ℕ} (h : i < 63) : Nat.nth Nat.Prime i = table i := by
  obtain ⟨hp, hc⟩ := table_spec ⟨i, h⟩
  exact (congrArg (Nat.nth Nat.Prime) hc.symm).trans (Nat.nth_count hp)

def entry (n : ℕ) : ℕ := (table (n-1) * table n) % table (n+1)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem values : ∀ i : Fin 62, 0 < i.val → (entry i).Prime →
    entry i ∈ ([2,7,11,13,29] : List ℕ) := by
  decide +kernel

end OMA.GapCheck

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn hn' hp
  have eq : OeisA182126.a n = OMA.GapCheck.entry n := by
    simp only [OeisA182126.a, if_neg (by omega : n ≠ 0), OeisA182126.prime,
      OMA.GapCheck.entry]
    rw [show n+1-1 = n by omega, show n+2-1 = n+1 by omega]
    rw [OMA.GapCheck.nth_eq (by omega : n-1 < 63), OMA.GapCheck.nth_eq (by omega : n < 63),
      OMA.GapCheck.nth_eq (by omega : n+1 < 63)]
  rw [eq] at hp ⊢
  exact OMA.GapCheck.values ⟨n, by omega⟩ hn hp
