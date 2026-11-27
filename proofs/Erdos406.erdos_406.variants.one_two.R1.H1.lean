import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

/-! It suffices to look at the 26 least significant ternary digits. Stop the
search when the expansion ends so that leading zeroes cannot be witnesses. -/

private def zeroDigit : ℕ → ℕ → Bool
  | 0, _ => false
  | j+1, n => n != 0 && (n % 3 == 0 || zeroDigit j (n/3))

private theorem zeroDigit_sound (j n : ℕ) (h : zeroDigit j n=true) :
    0 ∈ Nat.digits 3 n := by
  induction j generalizing n with
  | zero => simp [zeroDigit] at h
  | succ j ih =>
    simp only [zeroDigit, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq] at h
    rw [Nat.digits_def' (by decide : 1<3) (Nat.pos_of_ne_zero h.1)]
    rcases h.2 with h | h
    · simp [h]
    · exact List.mem_cons_of_mem _ (ih _ h)

set_option maxRecDepth 4096 in
private theorem checked : ∀ i : Fin 985, zeroDigit 26 (2^(i.val+16))=true := by decide +kernel

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  intro k hk hmax hall
  let i : Fin 985 := ⟨k-16,by omega⟩
  have he : i.val+16=k := by dsimp [i]; omega
  have hz := zeroDigit_sound _ _ (checked i)
  rw [he] at hz
  simpa using hall hz
