import OMAReductions.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    rw [OMA.R_OeisA135508_conjecture_R1.x_succ_fact n (by omega)]
    exact dvd_mul_of_dvd_left ih _
