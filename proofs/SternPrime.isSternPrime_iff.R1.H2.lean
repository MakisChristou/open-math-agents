import OMAReductions.R_SternPrime_isSternPrime_iff_R1

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples q
  simpa using hq
