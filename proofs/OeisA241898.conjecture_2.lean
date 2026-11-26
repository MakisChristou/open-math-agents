import FormalConjectures.OEIS.«241898»
import Mathlib.NumberTheory.SumFourSquares

/-! Start with a four-square representation. If one coordinate is 7, permute it
to the first position and change signs of the other three to give residues
0, 1, 2, or 3 modulo 7. Up to permutation there are twenty residue classes.

For each class, reflect the vector orthogonally to a short integer vector
of squared length 7 or 14. Its dot product with the input is a multiple of 7,
so the reflected coordinates are integral. The displayed affine linear forms
are these reflected coordinates after writing the other entries as 7i+r.
Their squared norms are checked as polynomial identities. If every reflection
has a coordinate equal to 7 or -7, the corresponding linear equations are
inconsistent, except for two inputs which admit direct representations. -/

namespace OMA.AvoidSeven

def forbidden (a b c d : ℤ) : Prop :=
  a = 7 ∨ a = -7 ∨ b = 7 ∨ b = -7 ∨ c = 7 ∨ c = -7 ∨ d = 7 ∨ d = -7

def represent (n : ℤ) : Prop :=
  ∃ a b c d : ℤ, ¬ forbidden a b c d ∧ a^2 + b^2 + c^2 + d^2 = n

lemma forced {n : ℤ} (bad : ¬ represent n) (a b c d : ℤ)
    (hn : a^2 + b^2 + c^2 + d^2 = n) : forbidden a b c d := by
  by_contra h
  exact bad ⟨a,b,c,d,h,hn⟩

set_option maxHeartbeats 4000000 in
lemma residue000 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+0)^2 + (7*k+0)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i + 2*j) (3 - 2*i - 6*j) (2 - 6*i + 3*j) (7*k) (by ring)
  have h1 := forced bad
    (6 + 3*i + 2*k) (3 - 2*i - 6*k) (7*j) (2 - 6*i + 3*k) (by ring)
  have h2 := forced bad
    (5 + 2*i + 4*j + 2*k) (2 + 5*i - 4*j - 2*k) (4 - 4*i - j - 4*k) (2 - 2*i - 4*j + 5*k) (by ring)
  have h3 := forced bad
    (5 + 4*i + 2*j + 2*k) (4 - i - 4*j - 4*k) (2 - 4*i + 5*j - 2*k) (2 - 4*i - 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue001 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+0)^2 + (7*k+1)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i + 2*j) (3 - 2*i - 6*j) (2 - 6*i + 3*j) (1 + 7*k) (by ring)
  have h1 := forced bad
    (6 - 3*i - 2*j) (-3 - 2*i - 6*j) (-2 - 6*i + 3*j) (1 + 7*k) (by ring)
  unfold forbidden at h0 h1
  omega

set_option maxHeartbeats 4000000 in
lemma residue002 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+0)^2 + (7*k+2)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i + 2*j) (3 - 2*i - 6*j) (2 - 6*i + 3*j) (2 + 7*k) (by ring)
  have h1 := forced bad
    (6 - 3*i - 2*j) (-3 - 2*i - 6*j) (-2 - 6*i + 3*j) (2 + 7*k) (by ring)
  unfold forbidden at h0 h1
  omega

set_option maxHeartbeats 4000000 in
lemma residue003 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+0)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i + 2*j) (3 - 2*i - 6*j) (2 - 6*i + 3*j) (3 + 7*k) (by ring)
  have h1 := forced bad
    (6 - 3*i - 2*j) (-3 - 2*i - 6*j) (-2 - 6*i + 3*j) (3 + 7*k) (by ring)
  unfold forbidden at h0 h1
  omega

set_option maxHeartbeats 4000000 in
lemma residue011 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+1)^2 + (7*k+1)^2) := by
  by_contra bad
  have h0 := forced bad
    (-1 + 4*i + 4*j - 4*k) (4 + 5*i - 2*j + 2*k) (5 - 2*i + 5*j + 2*k) (-3 + 2*i + 2*j + 5*k) (by ring)
  have h1 := forced bad
    (-1 - 4*i - 4*j + 4*k) (-4 + 5*i - 2*j + 2*k) (-3 - 2*i + 5*j + 2*k) (5 + 2*i + 2*j + 5*k) (by ring)
  have h2 := forced bad
    (-1 + 4*i - 4*j + 4*k) (4 + 5*i + 2*j - 2*k) (-3 + 2*i + 5*j + 2*k) (5 - 2*i + 2*j + 5*k) (by ring)
  have h3 := forced bad
    (5 + 4*i + 2*j - 2*k) (4 - i - 4*j + 4*k) (3 - 4*i + 5*j + 2*k) (-1 + 4*i + 2*j + 5*k) (by ring)
  have h4 := forced bad
    (5 - 4*i - 2*j + 2*k) (-4 - i - 4*j + 4*k) (-1 - 4*i + 5*j + 2*k) (3 + 4*i + 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega

set_option maxHeartbeats 4000000 in
lemma residue012 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+1)^2 + (7*k+2)^2) := by
  by_contra bad
  have exception0 : ¬ (i = 0 ∧ j = 0 ∧ k = -1) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact bad ⟨5, 5, 5, 0, by norm_num [forbidden], by decide⟩
  have exception1 : ¬ (i = 0 ∧ j = -2 ∧ k = 2) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact bad ⟨21, 4, 4, 1, by norm_num [forbidden], by decide⟩
  have h0 := forced bad
    (7 + 3*j + 2*k) (7*i) (1 - 2*j - 6*k) (2 - 6*j + 3*k) (by ring)
  have h1 := forced bad
    (5 + 2*i + 4*j - 2*k) (2 + 5*i - 4*j + 2*k) (5 - 4*i - j + 4*k) (2*i + 4*j + 5*k) (by ring)
  have h2 := forced bad
    (5 - 2*i - 4*j + 2*k) (-2 + 5*i - 4*j + 2*k) (-3 - 4*i - j + 4*k) (4 + 2*i + 4*j + 5*k) (by ring)
  have h3 := forced bad
    (5 - 2*i + 4*j - 2*k) (-2 + 5*i + 4*j - 2*k) (5 + 4*i - j + 4*k) (-2*i + 4*j + 5*k) (by ring)
  have h4 := forced bad
    (5 + 2*i - 4*j + 2*k) (2 + 5*i + 4*j - 2*k) (-3 + 4*i - j + 4*k) (4 - 2*i + 4*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega

set_option maxHeartbeats 4000000 in
lemma residue013 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+1)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 2*j - 3*k) (7*i) (5 + 3*j + 6*k) (-3 + 6*j - 2*k) (by ring)
  have h1 := forced bad
    (7 + 2*i + 2*j + 4*k) (5*i - 2*j - 4*k) (1 - 2*i + 5*j - 4*k) (3 - 4*i - 4*j - k) (by ring)
  have h2 := forced bad
    (3 - 2*i - 2*j - 4*k) (-4 + 5*i - 2*j - 4*k) (-3 - 2*i + 5*j - 4*k) (-5 - 4*i - 4*j - k) (by ring)
  have h3 := forced bad
    (7 - 2*j + 3*k) (7*i) (1 + 3*j + 6*k) (3 + 6*j - 2*k) (by ring)
  have h4 := forced bad
    (3 + 2*i - 2*j - 4*k) (4 + 5*i + 2*j + 4*k) (-3 + 2*i + 5*j - 4*k) (-5 + 4*i - 4*j - k) (by ring)
  have h5 := forced bad
    (7 - 2*i + 2*j + 4*k) (5*i + 2*j + 4*k) (1 + 2*i + 5*j - 4*k) (3 + 4*i - 4*j - k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4 h5
  omega

set_option maxHeartbeats 4000000 in
lemma residue022 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+2)^2 + (7*k+2)^2) := by
  by_contra bad
  have h0 := forced bad
    (-1 + 4*i + 4*j - 4*k) (4 + 5*i - 2*j + 2*k) (6 - 2*i + 5*j + 2*k) (-2 + 2*i + 2*j + 5*k) (by ring)
  have h1 := forced bad
    (-1 - 4*i - 4*j + 4*k) (-4 + 5*i - 2*j + 2*k) (-2 - 2*i + 5*j + 2*k) (6 + 2*i + 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1
  omega

set_option maxHeartbeats 4000000 in
lemma residue023 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+2)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*j - 2*k) (7*i) (5 - 2*j + 6*k) (1 + 6*j + 3*k) (by ring)
  have h1 := forced bad
    (7 + 2*i + 4*j + 2*k) (5*i - 4*j - 2*k) (2 - 4*i - j - 4*k) (3 - 2*i - 4*j + 5*k) (by ring)
  have h2 := forced bad
    (7 - 2*i + 4*j + 2*k) (5*i + 4*j + 2*k) (2 + 4*i - j - 4*k) (3 + 2*i - 4*j + 5*k) (by ring)
  have h3 := forced bad
    (3 + 2*i - 4*j - 2*k) (4 + 5*i + 4*j + 2*k) (-6 + 4*i - j - 4*k) (-1 + 2*i - 4*j + 5*k) (by ring)
  have h4 := forced bad
    (3 - 2*i - 4*j - 2*k) (-4 + 5*i - 4*j - 2*k) (-6 - 4*i - j - 4*k) (-1 - 2*i - 4*j + 5*k) (by ring)
  have h5 := forced bad
    (6 - 3*j + 2*k) (7*i) (-1 - 2*j + 6*k) (5 + 6*j + 3*k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4 h5
  omega

set_option maxHeartbeats 4000000 in
lemma residue033 (i j k : ℤ) :
    represent (7^2 + (7*i+0)^2 + (7*j+3)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (-1 + 4*i + 4*j - 4*k) (4 + 5*i - 2*j + 2*k) (7 - 2*i + 5*j + 2*k) (-1 + 2*i + 2*j + 5*k) (by ring)
  have h1 := forced bad
    (-1 - 4*i - 4*j + 4*k) (-4 + 5*i - 2*j + 2*k) (-1 - 2*i + 5*j + 2*k) (7 + 2*i + 2*j + 5*k) (by ring)
  have h2 := forced bad
    (5 + 4*i + 2*j - 2*k) (4 - i - 4*j + 4*k) (5 - 4*i + 5*j + 2*k) (1 + 4*i + 2*j + 5*k) (by ring)
  have h3 := forced bad
    (5 + 4*i - 2*j + 2*k) (4 - i + 4*j - 4*k) (1 + 4*i + 5*j + 2*k) (5 - 4*i + 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue111 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+1)^2 + (7*k+1)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 4*i - 2*j - 2*k) (5 - i + 4*j + 4*k) (-1 + 4*i + 5*j - 2*k) (-1 + 4*i - 2*j + 5*k) (by ring)
  have h1 := forced bad
    (5 - 4*i + 2*j + 2*k) (-3 - i + 4*j + 4*k) (3 + 4*i + 5*j - 2*k) (3 + 4*i - 2*j + 5*k) (by ring)
  have h2 := forced bad
    (5 - 2*i + 4*j - 2*k) (-1 + 5*i + 4*j - 2*k) (5 + 4*i - j + 4*k) (-1 - 2*i + 4*j + 5*k) (by ring)
  have h3 := forced bad
    (5 - 2*i - 2*j + 4*k) (-1 + 5*i - 2*j + 4*k) (-1 - 2*i + 5*j + 4*k) (5 + 4*i + 4*j - k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue112 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+1)^2 + (7*k+2)^2) := by
  by_contra bad
  have h0 := forced bad
    (7 + 3*i + 2*k) (1 - 2*i - 6*k) (1 + 7*j) (2 - 6*i + 3*k) (by ring)
  have h1 := forced bad
    (5 - 3*i - 2*k) (-5 - 2*i - 6*k) (1 + 7*j) (-2 - 6*i + 3*k) (by ring)
  have h2 := forced bad
    (7 + 3*j + 2*k) (1 + 7*i) (1 - 2*j - 6*k) (2 - 6*j + 3*k) (by ring)
  have h3 := forced bad
    (-1 - 4*i - 4*j + 4*k) (-3 + 5*i - 2*j + 2*k) (-3 - 2*i + 5*j + 2*k) (6 + 2*i + 2*j + 5*k) (by ring)
  have h4 := forced bad
    (5 - 3*j - 2*k) (1 + 7*i) (-5 - 2*j - 6*k) (-2 - 6*j + 3*k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega

set_option maxHeartbeats 4000000 in
lemma residue113 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+1)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 2*i - 3*k) (5 + 3*i + 6*k) (1 + 7*j) (-3 + 6*i - 2*k) (by ring)
  have h1 := forced bad
    (7 - 2*i + 3*k) (1 + 3*i + 6*k) (1 + 7*j) (3 + 6*i - 2*k) (by ring)
  have h2 := forced bad
    (5 + 2*j - 3*k) (1 + 7*i) (5 + 3*j + 6*k) (-3 + 6*j - 2*k) (by ring)
  have h3 := forced bad
    (5 - 2*i - 4*j + 2*k) (-1 + 5*i - 4*j + 2*k) (-3 - 4*i - j + 4*k) (5 + 2*i + 4*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue122 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+2)^2 + (7*k+2)^2) := by
  by_contra bad
  have h0 := forced bad
    (7 + 3*i + 2*j) (1 - 2*i - 6*j) (2 - 6*i + 3*j) (2 + 7*k) (by ring)
  have h1 := forced bad
    (5 - 3*i - 2*j) (-5 - 2*i - 6*j) (-2 - 6*i + 3*j) (2 + 7*k) (by ring)
  have h2 := forced bad
    (7 + 3*i + 2*k) (1 - 2*i - 6*k) (2 + 7*j) (2 - 6*i + 3*k) (by ring)
  have h3 := forced bad
    (7 + 2*i + 4*j + 2*k) (1 + 5*i - 4*j - 2*k) (2 - 4*i - j - 4*k) (2 - 2*i - 4*j + 5*k) (by ring)
  have h4 := forced bad
    (3 - 2*i - 2*j - 4*k) (-3 + 5*i - 2*j - 4*k) (-2 - 2*i + 5*j - 4*k) (-6 - 4*i - 4*j - k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega

set_option maxHeartbeats 4000000 in
lemma residue123 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+2)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (7 + 3*i + 2*j) (1 - 2*i - 6*j) (2 - 6*i + 3*j) (3 + 7*k) (by ring)
  have h1 := forced bad
    (5 - 3*i - 2*j) (-5 - 2*i - 6*j) (-2 - 6*i + 3*j) (3 + 7*k) (by ring)
  have h2 := forced bad
    (6 + 3*j - 2*k) (1 + 7*i) (5 - 2*j + 6*k) (1 + 6*j + 3*k) (by ring)
  have h3 := forced bad
    (7 + 4*i + 2*j + 2*k) (1 - i - 4*j - 4*k) (2 - 4*i + 5*j - 2*k) (3 - 4*i - 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue133 (i j k : ℤ) :
    represent (7^2 + (7*i+1)^2 + (7*j+3)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 2*i - 3*k) (5 + 3*i + 6*k) (3 + 7*j) (-3 + 6*i - 2*k) (by ring)
  have h1 := forced bad
    (7 - 2*i + 3*k) (1 + 3*i + 6*k) (3 + 7*j) (3 + 6*i - 2*k) (by ring)
  have h2 := forced bad
    (5 + 2*i - 3*j) (5 + 3*i + 6*j) (-3 + 6*i - 2*j) (3 + 7*k) (by ring)
  have h3 := forced bad
    (3 + 4*i + 4*j + 4*k) (3 + 5*i - 2*j - 2*k) (5 - 2*i + 5*j - 2*k) (5 - 2*i - 2*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue222 (i j k : ℤ) :
    represent (7^2 + (7*i+2)^2 + (7*j+2)^2 + (7*k+2)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 4*i - 2*j - 2*k) (6 - i + 4*j + 4*k) (4*i + 5*j - 2*k) (4*i - 2*j + 5*k) (by ring)
  have h1 := forced bad
    (5 - 4*i + 2*j + 2*k) (-2 - i + 4*j + 4*k) (4 + 4*i + 5*j - 2*k) (4 + 4*i - 2*j + 5*k) (by ring)
  have h2 := forced bad
    (5 + 2*i + 2*j - 4*k) (4 + 5*i - 2*j + 4*k) (4 - 2*i + 5*j + 4*k) (-2 + 4*i + 4*j - k) (by ring)
  have h3 := forced bad
    (5 + 2*i - 4*j + 2*k) (4 + 5*i + 4*j - 2*k) (-2 + 4*i - j + 4*k) (4 - 2*i + 4*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue223 (i j k : ℤ) :
    represent (7^2 + (7*i+2)^2 + (7*j+2)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i - 2*k) (5 - 2*i + 6*k) (2 + 7*j) (1 + 6*i + 3*k) (by ring)
  have h1 := forced bad
    (6 - 3*i + 2*k) (-1 - 2*i + 6*k) (2 + 7*j) (5 + 6*i + 3*k) (by ring)
  have h2 := forced bad
    (6 + 3*j - 2*k) (2 + 7*i) (5 - 2*j + 6*k) (1 + 6*j + 3*k) (by ring)
  have h3 := forced bad
    (3 + 4*i + 4*j + 4*k) (4 + 5*i - 2*j - 2*k) (4 - 2*i + 5*j - 2*k) (5 - 2*i - 2*j + 5*k) (by ring)
  have h4 := forced bad
    (6 - 3*j + 2*k) (2 + 7*i) (-1 - 2*j + 6*k) (5 + 6*j + 3*k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega

set_option maxHeartbeats 4000000 in
lemma residue233 (i j k : ℤ) :
    represent (7^2 + (7*i+2)^2 + (7*j+3)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (6 + 3*i - 2*k) (5 - 2*i + 6*k) (3 + 7*j) (1 + 6*i + 3*k) (by ring)
  have h1 := forced bad
    (6 - 3*i + 2*k) (-1 - 2*i + 6*k) (3 + 7*j) (5 + 6*i + 3*k) (by ring)
  have h2 := forced bad
    (6 + 3*i - 2*j) (5 - 2*i + 6*j) (1 + 6*i + 3*j) (3 + 7*k) (by ring)
  have h3 := forced bad
    (3 + 2*i - 4*j - 2*k) (6 + 5*i + 4*j + 2*k) (-5 + 4*i - j - 4*k) (-1 + 2*i - 4*j + 5*k) (by ring)
  unfold forbidden at h0 h1 h2 h3
  omega

set_option maxHeartbeats 4000000 in
lemma residue333 (i j k : ℤ) :
    represent (7^2 + (7*i+3)^2 + (7*j+3)^2 + (7*k+3)^2) := by
  by_contra bad
  have h0 := forced bad
    (5 + 4*i - 2*j - 2*k) (7 - i + 4*j + 4*k) (1 + 4*i + 5*j - 2*k) (1 + 4*i - 2*j + 5*k) (by ring)
  have h1 := forced bad
    (5 - 4*i + 2*j + 2*k) (-1 - i + 4*j + 4*k) (5 + 4*i + 5*j - 2*k) (5 + 4*i - 2*j + 5*k) (by ring)
  have h2 := forced bad
    (5 + 2*i + 2*j - 4*k) (5 + 5*i - 2*j + 4*k) (5 - 2*i + 5*j + 4*k) (-1 + 4*i + 4*j - k) (by ring)
  have h3 := forced bad
    (5 - 2*i + 4*j - 2*k) (1 + 5*i + 4*j - 2*k) (7 + 4*i - j + 4*k) (1 - 2*i + 4*j + 5*k) (by ring)
  have h4 := forced bad
    (5 - 2*i - 2*j + 4*k) (1 + 5*i - 2*j + 4*k) (1 - 2*i + 5*j + 4*k) (7 + 4*i + 4*j - k) (by ring)
  unfold forbidden at h0 h1 h2 h3 h4
  omega


set_option maxHeartbeats 1200000 in
lemma covered (r s t : ℕ) (hr : r < 4) (hs : s < 4) (ht : t < 4) (i j k : ℤ) :
    represent (7^2 + (7*i+(r:ℤ))^2 + (7*j+(s:ℤ))^2 + (7*k+(t:ℤ))^2) := by
  interval_cases r <;> interval_cases s <;> interval_cases t
  · exact residue000 i j k
  · exact residue001 i j k
  · exact residue002 i j k
  · exact residue003 i j k
  · convert residue001 i k j using 1 <;> push_cast <;> ring
  · exact residue011 i j k
  · exact residue012 i j k
  · exact residue013 i j k
  · convert residue002 i k j using 1 <;> push_cast <;> ring
  · convert residue012 i k j using 1 <;> push_cast <;> ring
  · exact residue022 i j k
  · exact residue023 i j k
  · convert residue003 i k j using 1 <;> push_cast <;> ring
  · convert residue013 i k j using 1 <;> push_cast <;> ring
  · convert residue023 i k j using 1 <;> push_cast <;> ring
  · exact residue033 i j k
  · convert residue001 j k i using 1 <;> push_cast <;> ring
  · convert residue011 j i k using 1 <;> push_cast <;> ring
  · convert residue012 j i k using 1 <;> push_cast <;> ring
  · convert residue013 j i k using 1 <;> push_cast <;> ring
  · convert residue011 k i j using 1 <;> push_cast <;> ring
  · exact residue111 i j k
  · exact residue112 i j k
  · exact residue113 i j k
  · convert residue012 k i j using 1 <;> push_cast <;> ring
  · convert residue112 i k j using 1 <;> push_cast <;> ring
  · exact residue122 i j k
  · exact residue123 i j k
  · convert residue013 k i j using 1 <;> push_cast <;> ring
  · convert residue113 i k j using 1 <;> push_cast <;> ring
  · convert residue123 i k j using 1 <;> push_cast <;> ring
  · exact residue133 i j k
  · convert residue002 j k i using 1 <;> push_cast <;> ring
  · convert residue012 j k i using 1 <;> push_cast <;> ring
  · convert residue022 j i k using 1 <;> push_cast <;> ring
  · convert residue023 j i k using 1 <;> push_cast <;> ring
  · convert residue012 k j i using 1 <;> push_cast <;> ring
  · convert residue112 j k i using 1 <;> push_cast <;> ring
  · convert residue122 j i k using 1 <;> push_cast <;> ring
  · convert residue123 j i k using 1 <;> push_cast <;> ring
  · convert residue022 k i j using 1 <;> push_cast <;> ring
  · convert residue122 k i j using 1 <;> push_cast <;> ring
  · exact residue222 i j k
  · exact residue223 i j k
  · convert residue023 k i j using 1 <;> push_cast <;> ring
  · convert residue123 k i j using 1 <;> push_cast <;> ring
  · convert residue223 i k j using 1 <;> push_cast <;> ring
  · exact residue233 i j k
  · convert residue003 j k i using 1 <;> push_cast <;> ring
  · convert residue013 j k i using 1 <;> push_cast <;> ring
  · convert residue023 j k i using 1 <;> push_cast <;> ring
  · convert residue033 j i k using 1 <;> push_cast <;> ring
  · convert residue013 k j i using 1 <;> push_cast <;> ring
  · convert residue113 j k i using 1 <;> push_cast <;> ring
  · convert residue123 j k i using 1 <;> push_cast <;> ring
  · convert residue133 j i k using 1 <;> push_cast <;> ring
  · convert residue023 k j i using 1 <;> push_cast <;> ring
  · convert residue123 k j i using 1 <;> push_cast <;> ring
  · convert residue223 j k i using 1 <;> push_cast <;> ring
  · convert residue233 j i k using 1 <;> push_cast <;> ring
  · convert residue033 k i j using 1 <;> push_cast <;> ring
  · convert residue133 k i j using 1 <;> push_cast <;> ring
  · convert residue233 k i j using 1 <;> push_cast <;> ring
  · exact residue333 i j k

lemma normalize (x : ℤ) : ∃ i : ℤ, ∃ r : ℕ, r < 4 ∧ x^2 = (7*i + (r:ℤ))^2 := by
  have small (u : ℤ) (hu : u%7 ≤ 3) : ∃ i : ℤ, ∃ r : ℕ, r < 4 ∧ u = 7*i+(r:ℤ) := by
    refine ⟨u/7, (u%7).toNat, ?_, ?_⟩ <;> omega
  by_cases h : x%7 ≤ 3
  · obtain ⟨i,r,hr,he⟩ := small x h
    exact ⟨i,r,hr,congrArg (·^2) he⟩
  · obtain ⟨i,r,hr,he⟩ := small (-x) (by omega)
    refine ⟨i,r,hr,?_⟩
    rw [← he]
    ring

def naturalRep (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a^2+b^2+c^2+d^2=n

lemma natural_of {n : ℕ} (h : represent (n : ℤ)) : naturalRep n := by
  obtain ⟨a,b,c,d,hf,he⟩ := h
  unfold forbidden at hf
  push Not at hf
  have safe (v : ℤ) (hp : v ≠ 7) (hn : v ≠ -7) : v.natAbs ≠ 7 := by
    intro he
    rcases Int.natAbs_eq_iff.mp he with h | h
    · exact hp h
    · exact hn h
  have same (v : ℤ) : (v.natAbs : ℤ)^2 = v^2 := by rw [Int.natCast_natAbs, sq_abs]
  refine ⟨a.natAbs, b.natAbs, c.natAbs, d.natAbs, safe a (by tauto) (by tauto),
    safe b (by tauto) (by tauto), safe c (by tauto) (by tauto), safe d (by tauto) (by tauto), ?_⟩
  rw [← same a, ← same b, ← same c, ← same d] at he
  exact_mod_cast he

lemma with_seven (a b c : ℕ) : naturalRep (7^2+a^2+b^2+c^2) := by
  apply natural_of
  push_cast
  obtain ⟨i,r,hr,ha⟩ := normalize (a:ℤ)
  obtain ⟨j,s,hs,hb⟩ := normalize (b:ℤ)
  obtain ⟨k,t,ht,hc⟩ := normalize (c:ℤ)
  rw [ha,hb,hc]
  exact covered r s t hr hs ht i j k

end OMA.AvoidSeven

open OMA.AvoidSeven in
theorem OMA.solution : type_of% @OeisA241898.conjecture_2 := by
  intro n
  change naturalRep n
  obtain ⟨a,b,c,d,hn⟩ := Nat.sum_four_squares n
  rw [← hn]
  by_cases ha : a = 7
  · subst a
    exact with_seven b c d
  by_cases hb : b = 7
  · subst b
    simpa only [add_comm, add_left_comm, add_assoc] using with_seven a c d
  by_cases hc : c = 7
  · subst c
    simpa only [add_comm, add_left_comm, add_assoc] using with_seven a b d
  by_cases hd : d = 7
  · subst d
    simpa only [add_comm, add_left_comm, add_assoc] using with_seven a b c
  exact ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
