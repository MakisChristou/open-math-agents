import OMAStatements.S_oeis_a122554

/-!
Sela Fried's proof on the OEIS page for A122554 partitions each Layman set by parity.
The odd part is an interval of odd numbers. Dividing the even part by two gives the
union of a preceding set and the translate by one of the set before that.
-/
namespace Layman
open OMA.S_oeis_a122554 Finset

private lemma step (n x : ℕ) : x ∈ S (n + 2) ↔ x ∈ S (n + 1) ∨
    (∃ y ∈ S (n + 1), y + 2 = x) ∨ (∃ y ∈ S (n + 1), 2 * y = x) := by
  simp [S]

private lemma stay {n x : ℕ} (h : x ∈ S (n + 1)) : x ∈ S (n + 2) :=
  (step n x).mpr (Or.inl h)

private lemma addTwo {n x : ℕ} (h : x ∈ S (n + 1)) : x + 2 ∈ S (n + 2) :=
  (step n _).mpr (Or.inr (Or.inl ⟨x, h, rfl⟩))

private lemma double {n x : ℕ} (h : x ∈ S (n + 1)) : 2 * x ∈ S (n + 2) :=
  (step n _).mpr (Or.inr (Or.inr ⟨x, h, rfl⟩))

private lemma positive (n : ℕ) {x : ℕ} (hx : x ∈ S (n + 1)) : 0 < x := by
  induction n generalizing x with
  | zero => simp [S] at hx; omega
  | succ n ih =>
    rcases (step n x).mp hx with h | ⟨y, _, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ih h
    · omega
    · have := ih hy
      omega

private lemma odds (n j : ℕ) : 2 * j + 1 ∈ S (n + 1) ↔ j < n + 1 := by
  induction n generalizing j with
  | zero => simp [S]
  | succ n ih =>
    rw [step]
    constructor
    · rintro (h | ⟨y, hy, he⟩ | ⟨y, _, he⟩)
      · have := (ih j).mp h
        omega
      · have jpos : 0 < j := by omega
        have ey : y = 2 * (j - 1) + 1 := by omega
        rw [ey] at hy
        have := (ih _).mp hy
        omega
      · omega
    · intro hj
      by_cases h : j < n + 1
      · exact Or.inl ((ih j).mpr h)
      · exact Or.inr (Or.inl ⟨2 * (j - 1) + 1, (ih _).mpr (by omega), by omega⟩)

private lemma initialInterval (n x : ℕ) (h : 0 < x) (bound : x ≤ 2 * (n + 3)) :
    x ∈ S (n + 3) := by
  induction n generalizing x with
  | zero => interval_cases x <;> decide
  | succ n ih =>
    by_cases old : x ≤ 2 * (n + 3)
    · exact stay (ih x h old)
    · have := addTwo (ih (x - 2) (by omega) (by omega))
      simpa [show x - 2 + 2 = x by omega] using this

private lemma evens (n x : ℕ) : 2 * x ∈ S (n + 3) ↔
    x ∈ S (n + 2) ∨ ∃ y ∈ S (n + 1), y + 1 = x := by
  induction n generalizing x with
  | zero => simp [S]; omega
  | succ n ih =>
    constructor
    · intro h
      rcases (step (n + 2) _).mp h with old | ⟨y, hy, ey⟩ | ⟨y, hy, ey⟩
      · rcases (ih x).mp old with h | ⟨y, hy, ey⟩
        · exact Or.inl (stay h)
        · exact Or.inr ⟨y, stay hy, ey⟩
      · have ey' : y = 2 * (x - 1) := by omega
        rw [ey'] at hy
        rcases (ih _).mp hy with h | ⟨v, hv, ev⟩
        · exact Or.inr ⟨x - 1, h, by omega⟩
        · exact Or.inl (by simpa [show v + 2 = x by omega] using stay (addTwo hv))
      · exact Or.inl (by simpa [show y = x by omega] using hy)
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact double h
      · simpa [Nat.mul_add] using addTwo (double hy)

private def translated (s : Finset ℕ) := s.image (fun x => x + 1)
private def half (n : ℕ) := S (n + 2) ∪ translated (S (n + 1))

private lemma partition (n : ℕ) :
    S (n + 3) = (range (n + 3)).image (fun j => 2 * j + 1) ∪
      (half n).image (fun j => 2 * j) := by
  ext x
  simp only [mem_union, mem_image, mem_range, half, translated]
  by_cases even : x % 2 = 0
  · have hx : x = 2 * (x / 2) := by omega
    constructor
    · intro h
      rw [hx] at h
      exact Or.inr ⟨x / 2, (evens n _).mp h, hx.symm⟩
    · rintro (⟨j, _, hj⟩ | ⟨j, hj, rfl⟩)
      · omega
      · exact (evens n j).mpr hj
  · have hx : x = 2 * (x / 2) + 1 := by omega
    constructor
    · intro h
      rw [hx] at h
      exact Or.inl ⟨x / 2, (odds (n + 2) _).mp h, hx.symm⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, _, hj⟩)
      · exact (odds _ _).mpr hj
      · omega

private lemma size (n : ℕ) : a (n + 3) = n + 3 + (half n).card := by
  unfold a
  rw [partition, card_union_of_disjoint, card_image_of_injective, card_image_of_injective, card_range]
  · intro x y eq
    dsimp at eq
    omega
  · intro x y eq
    dsimp at eq
    omega
  · apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, ei⟩ := mem_image.mp hx
    obtain ⟨j, _, ej⟩ := mem_image.mp hy
    omega

private lemma overlap (n : ℕ) :
    S (n + 4) ∩ translated (S (n + 3)) = Icc 2 (2 * n + 7) := by
  ext x
  simp only [translated, mem_inter, mem_image, mem_Icc]
  constructor
  · rintro ⟨h, y, hy, rfl⟩
    have hpos := positive (n + 2) hy
    constructor
    · omega
    · by_cases he : y % 2 = 0
      · have eq : y + 1 = 2 * (y / 2) + 1 := by omega
        rw [eq] at h
        have := (odds (n + 3) _).mp h
        omega
      · have eq : y = 2 * (y / 2) + 1 := by omega
        rw [eq] at hy
        have := (odds (n + 2) _).mp hy
        omega
  · rintro ⟨hl, hu⟩
    exact ⟨initialInterval (n + 1) x (by omega) (by omega),
      x - 1, initialInterval n (x - 1) (by omega) (by omega), by omega⟩

private lemma recurrence (n : ℕ) :
    a (n + 5) + (n + 1) = a (n + 4) + a (n + 3) := by
  have hu := card_union_add_card_inter (S (n + 4)) (translated (S (n + 3)))
  rw [overlap, Nat.card_Icc] at hu
  change (half (n + 2)).card + _ = a (n + 4) + _ at hu
  have ht : (translated (S (n + 3))).card = a (n + 3) :=
    card_image_of_injective _ (by intro x y eq; dsimp at eq; omega)
  rw [ht] at hu
  have hs : a (n + 5) = n + 5 + (half (n + 2)).card := size (n + 2)
  omega

private lemma closed_form (n : ℕ) : a (n + 3) + 1 = LucasNat (n + 3) + (n + 3) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    have hr := recurrence n
    change a (n + 4) + 1 = LucasNat (n + 4) + (n + 4) at h₁
    change a (n + 5) + 1 = (LucasNat (n + 3) + LucasNat (n + 4)) + (n + 5)
    omega

theorem result : type_of% @OMA.S_oeis_a122554.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have h₀ := recurrence k
    have h₁ := recurrence (k + 1)
    have h₂ := recurrence (k + 2)
    change a (k + 6) + (k + 2) = a (k + 5) + a (k + 4) at h₁
    change a (k + 7) + (k + 3) = a (k + 6) + a (k + 5) at h₂
    change a (k + 7) + 2 * a (k + 5) + a (k + 4) = 3 * a (k + 6) + a (k + 3)
    omega
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have := closed_form k
    omega

end Layman

theorem OMA.solution : type_of% @OMA.S_oeis_a122554.main := Layman.result
