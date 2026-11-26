import FormalConjectures.OEIS.«331631»
import Mathlib.NumberTheory.PowModTotient

/-! A power of three congruent to one modulo a sufficiently large power of
ten appends the original seed as the final decimal digits of its product.
Thus every block stops. A later start is the least missing value. Blocks
cannot overlap: cancelling powers of three in a collision would put that
later start inside the earlier block. -/

namespace OMA.Tripling
open OeisA331631 Classical

lemma can_stop (s : ℕ) : ∃ e : ℕ, 0 < e ∧ ContainsSeed s (s*3^e) := by
  let M := 10^(Nat.digits 10 s).length
  have hs : s < M := Nat.lt_base_pow_length_digits (by decide)
  have hc : Nat.Coprime 3 M := (by decide : Nat.Coprime 3 10).pow_right _
  let e := M.totient
  have hmod : s*3^e ≡ s [MOD M] := by
    simpa using (Nat.ModEq.refl s).mul (Nat.ModEq.pow_totient hc)
  have hr : (s*3^e)%M = s := Eq.trans hmod (Nat.mod_eq_of_lt hs)
  have hd := Nat.mod_add_div (s*3^e) M
  rw [hr] at hd
  refine ⟨e, Nat.totient_pos.mpr (by dsimp [M]; positivity), [], Nat.digits 10 (s*3^e/M), ?_⟩
  simpa [M] using (Nat.digits_append_digits (n := s) (m := s*3^e/M) (by decide : 0 < 10)).trans
    (congrArg (Nat.digits 10) hd)

noncomputable def stop (s : ℕ) : ℕ := Nat.find (can_stop s)

lemma stop_spec (s : ℕ) : StopsAt s (stop s) :=
  ⟨(Nat.find_spec (can_stop s)).1, (Nat.find_spec (can_stop s)).2,
    fun _j hj hlt hc => Nat.find_min (can_stop s) hlt ⟨hj,hc⟩⟩

lemma missing_exists (l : List ℕ) : ∃ x : ℕ, 0 < x ∧ x ∉ l := by
  refine ⟨l.sum+1, by omega, fun h => ?_⟩
  have hh := List.le_sum_of_mem h
  omega

noncomputable def mex (l : List ℕ) := Nat.find (missing_exists l)

lemma mex_pos (l : List ℕ) : 0 < mex l := (Nat.find_spec (missing_exists l)).1
lemma mex_absent (l : List ℕ) : mex l ∉ l := (Nat.find_spec (missing_exists l)).2

lemma before_mex {l : List ℕ} {x : ℕ} (hp : 0 < x) (hlt : x < mex l) : x ∈ l := by
  by_contra hm
  exact Nat.find_min (missing_exists l) hlt ⟨hp, hm⟩

noncomputable def history : ℕ → List ℕ
  | 0 => []
  | b+1 => history b ++ blockValues (mex (history b)) (stop (mex (history b)))

noncomputable def seed (b : ℕ) := mex (history b)
noncomputable def lastExp (b : ℕ) := stop (seed b)
noncomputable def start (b : ℕ) := (history b).length

lemma hist_next (b : ℕ) : history (b+1) = history b ++ blockValues (seed b) (lastExp b) := rfl
lemma boundary (b : ℕ) : start (b+1) = start b + lastExp b + 1 := by
  simp only [start, hist_next, List.length_append, block_values_length]
  omega

lemma start_strict : StrictMono start :=
  strictMono_nat_of_lt_succ fun b => by rw [boundary]; omega

lemma block_mem {b j : ℕ} (h : j ≤ lastExp b) :
    seed b * 3^j ∈ blockValues (seed b) (lastExp b) :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩

lemma seed_strict : StrictMono seed := by
  apply strictMono_nat_of_lt_succ
  intro b
  by_contra! hle
  have hnot := mex_absent (history (b+1))
  change seed (b+1) ∉ history (b+1) at hnot
  rw [hist_next] at hnot
  apply hnot
  rcases lt_or_eq_of_le hle with h | h
  · exact List.mem_append_left _ (before_mex (mex_pos _) h)
  · apply List.mem_append_right
    simpa [h] using block_mem (b := b) (j := 0) (Nat.zero_le _)

lemma covered (n : ℕ) : ∃ b, n < start (b+1) :=
  ⟨n, lt_of_le_of_lt (start_strict.id_le n) (start_strict (Nat.lt_succ_self _))⟩

noncomputable def which (n : ℕ) := Nat.find (covered n)
noncomputable def terms (n : ℕ) := seed (which n) * 3^(n-start (which n))

lemma interval (n : ℕ) : start (which n) ≤ n ∧ n < start (which n + 1) := by
  refine ⟨?_, Nat.find_spec (covered n)⟩
  cases h : which n with
  | zero => exact Nat.zero_le _
  | succ b =>
    have hm := Nat.find_min (covered n) (show b < which n by omega)
    omega

lemma term_at (b j : ℕ) (hj : j ≤ lastExp b) :
    terms (start b + j) = seed b * 3^j := by
  let n := start b + j
  have upper : n < start (b+1) := by dsimp [n]; rw [boundary]; omega
  have idx : which n = b := by
    apply Nat.le_antisymm (Nat.find_min' (covered n) upper)
    by_contra! h
    change which n < b at h
    have h1 := (interval n).2
    have h2 := start_strict.monotone (show which n+1 ≤ b by omega)
    have h3 : start b ≤ n := Nat.le_add_right _ _
    omega
  change seed (which n) * 3^(n-start (which n)) = _
  rw [idx]
  simp [n]

lemma mem_history (b x : ℕ) : x ∈ history b ↔ ∃ i < start b, terms i = x := by
  induction b with
  | zero => simp [history, start]
  | succ b ih =>
    rw [hist_next, List.mem_append, ih]
    constructor
    · rintro (⟨i,hi,rfl⟩ | hb)
      · exact ⟨i, lt_trans hi (start_strict (Nat.lt_succ_self b)), rfl⟩
      · obtain ⟨j,hj,e⟩ := List.mem_map.mp hb
        have hj' : j ≤ lastExp b := by
          have := List.mem_range.mp hj
          omega
        exact ⟨start b + j, by rw [boundary]; omega, (term_at b j hj').trans e⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases early : i < start b
      · exact Or.inl ⟨i,early,rfl⟩
      · right
        let j := i-start b
        have hidx : start b+j = i := by dsimp [j]; omega
        have hj : j ≤ lastExp b := by rw [boundary] at hi; dsimp [j]; omega
        rw [← hidx, term_at b j hj]
        exact block_mem hj

lemma actual_seed (b : ℕ) : terms (start b) = seed b := by
  simpa using term_at b 0 (Nat.zero_le _)

lemma least_before (b : ℕ) : LeastMissingBefore terms (start b) (seed b) := by
  refine ⟨⟨mex_pos _, fun i hi eq => mex_absent _ ((mem_history b _).mpr ⟨i, hi, eq⟩)⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hx, absent⟩
  by_contra! h
  obtain ⟨i,hi,he⟩ := (mem_history b x).mp (before_mex hx h)
  exact absent i hi he

lemma follows : FollowsRule terms := by
  refine ⟨start, lastExp, rfl, ?_⟩
  intro b
  dsimp only
  rw [actual_seed]
  exact ⟨least_before b, stop_spec _, term_at b, boundary b⟩

lemma no_cross {b c i j : ℕ} (hbc : b < c) (hi : i ≤ lastExp b) :
    seed b * 3^i ≠ seed c * 3^j := by
  intro eq
  have hseed := seed_strict hbc
  have hji : j ≤ i := by
    by_contra! h
    have h1 : seed b * 3^i < seed c * 3^i := Nat.mul_lt_mul_of_pos_right hseed (by positivity)
    have h2 : seed c * 3^i ≤ seed c * 3^j :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h.le)
    omega
  let d := i-j
  have hd : d+j = i := by dsimp [d]; omega
  have e : seed b * 3^d = seed c := by
    apply Nat.mul_right_cancel (show 0 < (3:ℕ)^j by positivity)
    rw [mul_assoc, ← pow_add, hd]
    exact eq
  have hdt : d ≤ lastExp b := by dsimp [d]; omega
  have before := start_strict.monotone (show b+1 ≤ c by omega)
  have less : start b + d < start c := by rw [boundary] at before; omega
  exact (least_before c).1.2 (start b+d) less ((term_at b d hdt).trans e)

lemma injective : Function.Injective terms := by
  intro i j eq
  obtain ⟨ia,ib⟩ := interval i
  obtain ⟨ja,jb⟩ := interval j
  rw [boundary] at ib jb
  have hi : i - start (which i) ≤ lastExp (which i) := by omega
  have hj : j - start (which j) ≤ lastExp (which j) := by omega
  unfold terms at eq
  rcases lt_trichotomy (which i) (which j) with h | h | h
  · exact (no_cross h hi eq).elim
  · rw [h] at eq ia
    have hp := Nat.eq_of_mul_eq_mul_left (mex_pos (history (which j))) eq
    have he := Nat.pow_right_injective (by decide : 2 ≤ 3) hp
    omega
  · exact (no_cross h hj eq.symm).elim

lemma covers_positive (x : ℕ) (hx : 0 < x) : ∃ i, terms i = x := by
  have h1 : x+1 ≤ seed (x+1) := seed_strict.id_le (x+1)
  have h2 : x < seed (x+1) := by omega
  obtain ⟨i,_,he⟩ := (mem_history (x+1) x).mp (before_mex hx h2)
  exact ⟨i, he⟩

end OMA.Tripling

open OMA.Tripling in
theorem OMA.solution : type_of% @OeisA331631.conjecture :=
  ⟨terms, follows, injective, covers_positive⟩
