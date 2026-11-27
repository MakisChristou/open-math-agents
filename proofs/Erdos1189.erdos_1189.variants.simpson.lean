import FormalConjectures.ErdosProblems.«1189»
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! For a modulus n which cannot be deleted, take b covered only by n.
On b+t form the product of the other roots-of-unity factors. It is nonzero
at t=0 and vanishes for 1 ≤ t < n. Expanding gives at most 2^(k-1)
exponential terms. Eliminating their bases one at a time shows that this
many consecutive zeros would force the value at zero to vanish as well.
The modulus bound was proved by R. J. Simpson (1985). -/

namespace OMA.Simpson
open Erdos1189

noncomputable def value : List (ℂ × ℂ) → ℕ → ℂ
  | [], _ => 0
  | (s,c)::xs, t => c*s^t + value xs t

lemma value_append (xs ys : List (ℂ × ℂ)) (t : ℕ) :
    value (xs ++ ys) t = value xs t + value ys t := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => rcases x with ⟨s,c⟩; simp [value,ih,add_assoc]

lemma scale (xs : List (ℂ × ℂ)) (s c : ℂ) (t : ℕ) :
    value (xs.map (fun x => (s*x.1, c*x.2))) t = c*s^t * value xs t := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => rcases x with ⟨q,w⟩; simp [value,ih,mul_pow]; ring

lemma difference (xs : List (ℂ × ℂ)) (s : ℂ) (t : ℕ) :
    value (xs.map (fun x => (x.1, x.2*(x.1-s)))) t = value xs (t+1) - s * value xs t := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => rcases x with ⟨q,w⟩; simp [value,ih,pow_succ]; ring

lemma previous (d : ℕ) (xs : List (ℂ × ℂ)) (hd : xs.length = d)
    (hn : ∀ x ∈ xs, x.1 ≠ 0) (zeros : ∀ t, 1 ≤ t → t ≤ d → value xs t = 0) :
    value xs 0 = 0 := by
  induction d generalizing xs with
  | zero => have : xs = [] := List.length_eq_zero_iff.mp hd; simp [this,value]
  | succ k ih =>
    cases xs with
    | nil => simp at hd
    | cons x xs =>
      obtain ⟨s,c⟩ := x
      have hk : xs.length = k := by simpa using hd
      let ys := xs.map fun x => (x.1, x.2*(x.1-s))
      have eqn (t : ℕ) : value ys t = value ((s,c)::xs) (t+1) - s * value ((s,c)::xs) t := by
        rw [show value ys t = _ from difference xs s t]
        simp only [value,pow_succ]
        ring
      have hprev := ih ys (by simpa [ys]) (by
        intro x hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        exact hn y (List.mem_cons_of_mem _ hy)) (by
        intro t ht ht'
        rw [eqn, zeros (t+1) (by omega) (by omega), zeros t ht (by omega)]
        ring)
      rw [eqn, zeros 1 (by omega) (by omega)] at hprev
      have hs : s ≠ 0 := hn (s,c) (by simp)
      exact (mul_eq_zero.mp (by linear_combination -hprev : s * value ((s,c)::xs) 0 = 0)).resolve_left hs

lemma expand (S : Finset ℕ) (u v : ℕ → ℂ) (h : ∀ m, v m ≠ 0) :
    ∃ xs : List (ℂ × ℂ), xs.length = 2^S.card ∧ (∀ x ∈ xs, x.1 ≠ 0) ∧
      ∀ t, value xs t = ∏ m ∈ S, (u m*(v m)^t - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨[(1,1)], by simp, ?_, ?_⟩
    · simp
    · simp [value]
  | @insert m S hm ih =>
    obtain ⟨xs,hx,hn,he⟩ := ih
    let ys := xs.map (fun x => (v m*x.1, u m*x.2))
    let zs := xs.map (fun x => ((1:ℂ)*x.1, (-1:ℂ)*x.2))
    refine ⟨ys ++ zs, ?_, ?_, ?_⟩
    · simp [ys,zs,hx,Finset.card_insert_of_notMem hm,pow_succ]; omega
    · intro x hx'
      rcases List.mem_append.mp hx' with hy | hz
      · change x ∈ xs.map (fun w => (v m*w.1, u m*w.2)) at hy
        obtain ⟨y,hmem,rfl⟩ := List.mem_map.mp hy
        exact mul_ne_zero (h m) (hn y hmem)
      · change x ∈ xs.map (fun w => ((1:ℂ)*w.1, (-1:ℂ)*w.2)) at hz
        obtain ⟨y,hmem,rfl⟩ := List.mem_map.mp hz
        simpa using hn y hmem
    · intro t
      rw [value_append, show value ys t = _ from scale xs (v m) (u m) t,
        show value zs t = _ from scale xs 1 (-1) t, Finset.prod_insert hm, he t]
      ring

noncomputable def root (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

lemma root_ne (m : ℕ) : root m ≠ 0 := Complex.exp_ne_zero _

lemma detects {m : ℕ} (hm : m ≠ 0) (b a : ℤ) (t : ℕ) :
    root m ^ (b-a) * root m ^ t = 1 ↔ a ≡ b+(t:ℤ) [ZMOD (m:ℤ)] := by
  have prim : IsPrimitiveRoot (root m) m := Complex.isPrimitiveRoot_exp m hm
  rw [← zpow_natCast (root m) t, ← zpow_add₀ (root_ne m),
    prim.zpow_eq_one_iff_dvd, Int.modEq_iff_dvd]
  ring_nf

end OMA.Simpson

open OMA.Simpson in
theorem OMA.solution : type_of% @Erdos1189.erdos_1189.variants.simpson := by
  classical
  intro M hM n hn
  obtain ⟨⟨large,a,ha⟩,irred⟩ := hM
  let S := M.erase n
  have hw : ∃ b : ℤ, ∀ m ∈ S, ¬ b ≡ a m [ZMOD (m:ℤ)] := by
    by_contra! h
    exact irred S (Finset.erase_ssubset hn)
      ⟨fun m hm => large m (Finset.mem_of_mem_erase hm), a, h⟩
  obtain ⟨b,hb⟩ := hw
  have bn : b ≡ a n [ZMOD (n:ℤ)] := by
    obtain ⟨m,hm,he⟩ := ha b
    by_cases h : m = n
    · simpa [h] using he
    · exact (hb m (Finset.mem_erase.mpr ⟨h,hm⟩) he).elim
  let u (m : ℕ) := root m ^ (b-a m)
  obtain ⟨xs,hx,hnz,he⟩ := expand S u root root_ne
  have h0 : value xs 0 ≠ 0 := by
    rw [he]
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    apply sub_ne_zero.mpr
    have bign := large m (Finset.mem_of_mem_erase hm)
    intro h
    have e := (detects (m := m) (by omega) b (a m) 0).mp h
    exact hb m hm (by simpa using e.symm)
  by_contra! h
  have hlen : xs.length = 2^(M.card-1) := by simpa [S,Finset.card_erase_of_mem hn] using hx
  apply h0
  apply previous _ xs hlen hnz
  intro t ht ht'
  obtain ⟨m,hm,hz⟩ := ha (b+(t:ℤ))
  have ne : m ≠ n := by
    rintro rfl
    have hd : (m:ℤ) ∣ (t:ℤ) := by simpa using (bn.trans hz.symm).dvd
    have dvd : m ∣ t := by exact_mod_cast hd
    have := Nat.le_of_dvd (by omega : 0 < t) dvd
    omega
  rw [he]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ne,hm⟩)
  apply sub_eq_zero.mpr
  have bign := large m hm
  exact (detects (m := m) (by omega) b (a m) t).mpr hz.symm
