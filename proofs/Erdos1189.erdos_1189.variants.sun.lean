import FormalConjectures.ErdosProblems.«1189»
import Mathlib.Data.Nat.ModEq

/-! Write the moduli as pure powers of two and the p mixed moduli p*2^i.
The theorem is due to Zhi-Wei Sun, On covering numbers (2007).
The pure classes leave a binary residue uncovered. Over any such residue,
the mixed classes must give a bijection with the residues modulo p. Deleting
a pure class leaves two binary residues, which cannot both agree with the
unique class of modulus p*2^(p-1). -/

namespace OMA.SunCover
open Erdos1189

abbrev moduli (p L : ℕ) := (2^L * p).divisors.filter (1 < ·)

lemma cop {p : ℕ} (hp : p.Prime) (odd : Odd p) (k : ℕ) : (2^k).Coprime p :=
  ((Nat.coprime_primes Nat.prime_two hp).mpr (by rintro rfl; exact (by decide : ¬ Odd (2:ℕ)) odd)).pow_left k

lemma shape {p L m : ℕ} (hp : p.Prime) (h : m ∈ moduli p L) :
    (∃ i < L, m = 2^(i+1)) ∨ (∃ i ≤ L, m = p*2^i) := by
  obtain ⟨hd,hm⟩ := Finset.mem_filter.mp h
  have dv := Nat.dvd_of_mem_divisors hd
  by_cases pm : p ∣ m
  · obtain ⟨q,rfl⟩ := pm
    have hq : q ∣ 2^L := by
      rw [mul_comm (2^L) p] at dv
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos dv
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hq
    exact Or.inr ⟨i,hi,rfl⟩
  · have cp := (hp.coprime_iff_not_dvd.mpr pm).symm
    obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (cp.dvd_of_dvd_mul_right dv)
    cases i with
    | zero => simp at hm
    | succ i => exact Or.inl ⟨i, by omega, rfl⟩

lemma pure_mem {p L i : ℕ} (hp : p.Prime) (hi : i < L) : 2^(i+1) ∈ moduli p L := by
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) p,
    Nat.mul_ne_zero (by positivity) hp.ne_zero⟩, one_lt_pow' (by decide) (by omega)⟩

lemma mixed_mem {p L i : ℕ} (hp : p.Prime) (hi : i ≤ L) : p*2^i ∈ moduli p L := by
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨?_, Nat.mul_ne_zero (by positivity) hp.ne_zero⟩, ?_⟩
  · rw [mul_comm (2^L) p]
    exact mul_dvd_mul_left p (pow_dvd_pow 2 hi)
  · exact hp.one_lt.trans_le (Nat.le_mul_of_pos_right _ (by positivity))

def residue (m : ℕ) (hm : 0 < m) (z : ℤ) : Fin m :=
  ⟨(z % (m:ℤ)).toNat, by
    have := Int.emod_lt_of_pos z (show 0 < (m:ℤ) by exact_mod_cast hm)
    omega⟩

lemma rep {m : ℕ} (hm : 0 < m) (z : ℤ) :
    ((residue m hm z).val : ℤ) ≡ z [ZMOD (m:ℤ)] := by
  have h := Int.emod_nonneg z (show (m:ℤ) ≠ 0 by exact_mod_cast hm.ne')
  simpa [residue, Int.toNat_of_nonneg h] using Int.mod_modEq z (m:ℤ)

lemma combine {p : ℕ} (hp : p.Prime) (odd : Odd p) (k : ℕ) (b r : ℤ) :
    ∃ z : ℤ, z ≡ b [ZMOD (2:ℤ)^k] ∧ z ≡ r [ZMOD (p:ℤ)] := by
  have hpos : 0 < (2:ℕ)^k := by positivity
  let t := Nat.chineseRemainder (cop hp odd k)
    (residue (2^k) hpos b).val (residue p hp.pos r).val
  refine ⟨(t.val:ℤ), ?_, (Int.natCast_modEq_iff.mpr t.property.2).trans (rep hp.pos r)⟩
  simpa using (Int.natCast_modEq_iff.mpr t.property.1).trans (rep hpos b)

lemma smaller {i j : ℕ} {b c : ℤ} (h : i ≤ j) (e : b ≡ c [ZMOD (2:ℤ)^j]) :
    b ≡ c [ZMOD (2:ℤ)^i] := e.of_dvd (pow_dvd_pow 2 h)

lemma binary_split (b : ℤ) (k : ℕ) :
    ¬ (b ≡ b+2^k [ZMOD (2:ℤ)^(k+1)]) := by
  rw [Int.left_modEq_add_iff, pow_succ]
  intro h
  obtain ⟨u, hu⟩ := h
  have hv : (2:ℤ)^k * 1 = (2:ℤ)^k * (2*u) := by linear_combination hu
  have := mul_left_cancel₀ (show (2:ℤ)^k ≠ 0 by positivity) hv
  omega

lemma lift_bit (b : ℤ) (k : ℕ) : b+2^k ≡ b [ZMOD (2:ℤ)^k] := by
  rw [Int.add_modEq_left_iff]

def Safe (N : Finset ℕ) (a : ℕ → ℤ) (k : ℕ) (b : ℤ) : Prop :=
  ∀ i < k, 2^(i+1) ∈ N → ¬ b ≡ a (2^(i+1)) [ZMOD (2:ℤ)^(i+1)]

lemma safe_lift {N : Finset ℕ} {a : ℕ → ℤ} {k : ℕ} {b c : ℤ}
    (s : Safe N a k b) (hc : c ≡ b [ZMOD (2:ℤ)^k]) : Safe N a k c :=
  fun i hi hm hit => s i hi hm ((smaller (by omega) hc).symm.trans hit)

lemma safe_next {N : Finset ℕ} {a : ℕ → ℤ} {k : ℕ} {b : ℤ}
    (s : Safe N a k b) (h : 2^(k+1) ∈ N → ¬ b ≡ a (2^(k+1)) [ZMOD (2:ℤ)^(k+1)]) :
    Safe N a (k+1) b := by
  intro i hi hm
  rcases lt_or_eq_of_le (by omega : i ≤ k) with hl | rfl
  · exact s i hl hm
  · exact h hm

lemma avoid_bit (k : ℕ) (b target : ℤ) :
    ∃ c : ℤ, c ≡ b [ZMOD (2:ℤ)^k] ∧ ¬ c ≡ target [ZMOD (2:ℤ)^(k+1)] := by
  by_cases h : b ≡ target [ZMOD (2:ℤ)^(k+1)]
  · exact ⟨b+2^k, lift_bit b k, fun h' => binary_split b k (h.trans h'.symm)⟩
  · exact ⟨b, Int.ModEq.rfl, h⟩

lemma extend {N : Finset ℕ} {a : ℕ → ℤ} {k L : ℕ} {b : ℤ}
    (hk : k ≤ L) (s : Safe N a k b) : ∃ c : ℤ, Safe N a L c ∧ c ≡ b [ZMOD (2:ℤ)^k] := by
  induction L, hk using Nat.le_induction with
  | base => exact ⟨b,s,Int.ModEq.rfl⟩
  | succ L h ih =>
    obtain ⟨v,sv,hv⟩ := ih
    obtain ⟨w,hw,avoid⟩ := avoid_bit L v (a (2^(L+1)))
    exact ⟨w, safe_next (safe_lift sv hw) (fun _ => avoid), (smaller h hw).trans hv⟩

lemma some_safe (N : Finset ℕ) (a : ℕ → ℤ) (L : ℕ) : ∃ c, Safe N a L c := by
  have base : Safe N a 0 0 := fun i hi => (Nat.not_lt_zero i hi).elim
  obtain ⟨c,sc,_⟩ := extend (Nat.zero_le L) base
  exact ⟨c,sc⟩

lemma missing_pure {N : Finset ℕ} (a : ℕ → ℤ) {k L : ℕ} (hk : k < L)
    (hm : 2^(k+1) ∉ N) (target : ℤ) :
    ∃ c, Safe N a L c ∧ ¬ c ≡ target [ZMOD (2:ℤ)^L] := by
  obtain ⟨u,su⟩ := some_safe N a k
  obtain ⟨v,hv,avoid⟩ := avoid_bit k u target
  have next := safe_next (safe_lift su hv) (fun h => (hm h).elim)
  obtain ⟨w,sw,hw⟩ := extend (show k+1 ≤ L by omega) next
  exact ⟨w,sw, fun h => avoid (hw.symm.trans (smaller (by omega) h))⟩

lemma first_bit (L : ℕ) (z : ℤ) :
    (2:ℤ)^L ∣ z ∨ ∃ i < L, z ≡ 2^i [ZMOD (2:ℤ)^(i+1)] := by
  induction L with
  | zero => exact Or.inl (by simp)
  | succ k ih =>
    rcases ih with ⟨d,hd⟩ | ⟨i,hi,e⟩
    · rcases Int.even_or_odd d with ⟨u,hou⟩ | ⟨u,hou⟩
      · exact Or.inl ⟨u, by rw [hd,hou,pow_succ]; ring⟩
      · refine Or.inr ⟨k, k.lt_succ_self, Int.modEq_iff_dvd.mpr ⟨-u, ?_⟩⟩
        rw [hd,hou,pow_succ]
        ring
    · exact Or.inr ⟨i,by omega,e⟩

noncomputable def mixedValue {p : ℕ} (hp : p.Prime) (odd : Odd p) (i : ℕ) : ℤ :=
  (combine hp odd i 0 (i:ℤ)).choose

lemma cover {p : ℕ} (hp : p.Prime) (odd : Odd p) : IsCoveringSet (moduli p (p-1)) := by
  classical
  let a (m : ℕ) : ℤ := if p ∣ m then mixedValue hp odd (Nat.log 2 (m/p)) else (m/2 : ℕ)
  refine ⟨fun _ h => (Finset.mem_filter.mp h).2, a, ?_⟩
  intro z
  rcases first_bit (p-1) z with hz | ⟨i,hi,hz⟩
  · let i := (residue p hp.pos z).val
    have hi : i ≤ p-1 := by have := (residue p hp.pos z).isLt; dsimp [i]; omega
    refine ⟨p*2^i, mixed_mem hp hi, ?_⟩
    have ha : a (p*2^i) = mixedValue hp odd i := by
      simp [a, Nat.mul_div_cancel_left _ hp.pos, Nat.log_pow (by decide : 1 < 2)]
    rw [ha]
    push_cast
    apply (Int.modEq_and_modEq_iff_modEq_mul (by simpa using (cop hp odd i).symm)).mp
    have hm := (combine hp odd i 0 (i:ℤ)).choose_spec
    refine ⟨(rep hp.pos z).symm.trans hm.2.symm, ?_⟩
    exact (Int.modEq_zero_iff_dvd.mpr ((pow_dvd_pow (2:ℤ) hi).trans hz)).trans hm.1.symm
  · refine ⟨2^(i+1), pure_mem hp hi, ?_⟩
    have hn : ¬ p ∣ 2^(i+1) := hp.coprime_iff_not_dvd.mp (cop hp odd _).symm
    have ha : a (2^(i+1)) = (2:ℤ)^i := by
      dsimp [a]
      rw [if_neg hn]
      simp [pow_succ]
    rw [ha]
    simpa using hz

lemma eq_residue {p : ℕ} (hp : 0 < p) (v : ℤ) (r : Fin p)
    (e : v ≡ (r.val:ℤ) [ZMOD (p:ℤ)]) : residue p hp v = r := by
  apply Fin.ext
  have h : (r.val:ℤ) % p = r.val := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt)
  change v % p = _ at e
  rw [h] at e
  simp [residue, e]

lemma hitsMixed {p : ℕ} (hp : p.Prime) (odd : Odd p) {N : Finset ℕ}
    (sub : N ⊆ moduli p (p-1)) (a : ℕ → ℤ)
    (covers : ∀ z : ℤ, ∃ m ∈ N, z ≡ a m [ZMOD (m:ℤ)])
    {b : ℤ} (sb : Safe N a (p-1) b) (r : Fin p) :
    ∃ j : Fin p, p*2^j.val ∈ N ∧ residue p hp.pos (a (p*2^j.val)) = r ∧
      b ≡ a (p*2^j.val) [ZMOD (2:ℤ)^j.val] := by
  obtain ⟨z,hzb,hzr⟩ := combine hp odd (p-1) b (r.val:ℤ)
  obtain ⟨m,hm,he⟩ := covers z
  rcases shape hp (sub hm) with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · have he' : z ≡ a (2^(k+1)) [ZMOD (2:ℤ)^(k+1)] := by simpa using he
    exact (sb k hk hm ((smaller (by omega) hzb).symm.trans he')).elim
  · have he' : z ≡ a (p*2^k) [ZMOD (p:ℤ)*2^k] := by simpa using he
    have ep := he'.of_dvd (dvd_mul_right (p:ℤ) ((2:ℤ)^k))
    have eb := he'.of_dvd (dvd_mul_left ((2:ℤ)^k) (p:ℤ))
    exact ⟨⟨k, by have := hp.pos; omega⟩, hm, eq_residue hp.pos _ r (ep.symm.trans hzr),
      (smaller hk hzb).symm.trans eb⟩

lemma essential {p : ℕ} (hp : p.Prime) (odd : Odd p) :
    IsIrreducibleCoveringSet (moduli p (p-1)) := by
  refine ⟨cover hp odd, ?_⟩
  rintro N hN ⟨_,a,ha⟩
  obtain ⟨b,sb⟩ := some_safe N a (p-1)
  let F (j : Fin p) := residue p hp.pos (a (p*2^j.val))
  have onto : Function.Surjective F := by
    intro r
    obtain ⟨j,_,hj,_⟩ := hitsMixed hp odd hN.subset a ha sb r
    exact ⟨j,hj⟩
  have inj : Function.Injective F := Finite.injective_iff_surjective.mpr onto
  have mixed {v : ℤ} (sv : Safe N a (p-1) v) (i : Fin p) :
      p*2^i.val ∈ N ∧ v ≡ a (p*2^i.val) [ZMOD (2:ℤ)^i.val] := by
    obtain ⟨j,hm,hj,hv⟩ := hitsMixed hp odd hN.subset a ha sv (F i)
    obtain rfl : j = i := inj hj
    exact ⟨hm,hv⟩
  apply hN.not_ge
  intro m hm
  rcases shape hp hm with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · by_contra absent
    obtain ⟨v,sv,hv⟩ := missing_pure a hk absent (a (p*2^(p-1)))
    exact hv (mixed sv ⟨p-1, by have := hp.pos; omega⟩).2
  · exact (mixed sb ⟨k,by have := hp.pos; omega⟩).1

end OMA.SunCover

theorem OMA.solution : type_of% @Erdos1189.erdos_1189.variants.sun :=
  fun _ hp odd => OMA.SunCover.essential hp odd
