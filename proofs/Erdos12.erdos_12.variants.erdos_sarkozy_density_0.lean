import FormalConjectures.ErdosProblems.«12»

/-! Erdős–Sárközy (1970). In each persistent residue class choose a member a
of the set and refine the modulus by all these representatives. Reflection
about a pairs residues in its class. Coprimality is unnecessary: two
persistent reflected residues would supply larger distinct terms b,c with
a dividing b+c. Each refinement therefore halves the occupied fraction. -/

namespace OMA.SarkozyDensity
open Finset Filter Erdos12
open scoped Topology
noncomputable section

def persists (A : Set ℕ) {m : ℕ} (r : ZMod m) : Prop :=
  ∀ K : ℕ, ∃ n ≥ K, n ∈ A ∧ (n:ZMod m) = r

open scoped Classical in
def residues (A : Set ℕ) (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  univ.filter (persists A)

lemma mem_res {A : Set ℕ} {m : ℕ} [NeZero m] {r : ZMod m} :
    r ∈ residues A m ↔ persists A r := by
  classical
  simp [residues]

lemma shrinks {A : Set ℕ} (good : IsGood A) (m : ℕ) (hm : 0 < m) :
    ∃ L : ℕ, ∃ hL : 0 < L,
      let _ : NeZero L := ⟨hL.ne'⟩
      let _ : NeZero m := ⟨hm.ne'⟩
      2 * ((residues A L).card:ℝ)/L ≤ ((residues A m).card:ℝ)/m := by
  classical
  let _ : NeZero m := ⟨hm.ne'⟩
  let R := residues A m
  have ex (r : ZMod m) : ∃ a : ℕ, 0 < a ∧ (r ∈ R → a ∈ A ∧ (a:ZMod m)=r) := by
    by_cases h : r ∈ R
    · obtain ⟨a,ha,hA,he⟩ := mem_res.mp h 1
      exact ⟨a,ha,fun _ => ⟨hA,he⟩⟩
    · exact ⟨1,by decide,fun hr => (h hr).elim⟩
  choose a hp hr using ex
  let C := ∏ r ∈ R, a r
  let L := m*C
  have hC : 0 < C := prod_pos fun r _ => hp r
  have hL : 0 < L := Nat.mul_pos hm hC
  let _ : NeZero L := ⟨hL.ne'⟩
  let T := residues A L
  let π := ZMod.castHom (show m ∣ L from dvd_mul_right ..) (ZMod m)
  let F (z : ZMod L) : ZMod L := 2*(a (π z):ZMod L) - z
  have projects {z : ZMod L} (hz : z ∈ T) : π z ∈ R := by
    apply mem_res.mpr
    intro K
    obtain ⟨b,bk,bA,be⟩ := mem_res.mp hz K
    exact ⟨b,bk,bA,by simpa [π] using congrArg π be⟩
  have stays {z : ZMod L} (hz : π z ∈ R) : π (F z) = π z := by
    dsimp [F]; simp only [map_sub,map_mul,map_ofNat,map_natCast,(hr _ hz).2]; ring
  have flip {z : ZMod L} (hz : π z ∈ R) : F (F z) = z := by
    change 2*(a (π (F z)):ZMod L) - (2*(a (π z):ZMod L) - z) = z
    rw [stays hz]; ring
  have avoid {z : ZMod L} (hz : z ∈ T) (hh : F z ∈ T) : False := by
    let d := a (π z)
    have hzR := projects hz
    have dA := (hr _ hzR).1
    obtain ⟨b,bk,bA,be⟩ := mem_res.mp hz (d+1)
    obtain ⟨c,ck,cA,ce⟩ := mem_res.mp hh (b+1)
    have dl : d ∣ L := (dvd_prod_of_mem a hzR).trans (dvd_mul_left C m)
    let ρ := ZMod.castHom dl (ZMod d)
    have eql : (b:ZMod L)+c=2*(d:ZMod L) := by rw [be,ce]; dsimp [F,d]; ring
    have sum0 : ((b+c:ℕ):ZMod d) = 0 := by
      have mapped := congrArg ρ eql
      simp only [map_add,map_natCast,map_mul,map_ofNat,ZMod.natCast_self,mul_zero] at mapped
      simpa only [Nat.cast_add] using mapped
    have eq := good.2 d dA b bA c cA ((ZMod.natCast_eq_zero_iff _ _).mp sum0) (by omega) (by omega)
    omega
  let U := T ∪ T.image F
  have cardU : U.card = 2*T.card := by
    have dis : Disjoint T (T.image F) := by
      refine disjoint_left.mpr ?_
      intro z hz hf
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hf
      exact avoid hw hz
    have inj : (T : Set (ZMod L)).InjOn F := fun x hx y hy e =>
      (flip (projects hx)).symm.trans ((congrArg F e).trans (flip (projects hy)))
    simp [U,card_union_of_disjoint dis,card_image_of_injOn inj,two_mul]
  have bound : U.card ≤ ((range C) ×ˢ R).card := by
    apply card_le_card_of_injOn (fun z : ZMod L => (z.val/m,π z))
    · intro z hz
      obtain hz | hz := mem_union.mp hz
      · exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hm).mpr (by simpa [L,mul_comm] using z.val_lt)),projects hz⟩
      · obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
        exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hm).mpr (by simpa [L,mul_comm] using (F w).val_lt)),by change π (F w) ∈ R; rw [stays (projects hw)]; exact projects hw⟩
    · intro z hz w hw e
      have e₁ : z.val/m=w.val/m := congrArg Prod.fst e
      have e₂ : π z = π w := congrArg Prod.snd e
      have pval (x : ZMod L) : (π x).val = x.val % m := by
        calc
          _ = (π (x.val:ZMod L)).val := by rw [ZMod.natCast_zmod_val]
          _ = _ := by rw [map_natCast,ZMod.val_natCast]
      have e₃ := congrArg ZMod.val e₂
      rw [pval,pval] at e₃
      apply ZMod.val_injective
      calc
        z.val = z.val % m + m*(z.val/m) := (Nat.mod_add_div ..).symm
        _ = w.val % m + m*(w.val/m) := by rw [e₁,e₃]
        _ = w.val := Nat.mod_add_div ..
  rw [cardU,card_product,card_range] at bound
  refine ⟨L,hL,?_⟩
  change 2*(T.card:ℝ)/(L:ℝ) ≤ (R.card:ℝ)/m
  rw [show (L:ℝ) = (m:ℝ)*C by exact Nat.cast_mul m C]
  have mr : (0:ℝ) < m := by exact_mod_cast hm
  have cr : (0:ℝ) < C := by exact_mod_cast hC
  field_simp
  have b : 2*(T.card:ℝ) ≤ C*(R.card:ℝ) := by exact_mod_cast bound
  nlinarith [mul_le_mul_of_nonneg_left b mr.le]

open scoped Classical in
def part (A : Set ℕ) (N : ℕ) : Finset ℕ := (range N).filter (· ∈ A)

lemma mem_part {A : Set ℕ} {N n : ℕ} : n ∈ part A N ↔ n < N ∧ n ∈ A := by
  classical
  simp [part]

def count (A : Set ℕ) (N : ℕ) : ℕ := (part A N).card

def Bound (A : Set ℕ) (d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, (count A N : ℝ) ≤ d*N + C

lemma Bound.mono {A B : Set ℕ} {a b : ℝ} (h : Bound B b) (hab : A ⊆ B) (hba : b ≤ a) :
    Bound A a := by
  classical
  obtain ⟨C,hC⟩ := h
  refine ⟨C,fun N => ?_⟩
  have cc : count A N ≤ count B N := by
    apply card_le_card
    intro n hn
    exact mem_part.mpr ⟨(mem_part.mp hn).1,hab (mem_part.mp hn).2⟩
  calc
    (count A N : ℝ) ≤ count B N := by exact_mod_cast cc
    _ ≤ b*N+C := hC N
    _ ≤ a*N+C := by gcongr

lemma Bound.union {A B : Set ℕ} {a b : ℝ} (ha : Bound A a) (hb : Bound B b) :
    Bound (A ∪ B) (a+b) := by
  classical
  obtain ⟨C,hC⟩ := ha
  obtain ⟨D,hD⟩ := hb
  refine ⟨C+D,fun N => ?_⟩
  have ab : count (A ∪ B) N ≤ count A N + count B N := by
    unfold count part
    convert card_union_le ((range N).filter (· ∈ A)) ((range N).filter (· ∈ B)) using 1
    congr 1
    ext n
    simp
    tauto
  have h : (count (A ∪ B) N : ℝ) ≤ count A N + count B N := by exact_mod_cast ab
  linarith [hC N,hD N]

lemma bound_residues {m : ℕ} (_hm : 0 < m) (R : Finset ℕ) :
    Bound {n | n % m ∈ R} ((R.card : ℝ)/m) := by
  classical
  refine ⟨R.card,fun N => ?_⟩
  have hc : count {n | n % m ∈ R} N ≤ ((range (N/m+1)) ×ˢ R).card := by
    apply card_le_card_of_injOn (fun n : ℕ => (n/m,n%m))
    · intro n hn
      obtain ⟨hN,hR⟩ := mem_part.mp hn
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hN))),hR⟩
    · intro n hn k hk e
      have e₁ := congrArg Prod.fst e
      have e₂ := congrArg Prod.snd e
      change n/m = k/m at e₁
      change n%m = k%m at e₂
      calc
        n = n%m + m*(n/m) := (Nat.mod_add_div n m).symm
        _ = k%m + m*(k/m) := by rw [e₁,e₂]
        _ = k := Nat.mod_add_div k m
  rw [card_product,card_range] at hc
  have hc' : (count {n | n % m ∈ R} N : ℝ) ≤ ((N/m : ℕ) + 1 : ℝ)*R.card := by exact_mod_cast hc
  calc
    _ ≤ _ := hc'
    _ ≤ ((N:ℝ)/m+1)*R.card := by gcongr; exact Nat.cast_div_le
    _ = _ := by ring


lemma tails (A : Set ℕ) (m : ℕ) [NeZero m] :
    ∀ᶠ n : ℕ in atTop, n ∈ A → (n:ZMod m) ∈ residues A m := by
  classical
  have each (r : ZMod m) : ∀ᶠ n : ℕ in atTop, n ∈ A → (n:ZMod m) = r → r ∈ residues A m := by
    by_cases h : persists A r
    · exact .of_forall fun _ _ _ => mem_res.mpr h
    · unfold persists at h
      push Not at h
      obtain ⟨K,hK⟩ := h
      filter_upwards [eventually_ge_atTop K] with n hn ha eq
      exact (hK n hn ha eq).elim
  filter_upwards [Filter.eventually_all.mpr each] with n hn ha
  exact hn (n:ZMod m) ha rfl

lemma bounded (A : Set ℕ) (m : ℕ) (hm : 0 < m) :
    let _ : NeZero m := ⟨hm.ne'⟩
    Bound A ((residues A m).card/(m:ℝ)) := by
  classical
  let _ : NeZero m := ⟨hm.ne'⟩
  let R := residues A m
  obtain ⟨K,hK⟩ := eventually_atTop.mp (tails A m)
  have init : Bound {n : ℕ | n < K} 0 := by
    refine ⟨K,fun N => ?_⟩
    have sub : part {n : ℕ | n < K} N ⊆ range K := fun n hn => mem_range.mpr (mem_part.mp hn).2
    have h : count {n : ℕ | n < K} N ≤ K := by simpa [count] using card_le_card sub
    simpa using (show (count {n : ℕ | n < K} N:ℝ) ≤ K by exact_mod_cast h)
  have hr := bound_residues hm (R.image ZMod.val)
  apply (init.union hr).mono
  · intro n hn
    by_cases h : n < K
    · exact Or.inl h
    · right
      exact mem_image.mpr ⟨(n:ZMod m),hK n (by omega) hn,ZMod.val_natCast _ _⟩
  · simp [R,card_image_of_injective _ (ZMod.val_injective m)]

lemma sparse {A : Set ℕ} (good : IsGood A) {e : ℝ} (he : 0 < e) : Bound A e := by
  classical
  have each (k : ℕ) : ∃ m : ℕ, ∃ hm : 0 < m, let _ : NeZero m := ⟨hm.ne'⟩
      ((residues A m).card:ℝ)/m ≤ 1/2^k := by
    induction k with
    | zero =>
      refine ⟨1,by decide,?_⟩
      have h := card_le_univ (residues A 1)
      simpa using h
    | succ k ih =>
      obtain ⟨m,hm,rate⟩ := ih
      obtain ⟨L,hL,cut⟩ := shrinks good m hm
      refine ⟨L,hL,?_⟩
      let _ : NeZero m := ⟨hm.ne'⟩
      let _ : NeZero L := ⟨hL.ne'⟩
      change ((residues A m).card:ℝ)/m ≤ 1/2^k at rate
      change 2*((residues A L).card:ℝ)/L ≤ ((residues A m).card:ℝ)/m at cut
      change ((residues A L).card:ℝ)/L ≤ 1/(2:ℝ)^(k+1)
      rw [pow_succ,← div_div]
      linarith only [cut,rate,show 2*((residues A L).card:ℝ)/L = 2*(((residues A L).card:ℝ)/L) by ring]
  obtain ⟨k,hk⟩ := exists_nat_gt (1/e)
  obtain ⟨m,hm,rate⟩ := each k
  let _ : NeZero m := ⟨hm.ne'⟩
  apply (bounded A m hm).mono Set.Subset.rfl (rate.trans ?_)
  have hl : 1/e < (2:ℝ)^k := hk.trans (by exact_mod_cast (Nat.lt_two_pow_self : k < 2^k))
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^k)).mpr
  linarith [(div_lt_iff₀ he).mp hl]

lemma density (A : Set ℕ) (h : ∀ e > (0:ℝ), Bound A e) : A.HasDensity 0 := by
  classical
  have pd (n : ℕ) : A.partialDensity Set.univ n = (count A n : ℝ)/n := by
    have eq : A ∩ Set.Iio n = (part A n : Set ℕ) := by
      ext k
      simp [mem_part, and_comm]
    simp [Set.partialDensity,eq,count]
  rw [Set.HasDensity,Metric.tendsto_nhds]
  intro e he
  obtain ⟨C,hC⟩ := h (e/2) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (max 0 (2*C/e))
  filter_upwards [eventually_ge_atTop K] with n hn
  have hN : (K:ℝ) ≤ n := by exact_mod_cast hn
  have pn : 0 < (n:ℝ) := lt_of_lt_of_le ((le_max_left _ _).trans_lt hK) hN
  have cut := (div_lt_iff₀ he).mp (lt_of_lt_of_le ((le_max_right _ _).trans_lt hK) hN)
  rw [pd,Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ pn]
  linarith [hC n]

end
end OMA.SarkozyDensity

theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.erdos_sarkozy_density_0 :=
  fun A hA => OMA.SarkozyDensity.density A (fun _ he => OMA.SarkozyDensity.sparse hA he)
