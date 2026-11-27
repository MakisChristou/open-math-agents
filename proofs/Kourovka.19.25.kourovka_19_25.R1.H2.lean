import OMAReductions.R_Kourovka_19_25_kourovka_19_25_R1

/-! The order-42 factor is the group of invertible affine transformations of
the field with seven elements. Compute the three component order distributions
separately, then combine them by least common multiples. -/

namespace OMA.AffineWitness

private structure Aff where
  slope : (ZMod 7)ˣ
  offset : ZMod 7
  deriving DecidableEq, Fintype

private theorem same {a b : Aff} (hs : a.slope=b.slope) (ho : a.offset=b.offset) : a=b := by
  cases a
  cases b
  simp_all

private instance : One Aff := ⟨⟨1,0⟩⟩
private instance : Mul Aff := ⟨fun a b => ⟨a.slope*b.slope, a.offset + (a.slope : ZMod 7)*b.offset⟩⟩
private instance : Inv Aff := ⟨fun a => ⟨a.slope⁻¹, -(↑a.slope⁻¹ : ZMod 7)*a.offset⟩⟩

private instance : Group Aff where
  one_mul a := by
    apply same
    · exact one_mul _
    · change 0+(1:ZMod 7)*a.offset=a.offset
      simp
  mul_one a := by
    apply same
    · exact mul_one _
    · change a.offset+(a.slope:ZMod 7)*0=a.offset
      simp
  mul_assoc a b c := by
    apply same
    · exact mul_assoc ..
    · change a.offset+↑a.slope*b.offset+((a.slope*b.slope : (ZMod 7)ˣ):ZMod 7)*c.offset =
        a.offset+↑a.slope*(b.offset+↑b.slope*c.offset)
      simp [mul_assoc,mul_add,add_assoc]
  inv_mul_cancel a := by
    apply same
    · exact inv_mul_cancel _
    · change -(↑a.slope⁻¹:ZMod 7)*a.offset+↑a.slope⁻¹*a.offset=0
      ring

private def guess {G : Type} [Group G] [DecidableEq G] (g : G) : ℕ :=
  ([1,2,3,4,5,6,7] : List ℕ).find? (fun n => decide (g^n=1)) |>.getD 0

private def valid {G : Type} [Group G] (g : G) (k : ℕ) : Prop :=
  0 < k ∧ g^k = 1 ∧ ∀ j : Fin k, 0 < j.val → g^j.val ≠ 1

private instance {G : Type} [Group G] [DecidableEq G] (g : G) (k : ℕ) : Decidable (valid g k) :=
  inferInstanceAs (Decidable (0 < k ∧ g^k = 1 ∧ ∀ j : Fin k, 0 < j.val → g^j.val ≠ 1))

private theorem order_valid {G : Type} [Group G] {g : G} {k : ℕ} (h : valid g k) :
    orderOf g = k := (orderOf_eq_iff h.1).mpr ⟨h.2.1, fun j hj => h.2.2 ⟨j,hj⟩⟩

private abbrev C := Multiplicative (ZMod 6)
private abbrev S := Equiv.Perm (Fin 4)

private instance permFintype : Fintype S := fintypePerm


set_option maxRecDepth 10000 in
private theorem checkC : ∀ g : C, valid g (guess g) := by decide +kernel
set_option maxRecDepth 10000 in
private theorem checkS : ∀ g : S, valid g (guess g) := by decide +kernel
set_option maxRecDepth 10000 in
private theorem checkA : ∀ g : Aff, valid g (guess g) := by decide +kernel

private def hist {G : Type} [Fintype G] (v : G → ℕ) (k : ℕ) :=
  (Finset.univ.filter (fun g => v g=k)).card

private theorem countBy {G : Type} [Fintype G] (v : G → ℕ) (hv : ∀ g, v g < 8) (f : ℕ → ℕ) :
    ∑ g : G, f (v g) = ∑ k ∈ Finset.range 8, hist v k * f k := by
  classical
  have eq := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset G)) (g := v)
    (t := Finset.range 8) (fun g _ => Finset.mem_range.mpr (hv g)) f
  simpa [hist] using eq.symm

private theorem expandThree {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (x : X → ℕ) (y : Y → ℕ) (z : Z → ℕ)
    (hx : ∀ a, x a < 8) (hy : ∀ a, y a < 8) (hz : ∀ a, z a < 8)
    (dx dy dz : ℕ → ℕ) (ex : ∀ i : Fin 8, hist x i = dx i)
    (ey : ∀ i : Fin 8, hist y i = dy i) (ez : ∀ i : Fin 8, hist z i = dz i)
    (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ a : X, ∑ b : Y, ∑ c : Z, f (x a) (y b) (z c)) =
      ∑ i ∈ Finset.range 8, dx i * ∑ j ∈ Finset.range 8, dy j *
        ∑ k ∈ Finset.range 8, dz k * f i j k := by
  rw [countBy x hx (fun i => ∑ b : Y, ∑ c : Z, f i (y b) (z c))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ex ⟨i,Finset.mem_range.mp hi⟩]
  congr 1
  rw [countBy y hy (fun j => ∑ c : Z, f i j (z c))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ey ⟨j,Finset.mem_range.mp hj⟩]
  congr 1
  rw [countBy z hz (f i j)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ez ⟨k,Finset.mem_range.mp hk⟩]

private def dc : ℕ → ℕ | 1 | 2 => 1 | 3 | 6 => 2 | _ => 0
private def ds : ℕ → ℕ | 1 => 1 | 2 => 9 | 3 => 8 | 4 => 6 | _ => 0
private def da : ℕ → ℕ | 1 => 1 | 2 => 7 | 3 | 6 => 14 | 7 => 6 | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
private theorem calcSum :
    ∑ g : C × S × Aff, Nat.totient (orderOf g) = 23984 := by
  let cost (i j k : ℕ) := Nat.totient (i.lcm (j.lcm k))
  have e : (∑ g : C × S × Aff, Nat.totient (orderOf g)) =
      ∑ g : C × S × Aff, cost (guess g.1) (guess g.2.1) (guess g.2.2) := by
    apply Finset.sum_congr rfl
    intro g _
    rw [Prod.orderOf,Prod.orderOf g.2,order_valid (checkC g.1),
      order_valid (checkS g.2.1),order_valid (checkA g.2.2)]
  rw [e,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [expandThree (guess (G:=C)) (guess (G:=S)) (guess (G:=Aff))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dc ds da (by decide +kernel) (by decide +kernel) (by decide +kernel) cost]
  decide +kernel

theorem witness : OMA.R_Kourovka_19_25_kourovka_19_25_R1.H2 := by
  refine ⟨Aff, inferInstance, inferInstance, by decide +kernel, ?_⟩
  convert calcSum using 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext g
  simp only [Finset.mem_univ]

end OMA.AffineWitness

theorem OMA.solution : OMA.R_Kourovka_19_25_kourovka_19_25_R1.H2 := OMA.AffineWitness.witness
