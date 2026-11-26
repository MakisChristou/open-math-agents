import FormalConjectures.ErdosProblems.«834»

/-! Ruiliang Li's nine-vertex hypergraph, Theorem 4.1 of arXiv:2512.24850.
The vertices from the paper are numbered from zero below. Every binary
color class contains an edge or misses one. Binary certificates for the edge
deletions and an explicit three-coloring give the other bounds. -/

namespace OMA.CriticalTriples

open Finset

def edges : Finset (Finset (Fin 9)) :=
  {{0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5},
    {0, 3, 7}, {0, 3, 8}, {0, 4, 6}, {0, 4, 7},
    {0, 4, 8}, {0, 5, 6}, {1, 2, 5}, {1, 2, 6},
    {1, 3, 8}, {1, 4, 8}, {1, 5, 6}, {2, 3, 7},
    {2, 4, 7}, {2, 5, 6}, {3, 5, 7}, {3, 5, 8},
    {4, 6, 7}, {4, 6, 8}}

def threeColors : Fin 9 → Fin 3 := ![0, 0, 1, 0, 0, 1, 2, 1, 1]

lemma split_coloring {F : Finset (Finset (Fin 9))} {blue : Finset (Fin 9)}
    (h : ∀ e ∈ F, (∃ x ∈ e, x ∈ blue) ∧ ∃ y ∈ e, y ∉ blue) :
    F.HypergraphColorable 2 := by
  refine ⟨fun i => if i ∈ blue then 0 else 1, ?_⟩
  intro e he
  obtain ⟨⟨x, hx, hxb⟩, y, hy, hyb⟩ := h e he
  exact ⟨x, hx, y, hy, by simp [hxb, hyb]⟩

-- Every assignment of two colors to the nine vertices has a monochromatic edge.
set_option maxHeartbeats 2500000 in
lemma forced : ∀ a b c d e f g h i : Bool,
    (a = b ∧ a = c) ∨
    (a = b ∧ a = i) ∨
    (a = c ∧ a = h) ∨
    (a = d ∧ a = f) ∨
    (a = d ∧ a = h) ∨
    (a = d ∧ a = i) ∨
    (a = e ∧ a = g) ∨
    (a = e ∧ a = h) ∨
    (a = e ∧ a = i) ∨
    (a = f ∧ a = g) ∨
    (b = c ∧ b = f) ∨
    (b = c ∧ b = g) ∨
    (b = d ∧ b = i) ∨
    (b = e ∧ b = i) ∨
    (b = f ∧ b = g) ∨
    (c = d ∧ c = h) ∨
    (c = e ∧ c = h) ∨
    (c = f ∧ c = g) ∨
    (d = f ∧ d = h) ∨
    (d = f ∧ d = i) ∨
    (e = g ∧ e = h) ∨
    (e = g ∧ e = i) := by
  intro a b c d e f g h i
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;> cases h <;> cases i <;> decide

lemma no_two : ¬edges.HypergraphColorable 2 := by
  rintro ⟨c, hc⟩
  let bit (v : Fin 9) := decide (c v = 0)
  have inj : Function.Injective (fun t : Fin 2 => decide (t = 0)) := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have no_mono (a b d : Fin 9) (he : {a,b,d} ∈ edges) :
      ¬ (bit a = bit b ∧ bit a = bit d) := by
    rintro ⟨hab, had⟩
    have eq₁ : c a = c b := inj hab
    have eq₂ : c a = c d := inj had
    obtain ⟨x, hx, y, hy, hxy⟩ := hc _ he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> grind
  rcases forced (bit 0) (bit 1) (bit 2) (bit 3) (bit 4) (bit 5) (bit 6) (bit 7) (bit 8) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact no_mono 0 1 2 (by decide) h
  · exact no_mono 0 1 8 (by decide) h
  · exact no_mono 0 2 7 (by decide) h
  · exact no_mono 0 3 5 (by decide) h
  · exact no_mono 0 3 7 (by decide) h
  · exact no_mono 0 3 8 (by decide) h
  · exact no_mono 0 4 6 (by decide) h
  · exact no_mono 0 4 7 (by decide) h
  · exact no_mono 0 4 8 (by decide) h
  · exact no_mono 0 5 6 (by decide) h
  · exact no_mono 1 2 5 (by decide) h
  · exact no_mono 1 2 6 (by decide) h
  · exact no_mono 1 3 8 (by decide) h
  · exact no_mono 1 4 8 (by decide) h
  · exact no_mono 1 5 6 (by decide) h
  · exact no_mono 2 3 7 (by decide) h
  · exact no_mono 2 4 7 (by decide) h
  · exact no_mono 2 5 6 (by decide) h
  · exact no_mono 3 5 7 (by decide) h
  · exact no_mono 3 5 8 (by decide) h
  · exact no_mono 4 6 7 (by decide) h
  · exact no_mono 4 6 8 (by decide) h


set_option maxHeartbeats 4000000 in
lemma edge_colorable (e) (he : e ∈ edges) : (edges.erase e).HypergraphColorable 2 := by
  simp only [edges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact split_coloring (blue := {5, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 3, 4, 6}) (by decide +kernel)
  · exact split_coloring (blue := {1, 3, 4, 6}) (by decide +kernel)
  · exact split_coloring (blue := {2, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 4, 5, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 4, 5, 7}) (by decide +kernel)
  · exact split_coloring (blue := {2, 5, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 3, 6, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 3, 6, 7}) (by decide +kernel)
  · exact split_coloring (blue := {1, 2, 3, 4}) (by decide +kernel)
  · exact split_coloring (blue := {1, 2, 3, 4, 5}) (by decide +kernel)
  · exact split_coloring (blue := {1, 2, 3, 4, 6}) (by decide +kernel)
  · exact split_coloring (blue := {1, 3, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 4, 5, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 5, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 3, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 4, 5, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {2, 5, 6, 7, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 3, 4, 5, 7}) (by decide +kernel)
  · exact split_coloring (blue := {2, 3, 4, 5, 8}) (by decide +kernel)
  · exact split_coloring (blue := {1, 3, 4, 6, 7}) (by decide +kernel)
  · exact split_coloring (blue := {2, 3, 4, 6, 8}) (by decide +kernel)

lemma vertex_colorable (v : Fin 9) : (edges.filter (fun e => v ∉ e)).HypergraphColorable 2 := by
  have hall : ∀ w : Fin 9, ∃ e ∈ edges, w ∈ e := by decide +kernel
  obtain ⟨e, he, hv⟩ := hall v
  obtain ⟨c, hc⟩ := edge_colorable e he
  refine ⟨c, fun f hf => hc f ?_⟩
  obtain ⟨hf, hmiss⟩ := mem_filter.mp hf
  exact mem_erase.mpr ⟨fun h => hmiss (h ▸ hv), hf⟩

end OMA.CriticalTriples

open OMA.CriticalTriples in
theorem OMA.solution : type_of% @Erdos834.erdos_834.parts.ii := by
  refine ⟨9, edges, ?_, ⟨?_, ?_⟩, edge_colorable, vertex_colorable, ?_⟩
  · unfold Finset.IsUniform
    decide +kernel
  · refine ⟨threeColors, ?_⟩
    unfold Finset.IsProperHypergraphColoring
    decide +kernel
  · intro j hj h
    obtain ⟨c, hc⟩ := h
    apply no_two
    refine ⟨fun v => (c v).castLE (by omega), ?_⟩
    intro e he
    obtain ⟨x, hx, y, hy, hxy⟩ := hc e he
    exact ⟨x, hx, y, hy, fun heq => hxy (Fin.ext (congrArg (fun t : Fin 2 => t.val) heq))⟩
  · decide +kernel
