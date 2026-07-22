/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import WOW217.Admissible

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The graph degree multiset, sorted in descending order exactly as in `SimpleGraph.residue`. -/
noncomputable def sortedDegreeList (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)

@[category test, AMS 5]
theorem residue_eq_residueAux_sortedDegreeList
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    residue G = residueAux (sortedDegreeList G) := by
  rfl

@[category test, AMS 5]
theorem sortedDegreeList_length (G : SimpleGraph α) [DecidableRel G.Adj] :
    (sortedDegreeList G).length = Fintype.card α := by
  simp [sortedDegreeList]

@[category test, AMS 5]
theorem sortedDegreeList_pairwise (G : SimpleGraph α) [DecidableRel G.Adj] :
    (sortedDegreeList G).Pairwise (· ≥ ·) := by
  exact Multiset.pairwise_sort _ _

/-- Every entry after the head of a sorted degree list is at most the head. -/
@[category test, AMS 5]
theorem sortedDegreeList_tail_le_head
    (G : SimpleGraph α) [DecidableRel G.Adj] {d : ℕ} {rest : List ℕ}
    (hseq : sortedDegreeList G = d :: rest) :
    ∀ x ∈ rest, x ≤ d := by
  have hs := sortedDegreeList_pairwise G
  rw [hseq] at hs
  simpa using hs.rel_get

/-- The head degree of a graph's sorted degree list fits in the remaining list. -/
@[category test, AMS 5]
theorem sortedDegreeList_head_le_tail_length
    (G : SimpleGraph α) [DecidableRel G.Adj] {d : ℕ} {rest : List ℕ}
    (hseq : sortedDegreeList G = d :: rest) :
    d ≤ rest.length := by
  have hdmem : d ∈ sortedDegreeList G := by
    rw [hseq]
    simp
  have hdorig : d ∈ (Finset.univ.val.map fun v => G.degree v) := by
    simpa [sortedDegreeList] using hdmem
  obtain ⟨v, hv, hdeg⟩ := Multiset.mem_map.mp hdorig
  have hlt : G.degree v < Fintype.card α := G.degree_lt_card_verts v
  have hlen := sortedDegreeList_length G
  rw [hseq] at hlen
  simp only [List.length_cons] at hlen
  omega

/-- A zero head in the descending degree list forces every remaining degree to be zero. -/
@[category test, AMS 5]
theorem sortedDegreeList_zero_tail
    (G : SimpleGraph α) [DecidableRel G.Adj] {rest : List ℕ}
    (hseq : sortedDegreeList G = 0 :: rest) :
    ∀ x ∈ rest, x = 0 := by
  intro x hx
  have hle := sortedDegreeList_tail_le_head G hseq x hx
  omega

end WrittenOnTheWallII.GraphConjecture217
