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

import WOW217.ExtremalRealization

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Deleting one vertex lowers the degree of a remaining vertex exactly when the two vertices were
adjacent. -/
@[category test, AMS 5]
theorem degree_induce_compl_singleton
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) (w : ({v}ᶜ : Set α)) :
    (G.induce ({v}ᶜ : Set α)).degree w =
      G.degree w - if G.Adj v w then 1 else 0 := by
  classical
  have hmap := G.map_neighborFinset_induce (s := ({v}ᶜ : Set α)) w
  have hcard := congrArg Finset.card hmap
  simp only [Finset.card_map] at hcard
  by_cases hvw : G.Adj v w
  · have hwv : G.Adj w v := hvw.symm
    have hvmem : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hwv
    simpa [Set.toFinset_compl, Set.toFinset_singleton, hvmem, hvw,
      G.card_neighborFinset_eq_degree] using hcard
  · have hwv : ¬G.Adj w v := by simpa [G.adj_comm] using hvw
    have hvnot : v ∉ G.neighborFinset w := by
      simpa using hwv
    simpa [Set.toFinset_compl, Set.toFinset_singleton, hvnot, hvw,
      G.card_neighborFinset_eq_degree] using hcard

end WrittenOnTheWallII.GraphConjecture217
