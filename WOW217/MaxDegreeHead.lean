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

import WOW217.SortedDegrees

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- At a maximum-degree vertex `v`, the descending degree list starts with `degree v`; its tail is
exactly the descending list of degrees of the other vertices. -/
@[category test, AMS 5]
theorem sortedDegreeList_eq_cons_erase_of_max
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α)
    (hmax : ∀ w, G.degree w ≤ G.degree v) :
    sortedDegreeList G =
      G.degree v :: (((Finset.univ.erase v).val.map fun w => G.degree w).sort (· ≥ ·)) := by
  classical
  let U : Finset α := Finset.univ.erase v
  have hvU : v ∉ U := by simp [U]
  have hfin : U.cons v hvU = Finset.univ := by
    ext w
    simp [U]
  have hrel : ∀ b ∈ U.val.map (fun w => G.degree w), G.degree v ≥ b := by
    intro b hb
    obtain ⟨w, hw, hwb⟩ := Multiset.mem_map.mp hb
    rw [← hwb]
    exact hmax w
  unfold sortedDegreeList
  rw [← hfin]
  simp only [Finset.cons_val, Multiset.map_cons]
  rw [Multiset.sort_cons]
  exact hrel

end WrittenOnTheWallII.GraphConjecture217
