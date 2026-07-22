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

import WOW217

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- If `y` is adjacent to `v`, `x` is not, and `deg y ≤ deg x`, then there is a fourth vertex
adjacent to `x` but not to `y`.  Erasing the possible edge `xy` from both neighbor sets makes the
cardinality comparison symmetric and guarantees the witness is distinct from `y`. -/
@[category test, AMS 5]
theorem exists_exchange_vertex
    (G : SimpleGraph α) [DecidableRel G.Adj] {v x y : α}
    (hyv : G.Adj y v) (hxv : ¬G.Adj x v) (hvx : v ≠ x)
    (hdeg : G.degree y ≤ G.degree x) :
    ∃ z : α,
      G.Adj x z ∧ ¬G.Adj y z ∧ z ≠ v ∧ z ≠ x ∧ z ≠ y := by
  classical
  let A : Finset α := (G.neighborFinset x).erase y
  let B : Finset α := (G.neighborFinset y).erase x
  have hcard : B.card ≤ A.card := by
    by_cases hxy : G.Adj x y
    · have hyx : G.Adj y x := hxy.symm
      simp [A, B, hxy, hyx, G.card_neighborFinset_eq_degree]
      omega
    · have hyx : ¬G.Adj y x := by simpa [G.adj_comm] using hxy
      simp [A, B, hxy, hyx, G.card_neighborFinset_eq_degree]
      exact hdeg
  have hvB : v ∈ B := by
    simp [B, hvx, hyv]
  have hvA : v ∉ A := by
    simp [A, hxv]
  have hex : ∃ z, z ∈ A ∧ z ∉ B := by
    by_contra h
    push_neg at h
    have hsub : A ⊆ B := by
      intro z hz
      exact h z hz
    have heq : A = B := Finset.eq_of_subset_of_card_le hsub hcard
    exact hvA (heq ▸ hvB)
  obtain ⟨z, hzA, hzB⟩ := hex
  have hzA' := Finset.mem_erase.mp hzA
  have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzA'.2
  have hzy : z ≠ y := hzA'.1
  have hzx : z ≠ x := hxz.ne'
  have hyz : ¬G.Adj y z := by
    intro hAdj
    apply hzB
    exact Finset.mem_erase.mpr ⟨hzx, (G.mem_neighborFinset y z).mpr hAdj⟩
  have hzv : z ≠ v := by
    intro h
    subst z
    exact hxv hxz
  exact ⟨z, hxz, hyz, hzv, hzx, hzy⟩

end WrittenOnTheWallII.GraphConjecture217
