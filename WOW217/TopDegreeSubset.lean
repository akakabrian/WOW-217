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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

namespace WrittenOnTheWallII.GraphConjecture217

open Classical

variable {α : Type*} [DecidableEq α]

/-- A finite set has a fixed-cardinality subset whose every selected weight is at least every
unselected weight.  It is obtained by maximizing the total weight over all such subsets. -/
@[category test, AMS 5]
theorem exists_top_weight_subset
    (U : Finset α) (weight : α → ℕ) (d : ℕ) (hd : d ≤ U.card) :
    ∃ S : Finset α,
      S ⊆ U ∧ S.card = d ∧
        ∀ x ∈ S, ∀ y ∈ U, y ∉ S → weight y ≤ weight x := by
  classical
  let C : Finset (Finset α) := U.powersetCard d
  have hC : C.Nonempty := Finset.powersetCard_nonempty.mpr hd
  let score : Finset α → ℕ := fun S => ∑ x ∈ S, weight x
  let scores : Finset ℕ := C.image score
  have hscores : scores.Nonempty := hC.image score
  let M : ℕ := scores.max' hscores
  have hMmem : M ∈ scores := scores.max'_mem hscores
  obtain ⟨S, hSC, hscore⟩ := Finset.mem_image.mp hMmem
  have hSdata := Finset.mem_powersetCard.mp hSC
  refine ⟨S, hSdata.1, hSdata.2, ?_⟩
  intro x hx y hyU hyS
  by_contra hnot
  have hxy : weight x < weight y := Nat.lt_of_not_ge hnot
  let T : Finset α := insert y (S.erase x)
  have hyErase : y ∉ S.erase x := by simp [hyS]
  have hTsub : T ⊆ U := by
    intro z hz
    simp only [T, Finset.mem_insert, Finset.mem_erase] at hz
    rcases hz with rfl | hz
    · exact hyU
    · exact hSdata.1 hz.2
  have hTcard : T.card = d := by
    rw [T, Finset.card_insert_of_notMem hyErase, Finset.card_erase_of_mem hx, hSdata.2]
    omega
  have hTC : T ∈ C := Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
  have hTscoreMem : score T ∈ scores := Finset.mem_image.mpr ⟨T, hTC, rfl⟩
  have hTle : score T ≤ M := scores.le_max' (score T) hTscoreMem
  have hSscore : score S = M := hscore
  have hErase : (∑ z ∈ S.erase x, weight z) + weight x = score S := by
    simpa [score, add_comm] using Finset.sum_erase_add (s := S) (f := weight) hx
  have hTscore : score T = weight y + ∑ z ∈ S.erase x, weight z := by
    simp [score, T, hyErase]
  rw [hSscore] at hErase
  rw [hTscore] at hTle
  omega

/-- Specialization to graph degrees outside a distinguished vertex. -/
@[category test, AMS 5]
theorem exists_top_degree_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) (d : ℕ)
    (hd : d ≤ (Finset.univ.erase v).card) :
    ∃ S : Finset α,
      S ⊆ Finset.univ.erase v ∧ S.card = d ∧
        ∀ x ∈ S, ∀ y ∈ Finset.univ.erase v, y ∉ S → G.degree y ≤ G.degree x :=
  exists_top_weight_subset (Finset.univ.erase v) G.degree d hd

end WrittenOnTheWallII.GraphConjecture217
