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

import WOW217.TopDegreeSubset
import Mathlib.Data.Finset.SDiff

namespace WrittenOnTheWallII.GraphConjecture217

open Classical

variable {α : Type*} [DecidableEq α]

/-- If every selected element has weight at least every unselected element, sorting the selected
weights and then the unselected weights already gives the globally descending sorted list. -/
@[category test, AMS 5]
theorem sorted_weights_append_complement
    (U S : Finset α) (weight : α → ℕ)
    (hSU : S ⊆ U)
    (hTop : ∀ x ∈ S, ∀ y ∈ U, y ∉ S → weight y ≤ weight x) :
    ((S.val.map weight).sort (· ≥ ·)) ++
        (((U \ S).val.map weight).sort (· ≥ ·)) =
      (U.val.map weight).sort (· ≥ ·) := by
  classical
  let A : List ℕ := (S.val.map weight).sort (· ≥ ·)
  let B : List ℕ := ((U \ S).val.map weight).sort (· ≥ ·)
  let L : List ℕ := (U.val.map weight).sort (· ≥ ·)
  have hA : A.Pairwise (· ≥ ·) := by
    exact Multiset.pairwise_sort _ _
  have hB : B.Pairwise (· ≥ ·) := by
    exact Multiset.pairwise_sort _ _
  have hL : L.Pairwise (· ≥ ·) := by
    exact Multiset.pairwise_sort _ _
  have hcross : ∀ a ∈ A, ∀ b ∈ B, a ≥ b := by
    intro a ha b hb
    have ha' : a ∈ S.val.map weight := by
      simpa [A] using ha
    have hb' : b ∈ (U \ S).val.map weight := by
      simpa [B] using hb
    obtain ⟨x, hx, hxa⟩ := Multiset.mem_map.mp ha'
    obtain ⟨y, hy, hyb⟩ := Multiset.mem_map.mp hb'
    have hxS : x ∈ S := hx
    have hyDiff : y ∈ U \ S := hy
    have hyU : y ∈ U := (Finset.mem_sdiff.mp hyDiff).1
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hyDiff).2
    rw [← hxa, ← hyb]
    exact hTop x hxS y hyU hyS
  have hAB : (A ++ B).Pairwise (· ≥ ·) :=
    List.pairwise_append.mpr ⟨hA, hB, hcross⟩
  have hpart : S.val + (U \ S).val = U.val := by
    rw [add_comm, Finset.sdiff_val, Multiset.sub_add_cancel]
    exact Finset.val_le_iff.mpr hSU
  have hmapped : S.val.map weight + (U \ S).val.map weight = U.val.map weight := by
    rw [← Multiset.map_add, hpart]
  have hperm : A ++ B ~ L := by
    apply Multiset.coe_eq_coe.mp
    simpa [A, B, L] using hmapped
  have hEq : A ++ B = L := hperm.eq_of_pairwise' hAB hL
  simpa [A, B, L] using hEq

/-- Consequently, the selected sorted weights are exactly the first `S.card` entries of the global
sorted list, and the unselected sorted weights are the remaining entries. -/
@[category test, AMS 5]
theorem sorted_weights_top_take_drop
    (U S : Finset α) (weight : α → ℕ)
    (hSU : S ⊆ U)
    (hTop : ∀ x ∈ S, ∀ y ∈ U, y ∉ S → weight y ≤ weight x) :
    let all := (U.val.map weight).sort (· ≥ ·)
    let selected := (S.val.map weight).sort (· ≥ ·)
    let remaining := ((U \ S).val.map weight).sort (· ≥ ·)
    selected = all.take S.card ∧ remaining = all.drop S.card := by
  classical
  let all := (U.val.map weight).sort (· ≥ ·)
  let selected := (S.val.map weight).sort (· ≥ ·)
  let remaining := ((U \ S).val.map weight).sort (· ≥ ·)
  have hcat : selected ++ remaining = all := by
    simpa [selected, remaining, all] using
      sorted_weights_append_complement U S weight hSU hTop
  have hlen : selected.length = S.card := by
    simp [selected]
  constructor
  · calc
      selected = (selected ++ remaining).take selected.length := by simp
      _ = all.take S.card := by rw [hcat, hlen]
  · calc
      remaining = (selected ++ remaining).drop selected.length := by simp
      _ = all.drop S.card := by rw [hcat, hlen]

end WrittenOnTheWallII.GraphConjecture217
