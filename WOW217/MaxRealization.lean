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

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Among all graphs with the same labelled degree function as `G`, one maximizes the number of
vertices from `S` adjacent to `v`. -/
@[category test, AMS 5]
theorem exists_degreeEquivalent_max_neighborIntersection
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) (S : Finset α) :
    ∃ H : SimpleGraph α,
      (∀ w, H.degree w = G.degree w) ∧
        ∀ K : SimpleGraph α, ∀ [DecidableRel K.Adj],
          (∀ w, K.degree w = G.degree w) →
          ((K.neighborFinset v) ∩ S).card ≤ ((H.neighborFinset v) ∩ S).card := by
  classical
  let C : Finset (SimpleGraph α) :=
    Finset.univ.filter fun H => ∀ w, H.degree w = G.degree w
  have hGC : G ∈ C := by
    simp [C]
  have hC : C.Nonempty := ⟨G, hGC⟩
  let score : SimpleGraph α → ℕ := fun H => ((H.neighborFinset v) ∩ S).card
  let scores : Finset ℕ := C.image score
  have hscores : scores.Nonempty := hC.image score
  let M : ℕ := scores.max' hscores
  have hMmem : M ∈ scores := scores.max'_mem hscores
  obtain ⟨H, hHC, hscore⟩ := Finset.mem_image.mp hMmem
  have hHdeg : ∀ w, H.degree w = G.degree w := by
    simpa [C] using hHC
  refine ⟨H, hHdeg, ?_⟩
  intro K instK hKdeg
  letI : DecidableRel K.Adj := instK
  have hKC : K ∈ C := by
    simp [C, hKdeg]
  have hKscore : score K ∈ scores := Finset.mem_image.mpr ⟨K, hKC, rfl⟩
  have hle : score K ≤ M := scores.le_max' (score K) hKscore
  simpa [score, hscore] using hle

end WrittenOnTheWallII.GraphConjecture217
