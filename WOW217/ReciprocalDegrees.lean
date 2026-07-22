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

/-- Sorting the degree multiset does not change its reciprocal-degree sum. -/
@[category test, AMS 5]
theorem degreeReciprocalSum_sortedDegreeList
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    degreeReciprocalSum (sortedDegreeList G) =
      ∑ v : α, (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
  have hsort :
      ((sortedDegreeList G : List ℕ) : Multiset ℕ) =
        Finset.univ.val.map (fun v => G.degree v) := by
    exact Multiset.sort_eq
  have hsum := congrArg
    (fun s : Multiset ℕ =>
      (s.map fun d => (1 : ℝ) / ((d : ℝ) + 1)).sum) hsort
  simpa [degreeReciprocalSum] using hsum

end WrittenOnTheWallII.GraphConjecture217
