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

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Cauchy--Schwarz turns the reciprocal degree sum into the edge-density expression
used in the residue-two order reduction. -/
@[category test, AMS 5]
theorem cauchy_degree_reciprocal_lower_bound
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Fintype.card α : ℝ) ^ 2 /
        (2 * (G.edgeFinset.card : ℝ) + (Fintype.card α : ℝ)) ≤
      ∑ v : α, (1 : ℝ) / ((G.degree v : ℝ) + 1) := by
  classical
  have hpos : ∀ v ∈ (Finset.univ : Finset α), 0 < ((G.degree v : ℝ) + 1) := by
    intro v hv
    positivity
  have h :=
    Finset.sq_sum_div_le_sum_sq_div (R := ℝ) (Finset.univ : Finset α)
      (fun _ : α => (1 : ℝ)) (g := fun v => (G.degree v : ℝ) + 1) hpos
  have hsumdeg :
      (∑ v : α, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simpa [Finset.sum_add_distrib, hsumdeg] using h

end WrittenOnTheWallII.GraphConjecture217
