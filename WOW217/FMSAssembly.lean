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

import WOW217.PositivePrefix
import WOW217.ReciprocalDegrees

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every nonzero head of a sorted graph degree list satisfies the numerical hypotheses needed by
one Havel--Hakimi reciprocal-sum step. -/
@[category test, AMS 5]
theorem sortedDegreeList_current_step_conditions
    (G : SimpleGraph α) [DecidableRel G.Adj] {d : ℕ} {rest : List ℕ}
    (hseq : sortedDegreeList G = d :: rest) (hd : 1 ≤ d) :
    d ≤ rest.length ∧
      (∀ x ∈ rest.take d, 1 ≤ x) ∧
      (∀ x ∈ rest.take d, x ≤ d) := by
  refine ⟨sortedDegreeList_head_le_tail_length G hseq,
    sortedDegreeList_take_positive G hseq hd, ?_⟩
  intro x hx
  exact sortedDegreeList_tail_le_head G hseq x (List.mem_of_mem_take hx)

/-- If the exact sorted graph degree list is HH-admissible, its graph residue dominates the
Caro--Wei reciprocal degree sum. -/
@[category test, AMS 5]
theorem degreeReciprocalSum_le_residue_of_HHAdmissible
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : HHAdmissible (sortedDegreeList G)) :
    (∑ v : α, (1 : ℝ) / ((G.degree v : ℝ) + 1)) ≤ (residue G : ℝ) := by
  rw [← degreeReciprocalSum_sortedDegreeList]
  rw [residue_eq_residueAux_sortedDegreeList]
  exact degreeReciprocalSum_le_residueAux (sortedDegreeList G) hG

/-- Conditional form of the FMS/Cauchy density inequality.  The remaining combinatorial input is
precisely HH-admissibility of graphical degree sequences. -/
@[category test, AMS 5]
theorem cauchy_density_le_residue_of_HHAdmissible
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : HHAdmissible (sortedDegreeList G)) :
    (Fintype.card α : ℝ) ^ 2 /
        (2 * (G.edgeFinset.card : ℝ) + (Fintype.card α : ℝ)) ≤
      (residue G : ℝ) := by
  exact (cauchy_degree_reciprocal_lower_bound G).trans
    (degreeReciprocalSum_le_residue_of_HHAdmissible G hG)

/-- A residue-two HH-admissible graph satisfies the quadratic edge lower bound. -/
@[category test, AMS 5]
theorem edge_lower_bound_of_residue_two_of_HHAdmissible
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : HHAdmissible (sortedDegreeList G)) (hr : residue G = 2) :
    (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 2) / 4 ≤
      (G.edgeFinset.card : ℝ) := by
  have hn : 1 ≤ Fintype.card α := by
    have : 0 < Fintype.card α := Fintype.card_pos
    omega
  have hc :
      (Fintype.card α : ℝ) ^ 2 /
          (2 * (G.edgeFinset.card : ℝ) + (Fintype.card α : ℝ)) ≤ 2 := by
    simpa [hr] using cauchy_density_le_residue_of_HHAdmissible G hG
  exact edge_lower_bound_of_cauchy (Fintype.card α) G.edgeFinset.card hn hc

/-- At order at least twelve, residue two plus HH-admissibility reaches the DJS edge threshold. -/
@[category test, AMS 5]
theorem edge_threshold_of_residue_two_of_HHAdmissible
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : HHAdmissible (sortedDegreeList G)) (hr : residue G = 2)
    (hn : 12 ≤ Fintype.card α) :
    (Fintype.card α : ℝ) + 15 ≤ (G.edgeFinset.card : ℝ) := by
  have hc :
      (Fintype.card α : ℝ) ^ 2 /
          (2 * (G.edgeFinset.card : ℝ) + (Fintype.card α : ℝ)) ≤ 2 := by
    simpa [hr] using cauchy_density_le_residue_of_HHAdmissible G hG
  exact edge_threshold_of_cauchy (Fintype.card α) G.edgeFinset.card hn hc

end WrittenOnTheWallII.GraphConjecture217
