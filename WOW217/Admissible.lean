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

import WOW217.HavelHakimi

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

/-- Recursive admissibility conditions sufficient for the reciprocal-sum proof along the
Havel--Hakimi process.  The missing graph-theoretic theorem is precisely that a sorted graphical
degree sequence satisfies this predicate. -/
def HHAdmissible : List ℕ → Prop
  | [] => True
  | 0 :: rest => ∀ x ∈ rest, x = 0
  | d :: rest =>
      1 ≤ d ∧
      d ≤ rest.length ∧
      (∀ x ∈ rest.take d, 1 ≤ x) ∧
      (∀ x ∈ rest.take d, x ≤ d) ∧
      HHAdmissible (havelHakimiStep (d :: rest))
termination_by s => s.length
decreasing_by
  simp only [havelHakimiStep_length_cons]
  omega

/-- An all-zero list has reciprocal-degree sum equal to its length. -/
@[category test, AMS 5]
theorem degreeReciprocalSum_eq_length_of_all_zero (l : List ℕ)
    (hzero : ∀ x ∈ l, x = 0) :
    degreeReciprocalSum l = (l.length : ℝ) := by
  induction l with
  | nil => simp [degreeReciprocalSum]
  | cons x xs ih =>
      have hx : x = 0 := hzero x (by simp)
      have htail : ∀ y ∈ xs, y = 0 := by
        intro y hy
        exact hzero y (by simp [hy])
      subst x
      simp [degreeReciprocalSum, ih htail]

/-- Every HH-admissible sequence has reciprocal-degree sum at most its Havel--Hakimi residue. -/
@[category test, AMS 5]
theorem degreeReciprocalSum_le_residueAux (s : List ℕ) (hs : HHAdmissible s) :
    degreeReciprocalSum s ≤ (residueAux s : ℝ) := by
  revert hs
  induction s using residueAux.induct with
  | case1 =>
      intro hs
      simp [degreeReciprocalSum, residueAux]
  | case2 rest =>
      intro hs
      have hzero : ∀ x ∈ rest, x = 0 := by
        simpa [HHAdmissible] using hs
      have hcw := degreeReciprocalSum_eq_length_of_all_zero rest hzero
      simp [degreeReciprocalSum, residueAux, hcw]
  | case3 d rest hd ih =>
      intro hs
      have hadm :
          1 ≤ d ∧
          d ≤ rest.length ∧
          (∀ x ∈ rest.take d, 1 ≤ x) ∧
          (∀ x ∈ rest.take d, x ≤ d) ∧
          HHAdmissible (havelHakimiStep (d :: rest)) := by
        simpa [HHAdmissible, hd] using hs
      rcases hadm with ⟨hdpos, hlen, hpos, hle, hnext⟩
      have hmono := degreeReciprocalSum_le_havelHakimiStep d rest hdpos hlen hpos hle
      have hrec := ih hnext
      rw [residueAux]
      · exact hmono.trans hrec
      · exact hd

end WrittenOnTheWallII.GraphConjecture217
