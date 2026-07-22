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

import WOW217.Cauchy

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

/-- The reciprocal-degree sum of a numerical degree list. -/
def degreeReciprocalSum (s : List ℕ) : ℝ :=
  (s.map fun d => (1 : ℝ) / ((d : ℝ) + 1)).sum

/-- The gain in reciprocal-degree weight when a positive degree `x` is decremented. -/
def decrementGain (x : ℕ) : ℝ :=
  (1 : ℝ) / (x : ℝ) - (1 : ℝ) / ((x : ℝ) + 1)

/-- If `1 ≤ x ≤ d`, decrementing `x` gains at least `1 / (d(d+1))` in reciprocal weight. -/
@[category test, AMS 5]
theorem reciprocal_decrement_gain (d x : ℕ) (hx : 1 ≤ x) (hxd : x ≤ d) :
    (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) ≤ decrementGain x := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  have hdR : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le hxR (by exact_mod_cast hxd)
  have hdiff : decrementGain x = (1 : ℝ) / ((x : ℝ) * ((x : ℝ) + 1)) := by
    unfold decrementGain
    field_simp
    ring
  rw [hdiff]
  have hdenD : (0 : ℝ) < (d : ℝ) * ((d : ℝ) + 1) := mul_pos hdR (by positivity)
  have hdenX : (0 : ℝ) < (x : ℝ) * ((x : ℝ) + 1) := mul_pos hxR (by positivity)
  apply (div_le_div_iff₀ hdenD hdenX).2
  have hxdR : (x : ℝ) ≤ (d : ℝ) := by exact_mod_cast hxd
  nlinarith

/-- Summing the preceding pointwise bound over a list of positive entries bounded by `d`. -/
@[category test, AMS 5]
theorem sum_decrement_gain_lower_bound (d : ℕ) (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hle : ∀ x ∈ l, x ≤ d) :
    (l.length : ℝ) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) ≤
      (l.map decrementGain).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hxpos : 1 ≤ x := hpos x (by simp)
      have hxle : x ≤ d := hle x (by simp)
      have htailpos : ∀ y ∈ xs, 1 ≤ y := by
        intro y hy
        exact hpos y (by simp [hy])
      have htaille : ∀ y ∈ xs, y ≤ d := by
        intro y hy
        exact hle y (by simp [hy])
      have hxgain := reciprocal_decrement_gain d x hxpos hxle
      have htail := ih htailpos htaille
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
      nlinarith

/-- Across exactly `d` positive entries, the total decrement gain pays for deleting the head `d`. -/
@[category test, AMS 5]
theorem head_weight_le_total_decrement_gain (d : ℕ) (l : List ℕ)
    (hd : 1 ≤ d) (hlen : l.length = d)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hle : ∀ x ∈ l, x ≤ d) :
    (1 : ℝ) / ((d : ℝ) + 1) ≤ (l.map decrementGain).sum := by
  have hsum := sum_decrement_gain_lower_bound d l hpos hle
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hfactor :
      (l.length : ℝ) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) =
        (1 : ℝ) / ((d : ℝ) + 1) := by
    rw [hlen]
    norm_num
    field_simp
  rwa [hfactor] at hsum

/-- The sum of decrement gains is the difference between the post- and pre-decrement sums. -/
@[category test, AMS 5]
theorem sum_decrementGain_eq (l : List ℕ) :
    (l.map decrementGain).sum =
      (l.map fun x => (1 : ℝ) / (x : ℝ)).sum - degreeReciprocalSum l := by
  induction l with
  | nil => simp [degreeReciprocalSum]
  | cons x xs ih =>
      simp [decrementGain, degreeReciprocalSum, ih]

/-- Decrementing exactly `d` positive entries bounded by `d` does not decrease the total
reciprocal-degree sum after the head `d` is removed. -/
@[category test, AMS 5]
theorem head_and_tail_reciprocal_le_after_decrement (d : ℕ) (l : List ℕ)
    (hd : 1 ≤ d) (hlen : l.length = d)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hle : ∀ x ∈ l, x ≤ d) :
    (1 : ℝ) / ((d : ℝ) + 1) + degreeReciprocalSum l ≤
      (l.map fun x => (1 : ℝ) / (x : ℝ)).sum := by
  have hgain := head_weight_le_total_decrement_gain d l hd hlen hpos hle
  rw [sum_decrementGain_eq] at hgain
  linarith

end WrittenOnTheWallII.GraphConjecture217
