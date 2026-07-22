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

/-- Number of positive entries in a numerical list. -/
def positiveCount (l : List ℕ) : ℕ :=
  (l.filter fun x => 0 < x).length

@[category test, AMS 5]
theorem positiveCount_eq_zero_of_all_zero (l : List ℕ)
    (hzero : ∀ x ∈ l, x = 0) : positiveCount l = 0 := by
  induction l with
  | nil => simp [positiveCount]
  | cons x xs ih =>
      have hx : x = 0 := hzero x (by simp)
      have htail : ∀ y ∈ xs, y = 0 := by
        intro y hy
        exact hzero y (by simp [hy])
      subst x
      simp [positiveCount, ih htail]

/-- In a descending list, if at least `n` entries are positive, then the first `n` are positive. -/
@[category test, AMS 5]
theorem take_positive_of_pairwise_of_le_positiveCount
    (l : List ℕ) (hs : l.Pairwise (· ≥ ·)) (n : ℕ)
    (hn : n ≤ positiveCount l) :
    ∀ x ∈ l.take n, 1 ≤ x := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      cases l with
      | nil => simp [positiveCount] at hn
      | cons a as =>
          have ha : 0 < a := by
            by_contra hnot
            have ha0 : a = 0 := Nat.eq_zero_of_not_pos hnot
            have hallTail : ∀ y ∈ as, y = 0 := by
              intro y hy
              have hay : a ≥ y := rel_of_pairwise_cons hs hy
              omega
            have hall : ∀ y ∈ a :: as, y = 0 := by
              intro y hy
              rcases hy with rfl | hy
              · exact ha0
              · exact hallTail y hy
            rw [positiveCount_eq_zero_of_all_zero (a :: as) hall] at hn
            omega
          have htailCount : n ≤ positiveCount as := by
            simp [positiveCount, ha] at hn
            omega
          have htail := ih as hs.of_cons htailCount
          intro x hx
          simp only [List.take_succ_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact htail x hx

/-- The positive entries in the sorted degree list are counted by the graph support. -/
@[category test, AMS 5]
theorem positiveCount_sortedDegreeList_eq_card_support
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    positiveCount (sortedDegreeList G) = G.support.toFinset.card := by
  have hsort :
      ((sortedDegreeList G : List ℕ) : Multiset ℕ) =
        Finset.univ.val.map (fun v => G.degree v) := by
    exact Multiset.sort_eq
  have hfilter := congrArg
    (fun s : Multiset ℕ => (s.filter fun d => 0 < d).card) hsort
  simpa [positiveCount, Multiset.filter_map, G.degree_pos_iff_mem_support] using hfilter

/-- A positive head `d` in a graph's descending degree list is followed by at least `d`
positive entries. -/
@[category test, AMS 5]
theorem sortedDegreeList_take_positive
    (G : SimpleGraph α) [DecidableRel G.Adj] {d : ℕ} {rest : List ℕ}
    (hseq : sortedDegreeList G = d :: rest) (hd : 1 ≤ d) :
    ∀ x ∈ rest.take d, 1 ≤ x := by
  have hdmem : d ∈ sortedDegreeList G := by
    rw [hseq]
    simp
  have hdorig : d ∈ (Finset.univ.val.map fun v => G.degree v) := by
    simpa [sortedDegreeList] using hdmem
  obtain ⟨v, hv, hdeg⟩ := Multiset.mem_map.mp hdorig
  have hvpos : 0 < G.degree v := by omega
  let U : Finset α := insert v (G.neighborFinset v)
  have hUsub : U ⊆ G.support.toFinset := by
    intro w hw
    simp only [U, Finset.mem_insert] at hw
    rw [Set.mem_toFinset]
    rcases hw with rfl | hw
    · exact (G.degree_pos_iff_mem_support v).mp hvpos
    · have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
      exact (G.degree_pos_iff_mem_support w).mp hadj.degree_pos_right
  have hcardU : U.card = d + 1 := by
    have hvnot : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
    simp [U, hvnot, G.card_neighborFinset_eq_degree, hdeg, Nat.add_comm]
  have hsupport : d + 1 ≤ G.support.toFinset.card := by
    rw [← hcardU]
    exact Finset.card_le_card hUsub
  have hfull : d + 1 ≤ positiveCount (sortedDegreeList G) := by
    rwa [positiveCount_sortedDegreeList_eq_card_support]
  have hrest : d ≤ positiveCount rest := by
    rw [hseq] at hfull
    simp [positiveCount, hd] at hfull
    omega
  have hs := sortedDegreeList_pairwise G
  rw [hseq] at hs
  exact take_positive_of_pairwise_of_le_positiveCount rest hs.of_cons d hrest

end WrittenOnTheWallII.GraphConjecture217
