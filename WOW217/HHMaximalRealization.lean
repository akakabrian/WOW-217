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
import WOW217.MaxRealization
import WOW217.ExchangeWitness
import WOW217.TwoSwitch

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A labelled graph can be replaced by a degree-equivalent graph in which a distinguished
vertex is adjacent to a top-degree set of exactly its degree many other vertices.  The proof
maximizes the chosen-neighbor intersection and uses one degree-preserving 2-switch to contradict
maximality whenever a chosen non-neighbor remains. -/
@[category test, AMS 5]
theorem exists_degreeEquivalent_topDegreeNeighborhood
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    ∃ (S : Finset α) (H : SimpleGraph α),
      S ⊆ Finset.univ.erase v ∧
      S.card = G.degree v ∧
      (∀ x ∈ S, ∀ y ∈ Finset.univ.erase v, y ∉ S → G.degree y ≤ G.degree x) ∧
      (∀ w, H.degree w = G.degree w) ∧
      H.neighborFinset v = S := by
  classical
  have hd : G.degree v ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    have hlt := G.degree_lt_card_verts v
    omega
  obtain ⟨S, hSU, hScard, hStop⟩ :=
    exists_top_degree_subset G v (G.degree v) hd
  obtain ⟨H, hHdeg, hHmax⟩ :=
    exists_degreeEquivalent_max_neighborIntersection G v S
  letI : DecidableRel H.Adj := Classical.decRel _
  have hNcard : (H.neighborFinset v).card = S.card := by
    rw [H.card_neighborFinset_eq_degree, hHdeg v, hScard]
  have hSN : S ⊆ H.neighborFinset v := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨x, hxS, hxN⟩ := hnot
    have hNSnot : ¬ H.neighborFinset v ⊆ S := by
      intro hNS
      have heq : H.neighborFinset v = S :=
        Finset.eq_of_subset_of_card_le hNS hNcard.ge
      exact hxN (by simpa [heq] using hxS)
    push_neg at hNSnot
    obtain ⟨y, hyN, hyS⟩ := hNSnot
    have hxU := hSU hxS
    have hxne : x ≠ v := (Finset.mem_erase.mp hxU).1
    have hvx : v ≠ x := hxne.symm
    have hvy : H.Adj v y := (H.mem_neighborFinset v y).mp hyN
    have hyU : y ∈ Finset.univ.erase v := by
      exact Finset.mem_erase.mpr ⟨hvy.ne', Finset.mem_univ y⟩
    have hdegG : G.degree y ≤ G.degree x := hStop x hxS y hyU hyS
    have hdegH : H.degree y ≤ H.degree x := by
      rw [hHdeg y, hHdeg x]
      exact hdegG
    have hxvN : ¬H.Adj x v := by
      intro h
      exact hxN ((H.mem_neighborFinset v x).mpr h.symm)
    obtain ⟨z, hxz, hyzN, hzv, hzx, hzy⟩ :=
      exists_exchange_vertex H hvy.symm hxvN hvx hdegH
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hyS hxS
    have hvz : v ≠ z := hzv.symm
    have hyz : y ≠ z := hzy.symm
    let K : SimpleGraph α := twoSwitch H v x y z
    letI : DecidableRel K.Adj := Classical.decRel _
    have hKdeg : ∀ w, K.degree w = G.degree w := by
      intro w
      calc
        K.degree w = H.degree w := by
          exact twoSwitch_degree_eq H hvx hvz hxy hyz hvy hxz
            (by
              intro h
              exact hxvN h.symm)
            hyzN w
        _ = G.degree w := hHdeg w
    have hKv : K.neighborFinset v = insert x ((H.neighborFinset v).erase y) := by
      exact neighborFinset_twoSwitch_v H hvx hvz hxy hyz hvy hxz
        (by
          intro h
          exact hxvN h.symm)
        hyzN
    have hinter :
        (insert x ((H.neighborFinset v).erase y)) ∩ S =
          insert x ((H.neighborFinset v) ∩ S) := by
      ext w
      simp [hxS, hyS]
    have hxInter : x ∉ (H.neighborFinset v) ∩ S := by
      simp [hxN]
    have hscore :
        ((K.neighborFinset v) ∩ S).card =
          ((H.neighborFinset v) ∩ S).card + 1 := by
      rw [hKv, hinter, Finset.card_insert_of_notMem hxInter]
    have hmaxle := hHmax K hKdeg
    rw [hscore] at hmaxle
    omega
  have hEq : S = H.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hSN hNcard.le
  exact ⟨S, H, hSU, hScard, hStop, hHdeg, hEq.symm⟩

end WrittenOnTheWallII.GraphConjecture217
