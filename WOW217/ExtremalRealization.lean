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
import WOW217.TwoSwitch
import WOW217.ExchangeWitness

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A graph can be replaced by a labelled degree-equivalent realization in which a distinguished
vertex is adjacent precisely to a set of highest-degree vertices of the appropriate cardinality. -/
@[category test, AMS 5]
theorem exists_degreeEquivalent_topNeighborhood
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    ∃ S : Finset α, ∃ H : SimpleGraph α,
      S ⊆ Finset.univ.erase v ∧
      S.card = G.degree v ∧
      (∀ x ∈ S, ∀ y ∈ Finset.univ.erase v, y ∉ S → G.degree y ≤ G.degree x) ∧
      (∀ w, H.degree w = G.degree w) ∧
      H.neighborFinset v = S := by
  classical
  have hNsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro x hx
    have hadj : G.Adj v x := (G.mem_neighborFinset v x).mp hx
    simp [hadj.ne']
  have hdle : G.degree v ≤ (Finset.univ.erase v).card := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hNsub
  obtain ⟨S, hSU, hScard, hStop⟩ := exists_top_degree_subset G v (G.degree v) hdle
  obtain ⟨H, hHdeg, hHmax⟩ :=
    exists_degreeEquivalent_max_neighborIntersection G v S
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hNcard : (H.neighborFinset v).card = S.card := by
    rw [H.card_neighborFinset_eq_degree, hHdeg v, hScard]
  have hSsubN : S ⊆ H.neighborFinset v := by
    intro x hxS
    by_contra hxN
    have hNnotSub : ¬H.neighborFinset v ⊆ S := by
      intro hNS
      have hEq : H.neighborFinset v = S :=
        Finset.eq_of_subset_of_card_le hNS (by rw [hNcard])
      apply hxN
      simpa [hEq] using hxS
    have hex : ∃ y, y ∈ H.neighborFinset v ∧ y ∉ S := by
      by_contra h
      push_neg at h
      exact hNnotSub (fun y hy => h y hy)
    obtain ⟨y, hyN, hyS⟩ := hex
    have hyv : H.Adj y v := by
      exact ((H.mem_neighborFinset v y).mp hyN).symm
    have hxv : ¬H.Adj x v := by
      intro hAdj
      exact hxN ((H.mem_neighborFinset v x).mpr hAdj.symm)
    have hvx : v ≠ x := by
      have hxU := hSU hxS
      simpa using (Finset.mem_erase.mp hxU).1.symm
    have hyU : y ∈ Finset.univ.erase v := by
      simp [hyv.ne]
    have hdegH : H.degree y ≤ H.degree x := by
      rw [hHdeg y, hHdeg x]
      exact hStop x hxS y hyU hyS
    obtain ⟨z, hxz, hyzN, hzv, hzx, hzy⟩ :=
      exists_exchange_vertex H hyv hxv hvx hdegH
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hyS hxS
    have hvz : v ≠ z := hzv.symm
    have hyz : y ≠ z := hzy.symm
    have hvy : H.Adj v y := hyv.symm
    have hvxN : ¬H.Adj v x := by
      simpa [H.adj_comm] using hxv
    let K : SimpleGraph α := twoSwitch H v x y z
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    have hKdeg : ∀ w, K.degree w = G.degree w := by
      intro w
      rw [show K = twoSwitch H v x y z from rfl,
        twoSwitch_degree_eq H hvx hvz hxy hyz hvy hxz hvxN hyzN w,
        hHdeg w]
    have hKneighbors : K.neighborFinset v =
        insert x ((H.neighborFinset v).erase y) := by
      exact neighborFinset_twoSwitch_v H hvx hvz hxy hyz hvy hxz hvxN hyzN
    have hxNotOld : x ∉ H.neighborFinset v := hxN
    have hxNotInter : x ∉ ((H.neighborFinset v).erase y ∩ S) := by
      simp [hxNotOld]
    have hEraseInter :
        (H.neighborFinset v).erase y ∩ S = H.neighborFinset v ∩ S := by
      ext a
      simp [hyS]
    have hScoreIncrease :
        (K.neighborFinset v ∩ S).card = (H.neighborFinset v ∩ S).card + 1 := by
      rw [hKneighbors]
      have hInterInsert :
          insert x ((H.neighborFinset v).erase y) ∩ S =
            insert x (((H.neighborFinset v).erase y) ∩ S) := by
        ext a
        simp [hxS]
      rw [hInterInsert, Finset.card_insert_of_notMem hxNotInter, hEraseInter]
    have hMax := hHmax K hKdeg
    rw [hScoreIncrease] at hMax
    omega
  have hNeq : H.neighborFinset v = S :=
    Finset.eq_of_subset_of_card_le hSsubN (by rw [hNcard])
  exact ⟨S, H, hSU, hScard, hStop, hHdeg, hNeq⟩

end WrittenOnTheWallII.GraphConjecture217
