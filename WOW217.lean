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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture217

/-!
# WOWII Conjecture 217 isolated formalization attempt

This scratch module preserves the upstream target and records only kernel-checkable
reductions. It is intentionally kept off `main` and is not a submission artifact.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- A graph has a Hamiltonian path in the exact form used by Conjecture 217. -/
abbrev HasHamiltonianPath (G : SimpleGraph α) : Prop :=
  ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

/-- The indicator is one exactly in the residue-two branch. -/
@[category test, AMS 5]
theorem residueEqTwoIndicator_eq_one_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 1 ↔ residue G = 2 := by
  simp [residueEqTwoIndicator]

/-- The indicator is zero exactly outside the residue-two branch. -/
@[category test, AMS 5]
theorem residueEqTwoIndicator_eq_zero_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 0 ↔ residue G ≠ 2 := by
  simp [residueEqTwoIndicator]

/-- Outside the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 2`. -/
@[category test, AMS 5]
theorem Ls_le_two_of_residue_ne_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G ≠ 2) : Ls G ≤ 2 := by
  simpa [residueEqTwoIndicator, hr] using hL

/-- In the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 6`. -/
@[category test, AMS 5]
theorem Ls_le_six_of_residue_eq_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G = 2) : Ls G ≤ 6 := by
  norm_num [residueEqTwoIndicator, hr] at hL
  exact hL

/-- Every individual spanning-tree leaf count is bounded by the `sSup` defining `Ls`. -/
@[category test, AMS 5]
theorem spanningTree_leafCount_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : G.Subgraph) (hT : T.IsSpanning ∧ IsTree T.coe) :
    ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ) ≤ Ls G := by
  classical
  unfold Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro x ⟨S, hS, rfl⟩
    change ((S.verts.toFinset.filter (fun v => S.degree v = 1)).card : ℝ) ≤
      (Fintype.card α : ℝ)
    exact_mod_cast
      (Finset.card_le_univ (S.verts.toFinset.filter (fun v => S.degree v = 1)))
  · exact ⟨T, hT, rfl⟩

/-- A connected graph with `Ls ≤ 2` has a concrete spanning tree with at most two leaves. -/
@[category test, AMS 5]
theorem exists_spanningTree_leafCount_le_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hL : Ls G ≤ 2) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧
        (T.verts.toFinset.filter (fun v => T.degree v = 1)).card ≤ 2 := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
  let S : G.Subgraph := SimpleGraph.toSubgraph (G := G) T hTG
  have hSspan : S.IsSpanning := by
    simpa [S] using SimpleGraph.toSubgraph.isSpanning T hTG
  have hStree : IsTree S.coe := by
    apply (S.spanningCoeEquivCoeOfSpanning hSspan).isTree_iff.mp
    simpa [S, SimpleGraph.toSubgraph] using hTtree
  have hcountR := spanningTree_leafCount_le_Ls G S ⟨hSspan, hStree⟩
  refine ⟨S, hSspan, hStree, ?_⟩
  exact_mod_cast hcountR.trans hL

/-- A connected graph with `Ls ≤ 6` has a concrete spanning tree with at most six leaves. -/
@[category test, AMS 5]
theorem exists_spanningTree_leafCount_le_six (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hL : Ls G ≤ 6) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧
        (T.verts.toFinset.filter (fun v => T.degree v = 1)).card ≤ 6 := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
  let S : G.Subgraph := SimpleGraph.toSubgraph (G := G) T hTG
  have hSspan : S.IsSpanning := by
    simpa [S] using SimpleGraph.toSubgraph.isSpanning T hTG
  have hStree : IsTree S.coe := by
    apply (S.spanningCoeEquivCoeOfSpanning hSspan).isTree_iff.mp
    simpa [S, SimpleGraph.toSubgraph] using hTtree
  have hcountR := spanningTree_leafCount_le_Ls G S ⟨hSspan, hStree⟩
  refine ⟨S, hSspan, hStree, ?_⟩
  exact_mod_cast hcountR.trans hL

/-- The elementary quadratic threshold used after the residue/Caro--Wei estimate. -/
@[category test, AMS 5]
theorem quadratic_density_threshold (n : ℕ) (hn : 12 ≤ n) :
    (n : ℝ) + 15 ≤ (n : ℝ) * ((n : ℝ) - 2) / 4 := by
  have hnR : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 ≤ ((n : ℝ) - 12) * ((n : ℝ) + 6) :=
    mul_nonneg (sub_nonneg.mpr hnR) (by positivity)
  nlinarith

/-- Rearrangement of the Cauchy estimate `n²/(2m+n) ≤ 2`. -/
@[category test, AMS 5]
theorem edge_lower_bound_of_cauchy (n m : ℕ) (hn : 1 ≤ n)
    (h : (n : ℝ) ^ 2 / (2 * (m : ℝ) + (n : ℝ)) ≤ 2) :
    (n : ℝ) * ((n : ℝ) - 2) / 4 ≤ (m : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 2 * (m : ℝ) + (n : ℝ) := by positivity
  have hmul := (div_le_iff₀ hden).mp h
  nlinarith

/-- Combining the preceding arithmetic steps gives the DJS edge threshold at order at least twelve. -/
@[category test, AMS 5]
theorem edge_threshold_of_cauchy (n m : ℕ) (hn : 12 ≤ n)
    (h : (n : ℝ) ^ 2 / (2 * (m : ℝ) + (n : ℝ)) ≤ 2) :
    (n : ℝ) + 15 ≤ (m : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  exact (quadratic_density_threshold n hn).trans (edge_lower_bound_of_cauchy n m hn1 h)

/-- A finite nontrivial tree with at most two leaves has maximum degree at most two. -/
@[category test, AMS 5]
theorem tree_degree_le_two_of_leafCount_le_two (H : SimpleGraph α) [DecidableRel H.Adj]
    (hT : IsTree H)
    (hLeaves : (Finset.univ.filter (fun v => H.degree v = 1)).card ≤ 2) :
    ∀ v, H.degree v ≤ 2 := by
  classical
  intro v
  by_contra hv
  have hv3 : 3 ≤ H.degree v := by omega
  have hmin : H.minDegree = 1 := hT.minDegree_eq_one_of_nontrivial
  have hdeg1 (w : α) : 1 ≤ H.degree w := by
    rw [← hmin]
    exact H.minDegree_le_degree w
  have hsumdeg : ∑ w : α, H.degree w = 2 * H.edgeFinset.card :=
    H.sum_degrees_eq_twice_card_edges
  have hedge : H.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
  have hsumZ : ∑ w : α, ((2 : ℤ) - (H.degree w : ℤ)) = 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    have hsumdegZ : (∑ w : α, (H.degree w : ℤ)) = 2 * (H.edgeFinset.card : ℤ) := by
      exact_mod_cast hsumdeg
    rw [hsumdegZ]
    have hedgeZ : (H.edgeFinset.card : ℤ) + 1 = Fintype.card α := by
      exact_mod_cast hedge
    omega
  have hterm (w : α) :
      ((2 : ℤ) - (H.degree w : ℤ)) ≤
        (if H.degree w = 1 then 1 else if w = v then -1 else 0) := by
    by_cases hw1 : H.degree w = 1
    · simp [hw1]
    · by_cases hwv : w = v
      · subst w
        simp [hw1]
        omega
      · simp [hw1, hwv]
        have hwpos : 1 ≤ H.degree w := hdeg1 w
        have hw2 : 2 ≤ H.degree w := by omega
        omega
  have hsumle :
      (∑ w : α, ((2 : ℤ) - (H.degree w : ℤ))) ≤
        ∑ w : α, (if H.degree w = 1 then 1 else if w = v then -1 else 0) := by
    exact Finset.sum_le_sum (fun w _ => hterm w)
  rw [hsumZ] at hsumle
  have hsplit (w : α) :
      (if H.degree w = 1 then (1 : ℤ) else if w = v then -1 else 0) =
        (if H.degree w = 1 then 1 else 0) + (if w = v then -1 else 0) := by
    by_cases hw1 : H.degree w = 1
    · have hwv : w ≠ v := by
        rintro rfl
        omega
      simp [hw1, hwv]
    · simp [hw1]
  have hright :
      ∑ w : α, (if H.degree w = 1 then (1 : ℤ) else if w = v then -1 else 0) =
        ((Finset.univ.filter (fun w => H.degree w = 1)).card : ℤ) - 1 := by
    calc
      _ = ∑ w : α,
          ((if H.degree w = 1 then (1 : ℤ) else 0) + (if w = v then -1 else 0)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hsplit w
      _ = (∑ w : α, if H.degree w = 1 then (1 : ℤ) else 0) +
          (∑ w : α, if w = v then (-1 : ℤ) else 0) := Finset.sum_add_distrib
      _ = ((Finset.univ.filter (fun w => H.degree w = 1)).card : ℤ) - 1 := by
            simpa [sub_eq_add_neg]
  rw [hright] at hsumle
  have hLeavesZ : ((Finset.univ.filter (fun w => H.degree w = 1)).card : ℤ) ≤ 2 := by
    exact_mod_cast hLeaves
  omega

/-- A finite connected graph of maximum degree at most two has a Hamiltonian path. -/
@[category test, AMS 5]
theorem hasHamiltonianPath_of_connected_degree_le_two
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (hH : H.Connected) (hdeg : ∀ v, H.degree v ≤ 2) :
    HasHamiltonianPath H := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ :=
    Walk.exists_isPath_forall_isPath_length_le_length H
  refine ⟨u, v, p, hp.isHamiltonian_of_mem ?_⟩
  intro w
  by_contra hw
  obtain ⟨q, hq⟩ := hH.exists_isPath u w
  obtain ⟨d, hd, hdx, hdy⟩ :=
    q.exists_boundary_dart {x | x ∈ p.support} (by simp) (by simpa)
  simp only [Set.mem_setOf_eq] at hdx hdy
  by_cases hxu : d.fst = u
  · have hyu : H.Adj d.snd u := by simpa [hxu] using d.adj.symm
    have hnew : (p.cons hyu).IsPath := hp.cons hdy
    have := hmax d.snd v (p.cons hyu) hnew
    simp at this
  by_cases hxv : d.fst = v
  · have hvy : H.Adj v d.snd := by simpa [hxv] using d.adj
    have hnew : (p.concat hvy).IsPath := hp.concat hdy hvy
    have := hmax u d.snd (p.concat hvy) hnew
    simp at this
  obtain ⟨p₁, p₂, hp₁, hp₂, hp_eq⟩ :=
    hp.mem_support_iff_exists_append.mp hdx
  have hp_app : (p₁.append p₂).IsPath := hp_eq ▸ hp
  have hp₁_ne : ¬p₁.Nil := Walk.not_nil_of_ne (Ne.symm hxu)
  have hp₂_ne : ¬p₂.Nil := Walk.not_nil_of_ne hxv
  have hxa : H.Adj d.fst p₁.penultimate := (p₁.adj_penultimate hp₁_ne).symm
  have hxb : H.Adj d.fst p₂.snd := p₂.adj_snd hp₂_ne
  have ha₁ : p₁.penultimate ∈ p₁.support := p₁.getVert_mem_support _
  have hb₂ : p₂.snd ∈ p₂.support := p₂.getVert_mem_support 1
  have hab : p₁.penultimate ≠ p₂.snd :=
    hp_app.ne_of_mem_support_of_append hxb.ne' ha₁ hb₂
  have ha : p₁.penultimate ∈ p.support := by
    rw [hp_eq]
    exact p₁.subset_support_append_left p₂ ha₁
  have hb : p₂.snd ∈ p.support := by
    rw [hp_eq]
    exact p₁.subset_support_append_right p₂ hb₂
  have hay : p₁.penultimate ≠ d.snd := fun h ↦ hdy (h ▸ ha)
  have hby : p₂.snd ≠ d.snd := fun h ↦ hdy (h ▸ hb)
  have hsub :
      ({p₁.penultimate, p₂.snd, d.snd} : Finset α) ⊆ H.neighborFinset d.fst := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simpa using hxa
    · simpa using hxb
    · simpa using d.adj
  have hcard := Finset.card_le_card hsub
  have hthree : ({p₁.penultimate, p₂.snd, d.snd} : Finset α).card = 3 := by
    simp [hab, hay, hby]
  rw [hthree, H.card_neighborFinset_eq_degree] at hcard
  have := hdeg d.fst
  omega

/-- The `Ls ≤ 2` branch of Conjecture 217. -/
@[category test, AMS 5]
theorem hasHamiltonianPath_of_Ls_le_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hL : Ls G ≤ 2) :
    HasHamiltonianPath G := by
  classical
  obtain ⟨T, hTspan, hTtree, hTleaves⟩ :=
    exists_spanningTree_leafCount_le_two G hG hL
  have hTreeSpan : IsTree T.spanningCoe :=
    (T.spanningCoeEquivCoeOfSpanning hTspan).isTree_iff.mpr hTtree
  have hLeavesSpan :
      (Finset.univ.filter (fun v => T.spanningCoe.degree v = 1)).card ≤ 2 := by
    simpa [hTspan.verts_eq_univ] using hTleaves
  have hdegSpan : ∀ v, T.spanningCoe.degree v ≤ 2 :=
    tree_degree_le_two_of_leafCount_le_two T.spanningCoe hTreeSpan hLeavesSpan
  obtain ⟨a, b, p, hp⟩ :=
    hasHamiltonianPath_of_connected_degree_le_two T.spanningCoe hTreeSpan.isConnected hdegSpan
  let f : T.spanningCoe →g G := Hom.ofLE T.spanningCoe_le
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact hxy
    · intro y
      exact ⟨y, rfl⟩
  exact ⟨f a, f b, p.map f, hp.map f hf⟩

/-- The exact conjecture follows once its two mathematical branches are supplied. -/
@[category test, AMS 5]
theorem conjecture217_of_branch_theorems
    (hNonResidue :
      ∀ (H : SimpleGraph α) [DecidableRel H.Adj],
        H.Connected → Ls H ≤ 2 → HasHamiltonianPath H)
    (hResidueTwo :
      ∀ (H : SimpleGraph α) [DecidableRel H.Adj],
        H.Connected → residue H = 2 → Ls H ≤ 6 → HasHamiltonianPath H)
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    HasHamiltonianPath G := by
  by_cases hr : residue G = 2
  · exact hResidueTwo G h hr (Ls_le_six_of_residue_eq_two G hL hr)
  · exact hNonResidue G h (Ls_le_two_of_residue_ne_two G hL hr)

end WrittenOnTheWallII.GraphConjecture217
