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
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Replace edges `v-y` and `x-z` by `v-x` and `y-z`.  Diagonal pairs are automatically discarded
by `fromEdgeSet`; the degree-preservation theorem below assumes the four vertices are distinct. -/
def twoSwitch (G : SimpleGraph α) (v x y z : α) : SimpleGraph α :=
  (G.deleteEdges ({s(v, y), s(x, z)} : Set (Sym2 α))) ⊔
    SimpleGraph.fromEdgeSet ({s(v, x), s(y, z)} : Set (Sym2 α))

@[category test, AMS 5]
theorem twoSwitch_adj_iff (G : SimpleGraph α) [DecidableRel G.Adj]
    (v x y z a b : α) :
    (twoSwitch G v x y z).Adj a b ↔
      (G.Adj a b ∧ s(a, b) ≠ s(v, y) ∧ s(a, b) ≠ s(x, z)) ∨
      ((s(a, b) = s(v, x) ∨ s(a, b) = s(y, z)) ∧ a ≠ b) := by
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj]

section Distinct

variable (G : SimpleGraph α) [DecidableRel G.Adj]
variable {v x y z : α}
variable (hvx : v ≠ x) (hvz : v ≠ z) (hxy : x ≠ y) (hyz : y ≠ z)
variable (hvy : G.Adj v y) (hxz : G.Adj x z)
variable (hvxN : ¬G.Adj v x) (hyzN : ¬G.Adj y z)

@[category test, AMS 5]
theorem neighborFinset_twoSwitch_v :
    (twoSwitch G v x y z).neighborFinset v =
      insert x ((G.neighborFinset v).erase y) := by
  ext w
  have hvy' : v ≠ y := hvy.ne
  have hxz' : x ≠ z := hxz.ne
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq,
    hvx, hvx.symm, hvz, hvz.symm, hxy, hxy.symm, hyz, hyz.symm,
    hvy', hvy'.symm, hxz', hxz'.symm, hvxN]

@[category test, AMS 5]
theorem neighborFinset_twoSwitch_x :
    (twoSwitch G v x y z).neighborFinset x =
      insert v ((G.neighborFinset x).erase z) := by
  ext w
  have hvy' : v ≠ y := hvy.ne
  have hxz' : x ≠ z := hxz.ne
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq,
    hvx, hvx.symm, hvz, hvz.symm, hxy, hxy.symm, hyz, hyz.symm,
    hvy', hvy'.symm, hxz', hxz'.symm, hvxN]

@[category test, AMS 5]
theorem neighborFinset_twoSwitch_y :
    (twoSwitch G v x y z).neighborFinset y =
      insert z ((G.neighborFinset y).erase v) := by
  ext w
  have hvy' : v ≠ y := hvy.ne
  have hxz' : x ≠ z := hxz.ne
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq,
    hvx, hvx.symm, hvz, hvz.symm, hxy, hxy.symm, hyz, hyz.symm,
    hvy', hvy'.symm, hxz', hxz'.symm, hyzN]

@[category test, AMS 5]
theorem neighborFinset_twoSwitch_z :
    (twoSwitch G v x y z).neighborFinset z =
      insert y ((G.neighborFinset z).erase x) := by
  ext w
  have hvy' : v ≠ y := hvy.ne
  have hxz' : x ≠ z := hxz.ne
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq,
    hvx, hvx.symm, hvz, hvz.symm, hxy, hxy.symm, hyz, hyz.symm,
    hvy', hvy'.symm, hxz', hxz'.symm, hyzN]

@[category test, AMS 5]
theorem neighborFinset_twoSwitch_other {w : α}
    (hwv : w ≠ v) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    (twoSwitch G v x y z).neighborFinset w = G.neighborFinset w := by
  ext a
  have hvy' : v ≠ y := hvy.ne
  have hxz' : x ≠ z := hxz.ne
  simp [twoSwitch, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq,
    hvx, hvx.symm, hvz, hvz.symm, hxy, hxy.symm, hyz, hyz.symm,
    hvy', hvy'.symm, hxz', hxz'.symm,
    hwv, hwv.symm, hwx, hwx.symm, hwy, hwy.symm, hwz, hwz.symm]

/-- A valid 2-switch preserves every vertex degree. -/
@[category test, AMS 5]
theorem twoSwitch_degree_eq (w : α) :
    (twoSwitch G v x y z).degree w = G.degree w := by
  by_cases hwv : w = v
  · subst w
    rw [← G.card_neighborFinset_eq_degree, ← (twoSwitch G v x y z).card_neighborFinset_eq_degree,
      neighborFinset_twoSwitch_v G hvx hvz hxy hyz hvy hxz hvxN hyzN]
    have hxnot : x ∉ G.neighborFinset v := by simpa using hvxN
    have hyin : y ∈ G.neighborFinset v := by simpa using hvy
    simp [hxnot, hyin]
  by_cases hwx : w = x
  · subst w
    rw [← G.card_neighborFinset_eq_degree, ← (twoSwitch G v x y z).card_neighborFinset_eq_degree,
      neighborFinset_twoSwitch_x G hvx hvz hxy hyz hvy hxz hvxN hyzN]
    have hvnot : v ∉ G.neighborFinset x := by simpa [G.adj_comm] using hvxN
    have hzin : z ∈ G.neighborFinset x := by simpa using hxz
    simp [hvnot, hzin]
  by_cases hwy : w = y
  · subst w
    rw [← G.card_neighborFinset_eq_degree, ← (twoSwitch G v x y z).card_neighborFinset_eq_degree,
      neighborFinset_twoSwitch_y G hvx hvz hxy hyz hvy hxz hvxN hyzN]
    have hznot : z ∉ G.neighborFinset y := by simpa using hyzN
    have hvin : v ∈ G.neighborFinset y := by simpa using hvy.symm
    simp [hznot, hvin]
  by_cases hwz : w = z
  · subst w
    rw [← G.card_neighborFinset_eq_degree, ← (twoSwitch G v x y z).card_neighborFinset_eq_degree,
      neighborFinset_twoSwitch_z G hvx hvz hxy hyz hvy hxz hvxN hyzN]
    have hynot : y ∉ G.neighborFinset z := by simpa [G.adj_comm] using hyzN
    have hxin : x ∈ G.neighborFinset z := by simpa using hxz.symm
    simp [hynot, hxin]
  · rw [← G.card_neighborFinset_eq_degree, ← (twoSwitch G v x y z).card_neighborFinset_eq_degree,
      neighborFinset_twoSwitch_other G hvx hvz hxy hyz hvy hxz hvxN hyzN hwv hwx hwy hwz]

end Distinct

end WrittenOnTheWallII.GraphConjecture217
