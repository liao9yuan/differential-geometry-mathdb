/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEssentialDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskCompression

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one
    (h252 : Moise252) (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hSc : IsConnected S.space) {U H T : Set E} (hU : IsOpen U) (hSU : S.space ⊆ U)
    (hH : IsPreconnected H) (hT : IsPreconnected T) (hHU : H ⊆ Uᶜ) (hTU : T ⊆ Uᶜ)
    (hsep : Separates S.space H T) (x : S.space) (g : FundamentalGroup S.space x)
    (hg : g ≠ 1) (hmap : FundamentalGroup.map
      (⟨Set.inclusion hSU, continuous_inclusion hSU⟩ : C(S.space, U)) x g = 1) :
    ∃ (P : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite),
      letI := hPfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsConnected P.space ∧ IsOrientable 2 P ∧
      IsTwoSided P.space ∧ P.space ⊆ U ∧ Separates P.space H T ∧
      Homology.bettiOne P.space < Homology.bettiOne S.space := by
  obtain ⟨D, r, hr, hDU, hmeet, _, hnon⟩ :=
    hS.exists_essential_disk_in_neighborhood_of_fundamentalGroup_map_eq_one
      h252 S hdim hSc hU hSU x g hg hmap
  obtain ⟨N, W, D₀, D₁, _, ρ, r₀, r₁, hN, hNU, _, _, _, _, _, _, hwall, _, _, _,
    hρ, hzero, _, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hS.exists_compression_neighborhood_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨P, hPfin, hP, hPc, hPo, hPt, hPsub, hPsep, hβ, _⟩ :=
    hS.exists_separating_component_bettiOne_lt_of_spanning_disk S hSc hdim
      hr hmeet hnon hρ hzero hN hwall hr₀ hr₁ hdis hfront hmeet₀ hmeet₁ hbd₀ hbd₁
      hH hT hsep (fun y hy hyN => hHU hy (hNU hyN))
      (fun y hy hyN => hTU hy (hNU hyN))
  have hremain : closure (S.space \ W) ⊆ U :=
    (closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space S).isClosed).trans hSU
  have hcaps : D₀ ∪ D₁ ⊆ U := by
    intro y hy
    apply hNU
    apply hN.isPolyhedron.isClosed.frontier_subset
    rw [hfront]
    exact hy.elim (fun h => Or.inl (Or.inr h)) Or.inr
  exact ⟨P, hPfin, hP, hPc, hPo, hPt,
    hPsub.trans (_root_.Set.union_subset (_root_.Set.union_subset hremain (subset_union_left.trans hcaps))
      (subset_union_right.trans hcaps)), hPsep, hβ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one

theorem IsCombinatorialManifold.fundamentalGroup_map_injective_of_bettiOne_min
    (h252 : Moise252) (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hdim : Module.finrank ℝ E = 3)
    (hSc : IsConnected S.space) {U H T : Set E} (hU : IsOpen U) (hSU : S.space ⊆ U)
    (hH : IsPreconnected H) (hT : IsPreconnected T) (hHU : H ⊆ Uᶜ) (hTU : T ⊆ Uᶜ)
    (hsep : Separates S.space H T)
    (hmin : ∀ (P : Geometry.SimplicialComplex ℝ E), P.faces.Finite →
      IsCombinatorialManifold 2 P → IsConnected P.space → P.space ⊆ U →
      Separates P.space H T → Homology.bettiOne S.space ≤ Homology.bettiOne P.space)
    (x : S.space) :
    Function.Injective (FundamentalGroup.map
      (⟨Set.inclusion hSU, continuous_inclusion hSU⟩ : C(S.space, U)) x) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  by_contra hne
  obtain ⟨P, hPfin, hP, hPc, _, _, hPU, hPsep, hβ⟩ :=
    hS.exists_separating_surface_bettiOne_lt_of_fundamentalGroup_map_eq_one
      h252 S hdim hSc hU hSU hH hT hHU hTU hsep x g hne hg
  exact (not_lt_of_ge (hmin P hPfin hP hPc hPU hPsep)) hβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.fundamentalGroup_map_injective_of_bettiOne_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.fundamentalGroup_map_injective_of_bettiOne_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.fundamentalGroup_map_injective_of_bettiOne_min ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.fundamentalGroup_map_injective_of_bettiOne_min

end DifferentialGeometry.Topology.PiecewiseLinear
