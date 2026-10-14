/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.Conjugate
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.image_conjugateHomeomorph {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M}
    (hS : IsPLCellOn d S B) {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source)
    (Φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hΦ : IsPLHomeomorphOn Φ _root_.Set.univ _root_.Set.univ) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ c.target) (hfix : _root_.Set.EqOn Φ id Kᶜ) :
    IsPLCellOn d ((c.conjugateHomeomorph Φ hK hKc hfix) '' S)
      ((c.conjugateHomeomorph Φ hK hKc hfix) '' B) := by
  have hmaps : _root_.Set.MapsTo Φ c.target c.target := by
    intro x hx
    by_contra hn
    have hnK : Φ x ∉ K := fun hxK => hn (hKc hxK)
    have heq : Φ x = x := Φ.injective (hfix hnK)
    exact hn (by rwa [heq])
  obtain ⟨q, hq, hB⟩ := hS.exists_isPLHomeomorphOn_image_chart hc hSc
  have hball : IsPLBall d (c '' S) := ⟨q, hq⟩
  have hr := hq.trans (hΦ.restrict hball.isPolyhedron (_root_.Set.subset_univ _))
  have hR : IsPolyhedron (Φ '' (c '' S)) := (IsPLBall.isPolyhedron ⟨Φ ∘ q, hr⟩)
  have hRc : Φ '' (c '' S) ⊆ c.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hmaps (c.map_source (hSc hx))
  have himg : ∀ A ⊆ S,
      (c.conjugateHomeomorph Φ hK hKc hfix) '' A = c.symm '' (Φ '' (c '' A)) := by
    intro A hAS
    rw [← _root_.Set.image_comp, ← _root_.Set.image_comp]
    apply _root_.Set.image_congr
    intro x hx
    exact c.conjugateMap_of_mem Φ (hSc (hAS hx))
  refine ⟨Φ '' (c '' S), Φ ∘ q, c.symm, hr,
    isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hR hRc, himg S Subset.rfl, ?_⟩
  rw [himg B hS.boundary_subset, _root_.Set.image_comp, ← hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_conjugateHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_conjugateHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_conjugateHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.image_conjugateHomeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
