/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_subset_of_inter_closure_sdiff_subset {X : Type*} [TopologicalSpace X]
    {S A Ab B Bb : Set X} (hAS : A ⊆ S) (hA : A ⊆ closure (A \ Ab))
    (hB : B ∩ closure (S \ B) ⊆ Bb) (hAB : A ∩ B ⊆ Ab) : A ∩ B ⊆ Bb := by
  rintro y ⟨hyA, hyB⟩
  by_contra hyb
  have hyc : y ∈ (closure (S \ B))ᶜ := fun h => hyb (hB ⟨hyB, h⟩)
  obtain ⟨z, hzU, hzA, hzAb⟩ := mem_closure_iff_nhds.mp (hA hyA) _
    (isClosed_closure.isOpen_compl.mem_nhds hyc)
  have hzB : z ∈ B := by
    by_contra hzB
    exact hzU (subset_closure ⟨hAS hzA, hzB⟩)
  exact hzAb (hAB ⟨hzA, hzB⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_of_inter_closure_sdiff_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_of_inter_closure_sdiff_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_of_inter_closure_sdiff_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_subset_of_inter_closure_sdiff_subset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one {S D : Set E}
    (hS : IsPLSphere 1 S) {r : (Fin 2 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 2)) D) (hDS : D ⊆ S) :
    D ∩ closure (S \ D) = r '' stdSimplexBoundary 1 := by
  classical
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  rw [← hKS] at hS hDS ⊢
  exact IsCombinatorialManifold.inter_closure_sdiff_eq_image_stdSimplexBoundary (n := 0) K
    (IsPLSphere.isCombinatorialManifold (n := 0) hS) hr hDS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one

end DifferentialGeometry.Topology.PiecewiseLinear
