/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem isTopologicalSphere_image_splitRim (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hc : e.card = 2) : IsTopologicalSphere 1 (h '' Dbd e) := by
  classical
  have hfin : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn ht.facesFinite
  have hNclosed : IsClosed N := by
    rw [ht.unionEq]
    exact hfin.isClosed_biUnion fun v hv => (ht.dualBall v hv).isPolyhedron.isClosed
  have hDbdN : Dbd e ⊆ N := by
    rw [← ht.splitProper e he hc]
    intro x hx
    rw [← hNclosed.closure_eq]
    exact frontier_subset_closure hx.2
  have hemb : _root_.Topology.IsEmbedding ((Dbd e).domRestrict h) := by
    have hemb' : _root_.Topology.IsEmbedding ((N.domRestrict h) ∘ Set.inclusion hDbdN) :=
      ht.isEmbedding.comp (Topology.IsEmbedding.inclusion hDbdN)
    convert hemb' using 1
    ext x
    rfl
  obtain ⟨r, hr, hDbd⟩ := ht.splitCell e he hc
  have hS : IsPLSphere 1 (Dbd e) := by
    rw [hDbd]
    exact hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨a⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hS
  let b : Dbd e ≃ₜ h '' Dbd e :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr (Set.range_domRestrict h (Dbd e)))
  let c : loopCircle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
      (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
        change z ∈ Metric.sphere (0 : ℂ) 1 ↔
          Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
        rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
          Complex.orthonormalBasisOneI.repr.norm_map])
  exact ⟨b.symm.trans (a.symm.trans c)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSphere_image_splitRim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSphere_image_splitRim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSphere_image_splitRim ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalSphere_image_splitRim

end DifferentialGeometry.Topology.PiecewiseLinear
