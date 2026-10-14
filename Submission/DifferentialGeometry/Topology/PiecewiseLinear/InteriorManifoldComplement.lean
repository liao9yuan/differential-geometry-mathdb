/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace IsCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem
    exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex 3 K).space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧ R.space = closure (K.space \ A.space) := by
  obtain ⟨T, hT, hTfin, hTA⟩ := exists_isSubdivision_restrict_isSubdivision K A hAK
  let _ : Finite T.faces := hTfin.to_subtype
  let B := restrict T A.space
  let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
  have hB : IsCombinatorialManifoldWithBoundary 3 B := hA.of_isSubdivision hTA
  have hBT : B.faces ⊆ T.faces := restrict_faces_subset T A.space
  have hBspace : B.space = A.space := hTA.space_eq
  have hdisT : Disjoint B.space (boundaryComplex 3 T).space := by
    rw [hBspace, boundaryComplex_space_of_isSubdivision K T hK hT]
    exact hdis
  have htrace : IsCombinatorialManifoldWithBoundary 2
      (restrict B (boundaryComplex 3 T).space) := by
    intro v hv
    exact (disjoint_left.mp hdisT
      (B.subset_space hv.1 (Finset.mem_singleton_self v))
      (hv.2 (subset_convexHull ℝ _ (Finset.mem_singleton_self v)))).elim
  refine ⟨subcomplexGeneratedBy T B.facesᶜ, subcomplexGeneratedBy_faces_finite T B.facesᶜ,
    (hK.of_isSubdivision hT).complement T B hB hBT htrace, ?_⟩
  rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl hBT,
    hT.space_eq, hBspace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary

end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
