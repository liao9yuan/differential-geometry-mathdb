/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CellFaceOrderOfInteriors
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCellRecognition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualFlagBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualInteriorSeparation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSource

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactDualCutCell_flag_incidence
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space) :
    (∀ l, compactDualCutBoundary M K hKM l =
      ⋃ m ∈ section34Face (compactDualCutCell M K hKM) l \ {l},
        compactDualCutCell M K hKM m) ∧
    (∀ l m, compactDualCutCell M K hKM l ∩ compactDualCutCell M K hKM m =
      ⋃ k ∈ section34Face (compactDualCutCell M K hKM) l ∩
        section34Face (compactDualCutCell M K hKM) m, compactDualCutCell M K hKM k) ∧
    ∀ l m, compactDualCutCell M K hKM m ⊆ compactDualCutCell M K hKM l →
      m = l ∨ section34BoundedDim m < section34BoundedDim l := by
  have hbd := compactDualCutBoundary_eq_iUnion_step M K hKM hM hK hint
  have hcell := isPLCellOn_compactDualCutCell M K hKM hM hK hint
  have hstep (m l : Section34CompactLabelOf K K) (h : Section34CompactCutStep m l) :
      compactDualCutCell M K hKM m ⊆ compactDualCutBoundary M K hKM l := by
    rw [hbd l]
    exact _root_.Set.subset_iUnion₂_of_subset m h subset_rfl
  exact boundary_inter_and_strict_of_disjoint_interiors section34CompactCutStep_dim_lt hstep
    (fun l => (hbd l).subset) (fun l => (hcell l).boundary_subset)
    (fun l => (hcell l).sdiff_boundary_nonempty)
    (compactDualCutCell_inter_subset_boundaries M K hM hK hKM hint hstep)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutCell_flag_incidence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutCell_flag_incidence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutCell_flag_incidence ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutCell_flag_incidence

end DifferentialGeometry.Topology.PiecewiseLinear
