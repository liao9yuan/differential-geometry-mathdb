import Submission.DifferentialGeometry.Topology.Handle.Manifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.Handle

private local instance _root_.Submission.DifferentialGeometry.Topology.Handle.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

theorem closedCell_chartAt_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) :
    chartAt (EuclideanHalfSpace (m + 1)) α = closedCellInteriorChart m := by
  change closedCellChartAt α = _
  rw [closedCellChartAt, dif_pos hα]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.closedCell_chartAt_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.closedCell_chartAt_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.closedCell_chartAt_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Handle.closedCell_chartAt_of_norm_lt_one

theorem closedCell_extChartAt_apply_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (x : ClosedCell (m + 1)) :
    extChartAt (𝓡∂ (m + 1)) α x = closedCellShiftSucc m 1 x.val := by
  change (closedCellChartAt α x).val = _
  rw [closedCellChartAt, dif_pos hα]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_apply_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.closedCell_extChartAt_apply_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_apply_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Handle.closedCell_extChartAt_apply_of_norm_lt_one

theorem closedCell_extChartAt_source_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) :
    (extChartAt (𝓡∂ (m + 1)) α).source =
      {x : ClosedCell (m + 1) | ‖x.val‖ < 1} := by
  rw [extChartAt_source,
    closedCell_chartAt_of_norm_lt_one α hα]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_source_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.closedCell_extChartAt_source_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_source_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Handle.closedCell_extChartAt_source_of_norm_lt_one

theorem closedCell_extChartAt_symm_val_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (z : EuclideanSpace ℝ (Fin (m + 1)))
    (hz : z ∈ (extChartAt (𝓡∂ (m + 1)) α).target) :
    ((extChartAt (𝓡∂ (m + 1)) α).symm z).val =
      closedCellShiftSucc m (-1) z := by
  have he := (extChartAt (𝓡∂ (m + 1)) α).right_inv hz
  rw [closedCell_extChartAt_apply_of_norm_lt_one α hα] at he
  calc
    ((extChartAt (𝓡∂ (m + 1)) α).symm z).val =
        closedCellShiftSucc m (-1)
          (closedCellShiftSucc m 1
            ((extChartAt (𝓡∂ (m + 1)) α).symm z).val) :=
      (closedCellShiftSucc_neg_left_inv m 1 _).symm
    _ = closedCellShiftSucc m (-1) z :=
      congrArg (closedCellShiftSucc m (-1)) he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_symm_val_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.closedCell_extChartAt_symm_val_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.closedCell_extChartAt_symm_val_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Handle.closedCell_extChartAt_symm_val_of_norm_lt_one

theorem mem_closedCell_extChartAt_target_iff_of_norm_lt_one {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (z : EuclideanSpace ℝ (Fin (m + 1))) :
    z ∈ (extChartAt (𝓡∂ (m + 1)) α).target ↔
      ‖closedCellShiftSucc m (-1) z‖ < 1 := by
  constructor
  · intro hz
    have hs := (extChartAt (𝓡∂ (m + 1)) α).map_target hz
    rw [closedCell_extChartAt_source_of_norm_lt_one α hα] at hs
    change ‖((extChartAt (𝓡∂ (m + 1)) α).symm z).val‖ < 1 at hs
    rwa [closedCell_extChartAt_symm_val_of_norm_lt_one α hα z hz] at hs
  · intro hz
    let x : ClosedCell (m + 1) :=
      ⟨closedCellShiftSucc m (-1) z, hz.le⟩
    have hx : x ∈ (extChartAt (𝓡∂ (m + 1)) α).source := by
      rw [closedCell_extChartAt_source_of_norm_lt_one α hα]
      exact hz
    have ht := (extChartAt (𝓡∂ (m + 1)) α).map_source hx
    rw [closedCell_extChartAt_apply_of_norm_lt_one α hα] at ht
    change closedCellShiftSucc m 1 (closedCellShiftSucc m (-1) z) ∈
      (extChartAt (𝓡∂ (m + 1)) α).target at ht
    rwa [closedCellShiftSucc_neg_right_inv m 1 z] at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.mem_closedCell_extChartAt_target_iff_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.mem_closedCell_extChartAt_target_iff_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.mem_closedCell_extChartAt_target_iff_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Handle.mem_closedCell_extChartAt_target_iff_of_norm_lt_one

end DifferentialGeometry.Topology.Handle
