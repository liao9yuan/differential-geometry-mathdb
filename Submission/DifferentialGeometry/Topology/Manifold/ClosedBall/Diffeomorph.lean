import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

private local instance closedCellCharts : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.closedCellCharts
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.closedCellCharts target :: scope.openDecls } }

private local instance closedCellSmooth : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.closedCellSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.closedCellSmooth target :: scope.openDecls } }

variable (D : EuclideanSpace ℝ (Fin (m + 1)) ≃ₘ⟮𝓡 (m + 1), 𝓡 (m + 1)⟯
    EuclideanSpace ℝ (Fin (m + 1)))
  (hD : D '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)

include hD in
private theorem norm_le_one_iff (x : EuclideanSpace ℝ (Fin (m + 1))) : ‖x‖ ≤ 1 ↔ ‖D x‖ ≤ 1 := by
  have h : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ↔
      D x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    constructor
    · intro hx
      rw [← hD]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hD] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact D.injective hxy ▸ hy
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.norm_le_one_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.norm_le_one_iff target :: scope.openDecls } }

def closedCellDiffeomorph :
    ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1) where
  toEquiv := D.toEquiv.subtypeEquiv (norm_le_one_iff D hD)
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨(D.continuous.comp continuous_subtype_val).subtype_mk _,
      D.contMDiff.comp (isSmoothEmbedding_closedCell_inclusion m).contMDiff⟩
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨(D.symm.continuous.comp continuous_subtype_val).subtype_mk _,
      D.symm.contMDiff.comp (isSmoothEmbedding_closedCell_inclusion m).contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph

@[simp] theorem closedCellDiffeomorph_apply (x : ClosedCell (m + 1)) :
    (closedCellDiffeomorph D hD x).val = D x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_apply

@[simp] theorem closedCellDiffeomorph_symm_apply (x : ClosedCell (m + 1)) :
    ((closedCellDiffeomorph D hD).symm x).val = D.symm x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_symm_apply

theorem closedCellDiffeomorph_eq_self_iff (x : ClosedCell (m + 1)) :
    closedCellDiffeomorph D hD x = x ↔ D x.val = x.val :=
  Subtype.ext_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_iff ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_iff

theorem closedCellDiffeomorph_eq_self_of_norm_le {r : ℝ}
    (hfix : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ r → D y = y) (x : ClosedCell (m + 1))
    (hx : ‖x.val‖ ≤ r) : closedCellDiffeomorph D hD x = x :=
  (closedCellDiffeomorph_eq_self_iff D hD x).mpr (hfix x.val hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_of_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_of_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_of_norm_le ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_eq_self_of_norm_le

theorem closedCellDiffeomorph_cellBoundaryInclusion (a : CellBoundary (m + 1) → CellBoundary (m + 1))
    (ha : ∀ z : CellBoundary (m + 1), D z.val = (a z).val) (z : CellBoundary (m + 1)) :
    closedCellDiffeomorph D hD (cellBoundaryInclusion (m + 1) z) =
      cellBoundaryInclusion (m + 1) (a z) :=
  Subtype.ext (ha z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_cellBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_cellBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_cellBoundaryInclusion ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_cellBoundaryInclusion

theorem closedCellDiffeomorph_boundary_eq_self
    (hfix : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ = 1 → D y = y) (z : CellBoundary (m + 1)) :
    closedCellDiffeomorph D hD (cellBoundaryInclusion (m + 1) z) =
      cellBoundaryInclusion (m + 1) z :=
  Subtype.ext (hfix z.val z.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_boundary_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_boundary_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_boundary_eq_self ``Submission.DifferentialGeometry.Topology.Manifold.closedCellDiffeomorph_boundary_eq_self

end DifferentialGeometry.Topology.Manifold
