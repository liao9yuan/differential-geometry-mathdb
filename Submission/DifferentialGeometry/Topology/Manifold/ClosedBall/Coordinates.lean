import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

open _root_.Submission.DifferentialGeometry.Topology.Handle

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell ``Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) := closedCellIsManifold m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell ``Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell

theorem extChartAt_closedCell_eq_shift {x : ClosedCell (m + 1)} (hx : ‖x.val‖ < 1)
    (y : ClosedCell (m + 1)) :
    extChartAt (𝓡∂ (m + 1)) x y = closedCellShiftSucc m 1 y.val := by
  have hc : chartAt (EuclideanHalfSpace (m + 1)) x = closedCellInteriorChart m := by
    change closedCellChartAt x = _
    rw [closedCellChartAt, dif_pos hx]
  rw [extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply, hc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_eq_shift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_eq_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_eq_shift ``Submission.DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_eq_shift

theorem mfderiv_closedCell_inclusion_of_norm_lt_one
    {x : ClosedCell (m + 1)} (hx : ‖x.val‖ < 1) :
    mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1)) (Subtype.val : ClosedCell (m + 1) → EuN) x =
      ContinuousLinearMap.id ℝ EuN := by
  have heq : (Subtype.val : ClosedCell (m + 1) → EuN) =
      (fun y : EuN => y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)) ∘
        extChartAt (𝓡∂ (m + 1)) x := by
    funext y
    rw [Function.comp_apply, extChartAt_closedCell_eq_shift hx,
      ← closedCellShiftSucc_eq_add, closedCellShiftSucc_neg_left_inv]
  have ho : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1))
      (fun y : EuN => y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0))
      (extChartAt (𝓡∂ (m + 1)) x x) :=
    mdifferentiableAt_iff_differentiableAt.mpr (differentiableAt_id.add_const _)
  rw [heq, mfderiv_comp x ho (mdifferentiableAt_extChartAt (mem_chart_source _ x))]
  rw [mfderiv_extChartAt_self]
  ext v
  change mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
    (fun y : EuN => y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0))
    (extChartAt (𝓡∂ (m + 1)) x x) v = v
  rw [mfderiv_eq_fderiv]
  exact congrArg (fun L : EuN →L[ℝ] EuN => L v)
    ((hasFDerivAt_id (extChartAt (𝓡∂ (m + 1)) x x)).add_const
      ((-1 : ℝ) • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0))).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.mfderiv_closedCell_inclusion_of_norm_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.mfderiv_closedCell_inclusion_of_norm_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.mfderiv_closedCell_inclusion_of_norm_lt_one ``Submission.DifferentialGeometry.Topology.Manifold.mfderiv_closedCell_inclusion_of_norm_lt_one

theorem injective_mfderiv_closedCell_inclusion (x : ClosedCell (m + 1)) :
    Function.Injective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
      (Subtype.val : ClosedCell (m + 1) → EuN) x) :=
  ((isSmoothEmbedding_closedCell_inclusion m).isImmersion.isImmersionAt x).injective_mfderiv (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCell_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCell_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCell_inclusion ``Submission.DifferentialGeometry.Topology.Manifold.injective_mfderiv_closedCell_inclusion

theorem extChartAt_closedCell_symm_val {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1)
    {y : EuN} (hy : y ∈ (extChartAt (𝓡∂ (m + 1)) α).target) :
    ((extChartAt (𝓡∂ (m + 1)) α).symm y).val = closedCellShiftSucc m (-1) y := by
  have h := (extChartAt (𝓡∂ (m + 1)) α).right_inv hy
  rw [extChartAt_closedCell_eq_shift hα] at h
  have hh := congrArg (closedCellShiftSucc m (-1)) h
  rwa [closedCellShiftSucc_neg_left_inv] at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_symm_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_symm_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_symm_val ``Submission.DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_symm_val

theorem extChartAt_closedCell_target {α : ClosedCell (m + 1)} (hα : ‖α.val‖ < 1) :
    (extChartAt (𝓡∂ (m + 1)) α).target = {y : EuN | ‖closedCellShiftSucc m (-1) y‖ < 1} := by
  have hc : chartAt (EuclideanHalfSpace (m + 1)) α = closedCellInteriorChart m := by
    change closedCellChartAt α = _
    rw [closedCellChartAt, dif_pos hα]
  ext y
  constructor
  · intro hy
    have hs := (extChartAt (𝓡∂ (m + 1)) α).map_target hy
    rw [extChartAt_source, hc] at hs
    change ‖((extChartAt (𝓡∂ (m + 1)) α).symm y).val‖ < 1 at hs
    rwa [extChartAt_closedCell_symm_val hα hy] at hs
  · intro hy
    let x : ClosedCell (m + 1) := ⟨closedCellShiftSucc m (-1) y, hy.le⟩
    have hx : x ∈ (extChartAt (𝓡∂ (m + 1)) α).source := by
      rw [extChartAt_source, hc]
      exact hy
    have h := (extChartAt (𝓡∂ (m + 1)) α).map_source hx
    rwa [extChartAt_closedCell_eq_shift hα,
      show x.val = closedCellShiftSucc m (-1) y from rfl,
      closedCellShiftSucc_neg_right_inv] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_target ``Submission.DifferentialGeometry.Topology.Manifold.extChartAt_closedCell_target

end DifferentialGeometry.Topology.Manifold
