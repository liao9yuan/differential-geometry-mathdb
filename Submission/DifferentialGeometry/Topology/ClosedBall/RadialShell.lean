import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev UnitShell (E : Type*) [NormedAddCommGroup E] (a : ℝ) :=
  {x : _root_.Metric.closedBall (0 : E) 1 // a < ‖(x : E)‖}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.UnitShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.UnitShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.UnitShell ``Submission.DifferentialGeometry.Topology.ClosedBall.UnitShell

variable {a : ℝ}

omit [NormedSpace ℝ E] in
private theorem unitShell_norm_pos (ha : 0 ≤ a) (x : UnitShell E a) : 0 < ‖(x.val : E)‖ :=
  ha.trans_lt x.property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShell_norm_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedBall.unitShell_norm_pos target :: scope.openDecls } }

omit [NormedSpace ℝ E] in
private theorem unitShell_norm_le_one (x : UnitShell E a) : ‖(x.val : E)‖ ≤ 1 := by
  simpa only [mem_closedBall_zero_iff] using x.val.property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShell_norm_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedBall.unitShell_norm_le_one target :: scope.openDecls } }

def unitShellRadialMap (ha : 0 ≤ a) : C(UnitShell E a, _root_.Metric.sphere (0 : E) 1) :=
  ⟨fun x => ⟨NormedSpace.normalize (x.val : E), mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (norm_pos_iff.mp (unitShell_norm_pos ha x)))⟩, by
    apply Continuous.subtype_mk
    have hval : Continuous (fun x : UnitShell E a => (x.val : E)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hval.norm.inv₀ (fun x => (unitShell_norm_pos ha x).ne')).smul hval⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap

@[simp] theorem unitShellRadialMap_apply (ha : 0 ≤ a) (x : UnitShell E a) :
    (unitShellRadialMap ha x : E) = ‖(x.val : E)‖⁻¹ • (x.val : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_apply ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_apply

omit [NormedSpace ℝ E] in
def sphereToUnitShell (ha₁ : a < 1) : C(_root_.Metric.sphere (0 : E) 1, UnitShell E a) := by
  refine ⟨fun x => ⟨⟨x.val, _root_.Metric.sphere_subset_closedBall x.property⟩, ?_⟩, ?_⟩
  · change a < ‖x.val‖
    rw [mem_sphere_zero_iff_norm.mp x.property]
    exact ha₁
  · exact (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell ``Submission.DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell

omit [NormedSpace ℝ E] in
@[simp] theorem sphereToUnitShell_apply (ha₁ : a < 1) (x : _root_.Metric.sphere (0 : E) 1) :
    ((sphereToUnitShell ha₁ x).val : E) = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell_apply ``Submission.DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell_apply

@[simp] theorem unitShellRadialMap_sphereToUnitShell (ha : 0 ≤ a) (ha₁ : a < 1) (x : _root_.Metric.sphere (0 : E) 1) :
    unitShellRadialMap ha (sphereToUnitShell ha₁ x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize x.val = x.val
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp x.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_sphereToUnitShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_sphereToUnitShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_sphereToUnitShell ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_sphereToUnitShell

private def unitShellRadialHomotopyPoint (ha : 0 ≤ a)
    (t : unitInterval) (x : UnitShell E a) : UnitShell E a := by
  let r := ‖(x.val : E)‖
  let k := (1 - (t : ℝ)) + (t : ℝ) * r⁻¹
  have hr : 0 < r := unitShell_norm_pos ha x
  have hrat : a < r := x.property
  have hr1 : r ≤ 1 := unitShell_norm_le_one x
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hk : 0 ≤ k := add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0 (inv_nonneg.mpr hr.le))
  have hnorm : ‖k • (x.val : E)‖ = (1 - (t : ℝ)) * r + (t : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg hk]
    change k * r = _
    dsimp [k]
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  refine ⟨⟨k • (x.val : E), ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, hnorm]
    nlinarith
  · change a < ‖k • (x.val : E)‖
    rw [hnorm]
    nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyPoint target :: scope.openDecls } }

def unitShellRadialDeformation (ha : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (UnitShell E a))
      ((sphereToUnitShell ha₁).comp (unitShellRadialMap ha))
      {x | ‖(x.val : E)‖ = 1} where
  toFun tx := unitShellRadialHomotopyPoint ha tx.1 tx.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hval : Continuous (fun p : unitInterval × UnitShell E a => (p.2.val : E)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : unitInterval × UnitShell E a => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).add
      (ht.mul (hval.norm.inv₀ (fun p => (unitShell_norm_pos ha p.2).ne')))).smul hval
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (0 : ℝ)) + 0 * ‖(x.val : E)‖⁻¹) • (x.val : E) = x.val
    simp
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (1 : ℝ)) + 1 * ‖(x.val : E)‖⁻¹) • (x.val : E) =
      ‖(x.val : E)‖⁻¹ • (x.val : E)
    simp
  prop' t x hx := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (t : ℝ)) + (t : ℝ) * ‖(x.val : E)‖⁻¹) • (x.val : E) = x.val
    change ‖(x.val : E)‖ = 1 at hx
    rw [hx, inv_one, mul_one, sub_add_cancel, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation

@[simp] theorem unitShellRadialDeformation_apply (ha : 0 ≤ a) (ha₁ : a < 1)
    (t : unitInterval) (x : UnitShell E a) :
    ((unitShellRadialDeformation ha ha₁ (t, x)).val : E) =
      ((1 - (t : ℝ)) + (t : ℝ) * ‖(x.val : E)‖⁻¹) • (x.val : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation_apply ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation_apply

def unitShellRadialHomotopyEquiv (ha : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousMap.HomotopyEquiv (UnitShell E a) (_root_.Metric.sphere (0 : E) 1) where
  toFun := unitShellRadialMap ha
  invFun := sphereToUnitShell ha₁
  left_inv := ⟨(unitShellRadialDeformation ha ha₁).toHomotopy.symm⟩
  right_inv := by
    have he : (unitShellRadialMap (E := E) ha).comp (sphereToUnitShell ha₁) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact unitShellRadialMap_sphereToUnitShell ha ha₁ x
    rw [he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyEquiv ``Submission.DifferentialGeometry.Topology.ClosedBall.unitShellRadialHomotopyEquiv

end DifferentialGeometry.Topology.ClosedBall
