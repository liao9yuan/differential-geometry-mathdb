import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import Submission.DifferentialGeometry.Topology.Manifold.Components
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Manifold _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c : BallChart n I M) (U : TopologicalSpace.Opens M) (hU : c.chart.target ⊆ U)

include c hU in
private theorem restrictTarget_nonempty : Nonempty U :=
  ⟨⟨c.chart 0, hU (c.chart.map_source
    (c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))))⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.restrictTarget_nonempty target :: scope.openDecls } }

private def restrictTargetChart :
    _root_.PartialDiffeomorph (𝓡 n) I (EuclideanSpace ℝ (Fin n)) U ∞ :=
  c.chart.trans (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.restrictTargetChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.restrictTargetChart target :: scope.openDecls } }

private theorem restrictTargetChart_source : (c.restrictTargetChart U hU).source = c.chart.source := by
  change c.chart.source ∩ c.chart ⁻¹' (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).target = _
  have ht : (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).target = U :=
    U.openPartialHomeomorphSubtypeCoe_target _
  rw [ht]
  exact inter_eq_left.mpr fun x hx => hU (c.chart.map_source hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.restrictTargetChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.restrictTargetChart_source target :: scope.openDecls } }

private theorem restrictTargetChart_target : (c.restrictTargetChart U hU).target =
    (Subtype.val : U → M) ⁻¹' c.chart.target := by
  change (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).source ∩
    (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)) ⁻¹' c.chart.target = _
  have hs : (PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)).source = univ :=
    U.openPartialHomeomorphSubtypeCoe_source _
  rw [hs, _root_.Set.univ_inter]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.restrictTargetChart_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.restrictTargetChart_target target :: scope.openDecls } }

def restrictTarget : BallChart n I U where
  chart := c.restrictTargetChart U hU
  closedBall_subset_source := by
    rw [c.restrictTargetChart_source U hU]
    exact c.closedBall_subset_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.restrictTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.restrictTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.restrictTarget ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget

@[simp] theorem restrictTarget_source : (c.restrictTarget U hU).chart.source = c.chart.source :=
  c.restrictTargetChart_source U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.restrictTarget_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.restrictTarget_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.restrictTarget_source ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget_source

@[simp] theorem restrictTarget_target : (c.restrictTarget U hU).chart.target =
    (Subtype.val : U → M) ⁻¹' c.chart.target := c.restrictTargetChart_target U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.restrictTarget_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.restrictTarget_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.restrictTarget_target ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget_target

theorem restrictTarget_apply {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c.chart.source) :
    ((c.restrictTarget U hU).chart x).val = c.chart x := by
  let e := PartialDiffeomorph.subtypeVal (I := I) U (c.restrictTarget_nonempty U hU)
  have het : e.target = U := U.openPartialHomeomorphSubtypeCoe_target _
  have he : c.chart x ∈ e.target := by rw [het]; exact hU (c.chart.map_source hx)
  change (e.symm (c.chart x)).val = c.chart x
  exact e.right_inv' he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.restrictTarget_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.restrictTarget_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.restrictTarget_apply ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget_apply


theorem restrictTarget_mfderiv {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c.chart.source) :
    mfderiv (𝓡 n) I ((c.restrictTarget U hU).chart : EuclideanSpace ℝ (Fin n) → U) x =
      mfderiv (𝓡 n) I (c.chart : EuclideanSpace ℝ (Fin n) → M) x := by
  have heq : (fun y : EuclideanSpace ℝ (Fin n) => ((c.restrictTarget U hU).chart y).val)
      =ᶠ[𝓝 x] (c.chart : EuclideanSpace ℝ (Fin n) → M) := by
    filter_upwards [c.chart.open_source.mem_nhds hx] with y hy
    exact c.restrictTarget_apply U hU hy
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp]
  exact heq.mfderiv_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.restrictTarget_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.restrictTarget_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.restrictTarget_mfderiv ``Submission.DifferentialGeometry.Topology.BallChart.restrictTarget_mfderiv

end BallChart

namespace OrientedBallChart

variable {M : ClosedOrientedManifold 3} (c : OrientedBallChart M)
  (K : ConnectedComponents M.Carrier) (hK : c.chart.target ⊆ M.componentSet K)

def component : OrientedBallChart (M.component K).toClosedOrientedManifold where
  toBallChart := c.toBallChart.restrictTarget (M.componentOpen K) hK
  preserves_orientation := by
    intro x hx
    have hx' : x ∈ c.chart.source :=
      (c.toBallChart.restrictTarget_source (M.componentOpen K) hK) ▸ hx
    have heq : (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
        (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
          (c.toBallChart.restrictTarget (M.componentOpen K) hK).chart hx) (by simp)).toLinearEquiv =
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
          (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart hx') (by simp)).toLinearEquiv := by
      ext v
      exact congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v)
        (c.toBallChart.restrictTarget_mfderiv (M.componentOpen K) hK hx')
    erw [heq]
    have ho := c.preserves_orientation x hx'
    change _ = M.componentTangentOrientation K ((c.toBallChart.restrictTarget (M.componentOpen K) hK).chart x)
    rw [M.componentTangentOrientation_apply,
      c.toBallChart.restrictTarget_apply (M.componentOpen K) hK hx']
    exact ho

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.component ``Submission.DifferentialGeometry.Topology.OrientedBallChart.component

@[simp] theorem component_source : (c.component K hK).chart.source = c.chart.source :=
  c.toBallChart.restrictTarget_source (M.componentOpen K) hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.component_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.component_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.component_source ``Submission.DifferentialGeometry.Topology.OrientedBallChart.component_source

@[simp] theorem component_target : (c.component K hK).chart.target =
    (Subtype.val : (M.component K).Carrier → M.Carrier) ⁻¹' c.chart.target :=
  c.toBallChart.restrictTarget_target (M.componentOpen K) hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.component_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.component_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.component_target ``Submission.DifferentialGeometry.Topology.OrientedBallChart.component_target

theorem component_apply {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ c.chart.source) :
    ((c.component K hK).chart x).val = c.chart x :=
  c.toBallChart.restrictTarget_apply (M.componentOpen K) hK hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.component_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.component_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.component_apply ``Submission.DifferentialGeometry.Topology.OrientedBallChart.component_apply

end OrientedBallChart

end DifferentialGeometry.Topology
