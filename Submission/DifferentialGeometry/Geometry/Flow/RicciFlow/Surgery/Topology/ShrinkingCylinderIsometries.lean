import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinderGauge
import Submission.DifferentialGeometry.Geometry.Neck.BufferedRotation
import Submission.DifferentialGeometry.Geometry.Neck.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Neck

private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry target :: scope.openDecls } }

theorem shrinkingCylinderMetric_eq_flow (t : Set.Iio (1 : ℝ)) :
    shrinkingCylinderMetric t =
      DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t.val := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hs := (Classical.choose_spec (exists_unique_shrinkingCylinderMetric t)).1 x v w
  have hf := DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner t.property x v w
  apply hs.trans
  apply Eq.trans _ hf.symm
  unfold shrinkingCylinderInner
  have hfst (u : TangentSpace NeckCylinderModel x) :
      mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x u =
        dIncl x.1 u.1 := by
    rw [show (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) =
      ((↑) : Sphere 2 → ThreeSpace) ∘ Prod.fst from rfl]
    rw [mfderiv_comp x
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).mdifferentiableAt
        (by simp)) mdifferentiableAt_fst, mfderiv_fst]
    rfl
  rw [hfst v, hfst w, mfderiv_snd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_eq_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_eq_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_eq_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_eq_flow

theorem pullback_shrinkingCylinderMetric_bufferedCylinderRotation
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderRotation δ e) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [shrinkingCylinderMetric_eq_flow]
  apply DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial
    (bufferedCylinder δ) (bufferedCylinder δ) (bufferedCylinderRotation δ e) _ t.property
  simpa only [DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero,
    referenceMetric] using
    pullback_referenceMetric_bufferedCylinderRotation δ e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderRotation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderRotation

theorem pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderRotation δ e) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  exact pullback_shrinkingCylinderMetric_bufferedCylinderRotation δ e t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation

theorem image_bufferedCylinderRotation_neckClosedTest
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    bufferedCylinderRotation δ e '' neckClosedTest δ = neckClosedTest δ :=
  image_bufferedCylinderRotation_controlledCylinder δ e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderRotation_neckClosedTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderRotation_neckClosedTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderRotation_neckClosedTest ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderRotation_neckClosedTest

theorem pullback_shrinkingCylinderMetric_bufferedCylinderOrientation
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderOrientation δ σ hσ) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [shrinkingCylinderMetric_eq_flow]
  apply DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial
    (bufferedCylinder δ) (bufferedCylinder δ) (bufferedCylinderOrientation δ σ hσ) _ t.property
  simpa only [DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero,
    referenceMetric] using
    pullback_referenceMetric_bufferedCylinderOrientation δ σ hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullback_shrinkingCylinderMetric_bufferedCylinderOrientation

theorem pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderOrientation δ σ hσ) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  exact pullback_shrinkingCylinderMetric_bufferedCylinderOrientation δ σ hσ t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation

theorem image_bufferedCylinderOrientation_neckClosedTest
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    bufferedCylinderOrientation δ σ hσ '' neckClosedTest δ = neckClosedTest δ :=
  image_bufferedCylinderOrientation_controlledCylinder δ σ hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderOrientation_neckClosedTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderOrientation_neckClosedTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderOrientation_neckClosedTest ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.image_bufferedCylinderOrientation_neckClosedTest

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
