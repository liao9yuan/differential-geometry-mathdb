import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Metric
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Smoothness
import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Submission.DifferentialGeometry.Geometry.Metric.Construction.Existence
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance modelCovectorAddCommGroup : AddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.addCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.modelCovectorAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.modelCovectorAddCommGroup target :: scope.openDecls } }

private local instance modelBilinearAddCommGroup :
    AddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.addCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.modelBilinearAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.modelBilinearAddCommGroup target :: scope.openDecls } }

def normalBall (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Opens E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x), Metric.isOpen_ball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalBall ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalBall

noncomputable def normalExpPD
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    PartialDiffeomorph 𝓘(Real, E) I E Y.M (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let Φ := expMapDiffeo (I := I) Y.metric x
  let U : _root_.TopologicalSpace.Opens E := normalBall (I := I) Y x
  have hU : (U : Set E) ⊆ Φ.source := by
    intro v hv
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
      (by simpa [U, normalBall, Metric.mem_ball, dist_zero_right] using hv)
  have himage : (Φ : E → Y.M) '' (U : Set E) =
      (fun v : E ↦
        (expMap (I := I) Y.metric x (show TangentSpace I x from v) : Y.M)) ''
        (U : Set E) := by
    apply _root_.Set.image_congr
    intro v hv
    exact expMapDiffeo_apply_eq (I := I) Y.metric x (hU hv)
  exact
    { toPartialEquiv :=
        { toFun := Φ
          invFun := normalChartAt (I := I) Y.metric x
          source := U
          target := (Φ : E → Y.M) '' (U : Set E)
          map_source' := by
            intro v hv
            exact ⟨v, hv, rfl⟩
          map_target' := by
            rintro q ⟨v, hv, rfl⟩
            have hleft : normalChartAt (I := I) Y.metric x ((Φ : E → Y.M) v) = v :=
              Φ.left_inv' (hU hv)
            rw [hleft]
            exact hv
          left_inv' := by
            intro v hv
            exact Φ.left_inv' (hU hv)
          right_inv' := by
            rintro q ⟨v, hv, rfl⟩
            have hleft : normalChartAt (I := I) Y.metric x ((Φ : E → Y.M) v) = v :=
              Φ.left_inv' (hU hv)
            rw [hleft] }
      open_source := U.2
      open_target := image_opens_isOpen Φ hU
      contMDiffOn_toFun := by
        have h := exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x
        have hfun :
            (Φ : E → Y.M) = fun w : E ↦ expMapDiffeo (I := I) Y.metric x w := by
          funext w
          rfl
        have hset : (U : Set E) = Metric.ball 0 (expMapC2Radius (I := I) Y.metric x) :=
          rfl
        rw [hfun, hset]
        exact h
      contMDiffOn_invFun := by
        have hsm := normal_chart_at_cont_mdiff_on_infty (I := I) Y.metric x
        have hsm' : ContMDiffOn I 𝓘(Real, E) ∞
            (normalChartAt (I := I) Y.metric x) ((Φ : E → Y.M) '' (U : Set E)) := by
          rw [himage]
          have hset : (U : Set E) =
              Metric.ball 0 (expMapC2Radius (I := I) Y.metric x) := rfl
          rw [hset]
          exact hsm
        exact hsm' }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalExpPD then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalExpPD"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalExpPD ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalExpPD

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem normalExpPD_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalExpPD (I := I) Y x).source = normalBall (I := I) Y x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalExpPD_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalExpPD_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalExpPD_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalExpPD_source

omit [NeZero (Module.finrank ℝ E)] in
private theorem normalBall_sub
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalBall (I := I) Y x : Set E) ⊆
      (normalExpPD (I := I) Y x).source := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [normalExpPD_source]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalBall_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.normalBall_sub target :: scope.openDecls } }

def normalImage
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Opens Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨(normalExpPD (I := I) Y x : E → Y.M) ''
      (normalBall (I := I) Y x : Set E),
    image_opens_isOpen (normalExpPD (I := I) Y x)
      (normalBall_sub (I := I) Y x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalImage ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalImage

noncomputable def normalBallDiffeo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Diffeomorph 𝓘(Real, E) I (normalBall (I := I) Y x)
      (normalImage (I := I) Y x)
      (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  unfold normalImage
  exact PartialDiffeomorph.toOpensDiffeo (normalExpPD (I := I) Y x)
    (normalBall_sub (I := I) Y x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalBallDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalBallDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalBallDiffeo ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalBallDiffeo

omit [NeZero (Module.finrank ℝ E)] in
private theorem normalBallSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalBall (I := I) Y x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : LocallyCompactSpace (normalBall (I := I) Y x) :=
    (normalBall (I := I) Y x).2.locallyCompactSpace
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalBallSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.normalBallSigma target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem normalImageSigma
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SigmaCompactSpace (normalImage (I := I) Y x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (normalBallDiffeo (I := I) Y x :
      normalBall (I := I) Y x → normalImage (I := I) Y x) = Set.univ :=
    Set.range_eq_univ.mpr (normalBallDiffeo (I := I) Y x).surjective
  rw [← hrange]
  exact isSigmaCompact_range (normalBallDiffeo (I := I) Y x).continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalImageSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.normalImageSigma target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem ballDiffeo_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ((normalBallDiffeo (I := I) Y x z : normalImage (I := I) Y x) : Y.M) =
      expMapDiffeo (I := I) Y.metric x (z : E) := by
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.ballDiffeo_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.ballDiffeo_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private theorem ballDiffeo_mfd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    mfderiv 𝓘(Real, E) I
        (normalBallDiffeo (I := I) Y x :
          normalBall (I := I) Y x → normalImage (I := I) Y x) z
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v) =
      mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (z : E)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) (z : E)).symm v) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have h := PartialDiffeomorph.mfderiv_toOpensDiffeo
    (normalExpPD (I := I) Y x) (normalBall_sub (I := I) Y x) z
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
  rw [show (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) =
    (expMapDiffeo (I := I) Y.metric x : E → Y.M) by rfl]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.ballDiffeo_mfd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.ballDiffeo_mfd target :: scope.openDecls } }

noncomputable def normalMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SmoothRiemannianMetric 𝓘(Real, E) (normalBall (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  letI : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  exact Diffeomorph.pullbackMetricCross
    (Y.metric.restrictOpen (I := I) (normalImage (I := I) Y x))
    (normalBallDiffeo (I := I) Y x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalMetric

omit [NeZero (Module.finrank ℝ E)] in
theorem normalMetric_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : normalBall (I := I) Y x) (v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalMetric (I := I) Y x).inner z
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w) =
      normalCoordMetric (I := I) Y x z v w := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  let : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  rw [normalMetric, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [ballDiffeo_apply, ballDiffeo_mfd, ballDiffeo_mfd]
  exact (normal_coord_metric_apply (I := I) Y x (z : E) v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalMetric_inner ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalMetric_inner

noncomputable def normalCut
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffBump (0 : E) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let R := expMapC2Radius (I := I) Y.metric x
  have hR : 0 < R := expMapC2Radius_pos (I := I) Y.metric x
  exact ⟨R / 4, R / 2, by positivity, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalCut then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalCut"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalCut ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalCut

omit [NeZero (Module.finrank Real E)] in
theorem normalCut_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ (normalCut (I := I) Y x : E → Real) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (normalCut (I := I) Y x).contDiff.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalCut_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalCut_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalCut_smooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalCut_smooth

omit [NeZero (Module.finrank Real E)] in
theorem normalCut_range
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (z : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalCut (I := I) Y x : E → Real) z ∈ Set.Icc (0 : Real) 1 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ⟨(normalCut (I := I) Y x).nonneg, (normalCut (I := I) Y x).le_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalCut_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalCut_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalCut_range ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalCut_range

omit [NeZero (Module.finrank Real E)] in
theorem normalCut_support
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    tsupport (normalCut (I := I) Y x : E → Real) ⊆
      (normalBall (I := I) Y x : Set E) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [(normalCut (I := I) Y x).tsupport_eq]
  change Metric.closedBall (0 : E) (expMapC2Radius (I := I) Y.metric x / 2) ⊆
    Metric.ball 0 (expMapC2Radius (I := I) Y.metric x)
  exact Metric.closedBall_subset_ball (by
    have hR := expMapC2Radius_pos (I := I) Y.metric x
    linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalCut_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalCut_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalCut_support ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalCut_support

omit [NeZero (Module.finrank Real E)] in
theorem normalCut_one
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ {z : E}, z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
      (normalCut (I := I) Y x : E → Real) z = 1 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  apply (normalCut (I := I) Y x).one_of_mem_closedBall
  exact Metric.ball_subset_closedBall hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalCut_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalCut_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalCut_one ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalCut_one

omit [NeZero (Module.finrank Real E)] in
theorem normalInner_sub
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4) ⊆
      (normalBall (I := I) Y x : Set E) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  change Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4) ⊆
    Metric.ball 0 (expMapC2Radius (I := I) Y.metric x)
  exact Metric.ball_subset_ball (by
    have hR := expMapC2Radius_pos (I := I) Y.metric x
    linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalInner_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalInner_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalInner_sub ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalInner_sub

private noncomputable def modelFlatMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    SmoothRiemannianMetric 𝓘(Real, E) E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  let B : E →L[Real] E →L[Real] Real := normalCoordMetric (I := I) Y x 0
  let Bt (y : E) :
      TangentSpace 𝓘(Real, E) y →L[Real] TangentSpace 𝓘(Real, E) y →L[Real] Real :=
    let e := (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y).toContinuousLinearMap
    (((B.comp e).flip.comp e).flip)
  have hBt (y : E) (v w : TangentSpace 𝓘(Real, E) y) :
      Bt y v w =
        B (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y v)
          (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y w) := rfl
  have hBsymm : ∀ v w : E, B v w = B w v := by
    intro v w
    dsimp only [B]
    rw [normal_coord_metric_zero (I := I)]
    exact Y.metric.symm x v w
  have hBpos : ∀ v : E, v ≠ 0 → 0 < B v v := by
    intro v hv
    dsimp only [B]
    rw [normal_coord_metric_zero (I := I)]
    exact Y.metric.pos x v hv
  exact
    { inner := Bt
      symm := by
        intro y v w
        rw [hBt, hBt, hBsymm]
      pos := by
        intro y v hv
        rw [hBt]
        apply hBpos
        intro heq
        apply hv
        apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y).injective
        simpa using heq
      isVonNBounded := fun y ↦
        DifferentialGeometry.Geometry.posDef_isVonNBounded
          (Bt y) (by
            intro v hv
            rw [hBt]
            apply hBpos
            intro heq
            apply hv
            apply (tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) y).injective
            simpa using heq)
      contMDiff := by
        intro y
        rw [_root_.Bundle.contMDiffAt_section]
        refine (contMDiffAt_const (x := y) (c := B)).congr_of_eventuallyEq ?_
        filter_upwards [
          (_root_.FiberBundle.trivializationAt E (TangentSpace (modelWithCornersSelf Real E)) y).open_baseSet.mem_nhds
            (_root_.FiberBundle.mem_baseSet_trivializationAt E
              (TangentSpace (modelWithCornersSelf Real E)) y)] with q hq
        ext v w
        rw [DifferentialGeometry.Geometry.metricCoeffInModel_apply
          (I := _) y hq (Bt q) v w]
        rw [TangentBundle.symmL_model_space]
        rw [hBt]
        change B v w = B v w
        rfl }

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.modelFlatMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.modelFlatMetric target :: scope.openDecls } }

noncomputable def normalTotal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    SmoothRiemannianMetric 𝓘(Real, E) E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  exact (modelFlatMetric (I := I) Y x).bumpExtendOpen
    (normalBall (I := I) Y x) (normalMetric (I := I) Y x)
    (normalCut (I := I) Y x : E → Real)
    (normalCut_smooth (I := I) Y x) (normalCut_range (I := I) Y x)
    (normalCut_support (I := I) Y x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalTotal ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalTotal

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTotal_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) → ∀ v w : E,
      (normalTotal (I := I) Y x).inner z
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w) =
        normalCoordMetric (I := I) Y x z v w := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : SigmaCompactSpace (normalBall (I := I) Y x) :=
    normalBallSigma (I := I) Y x
  let : SigmaCompactSpace (normalImage (I := I) Y x) :=
    normalImageSigma (I := I) Y x
  intro z hz v w
  have hsub := normalInner_sub (I := I) Y x
  let zU : normalBall (I := I) Y x := ⟨z, hsub hz⟩
  have hv : (show TangentSpace 𝓘(Real, E) zU from
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v) =
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm v := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).injective
    simp only [      tangentSpaceModelContinuousLinearEquiv_symm_apply]
  have hw : (show TangentSpace 𝓘(Real, E) zU from
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w) =
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm w := by
    apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).injective
    simp only [      tangentSpaceModelContinuousLinearEquiv_symm_apply]
  calc
    (normalTotal (I := I) Y x).inner z
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w) =
        (normalMetric (I := I) Y x).inner zU
          (show TangentSpace 𝓘(Real, E) zU from
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
          (show TangentSpace 𝓘(Real, E) zU from
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w) := by
      simpa only [normalTotal] using
        bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
          (modelFlatMetric (I := I) Y x) (normalBall (I := I) Y x)
          (normalMetric (I := I) Y x) (normalCut (I := I) Y x : E → Real)
          (normalCut_smooth (I := I) Y x) (normalCut_range (I := I) Y x)
          (normalCut_support (I := I) Y x)
          (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x / 4))
          (fun q hq ↦ normalCut_one (I := I) Y x hq) hsub z hz
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm w)
    _ = (normalMetric (I := I) Y x).inner zU
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm v)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) zU).symm w) := by
      rw [hv, hw]
    _ = normalCoordMetric (I := I) Y x z v w :=
      normalMetric_inner (I := I) Y x zU v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalTotal_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalTotal_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalTotal_inner ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalTotal_inner

omit [NeZero (Module.finrank ℝ E)] in
theorem normalTotal_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
      tangentBilinearFormToModel z ((normalTotal (I := I) Y x).inner z) =
        normalCoordMetric (I := I) Y x z := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [tangentBilinearFormToModel_apply]
  exact normalTotal_inner (I := I) Y x z hz v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normalTotal_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normalTotal_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normalTotal_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.normalTotal_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_cov_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
    ∀ (hco : IsCoercive (normalCoordMetric (I := I) Y x z)) (v w : E),
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
          (I := 𝓘(Real, E)) (normalTotal (I := I) Y x)
          (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)) =
      MetricKoszul.koszulVec hco
        (fderiv Real (normalCoordMetric (I := I) Y x) z) v w := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco v w
  have hsub := normalInner_sub (I := I) Y x
  have hB : (fun y : E ↦
      tangentBilinearFormToModel y ((normalTotal (I := I) Y x).inner y)) =ᶠ[nhds z]
        normalCoordMetric (I := I) Y x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact normalTotal_eq (I := I) Y x y hy
  have hdiff : DifferentiableAt Real (normalCoordMetric (I := I) Y x) z := by
    exact ((normal_coord_metric_cont_diff_on_exp_ball (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact DifferentialGeometry.Geometry.Connection.const_cov_eq_nhds
    (normalTotal (I := I) Y x) (normalCoordMetric (I := I) Y x)
    hB hdiff hco v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_cov_eq_fderiv
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E), z ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
    ∀ (hco : IsCoercive (normalCoordMetric (I := I) Y x z))
      (V : E → E)
      (_hV : MDifferentiableAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E))
        (fun y : E ↦
          (⟨y, (tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) y).symm (V y)⟩ :
              TangentBundle 𝓘(Real, E) E)) z)
      (v : E),
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
          (I := 𝓘(Real, E)) (normalTotal (I := I) Y x)
          (fun y : E ↦
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y).symm (V y)) z)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm v)) =
      fderiv Real V z v +
        MetricKoszul.koszulVec hco
          (fderiv Real (normalCoordMetric (I := I) Y x) z) v (V z) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco V _hV v
  have hsub := normalInner_sub (I := I) Y x
  have hB : (fun y : E ↦
      tangentBilinearFormToModel y ((normalTotal (I := I) Y x).inner y)) =ᶠ[nhds z]
        normalCoordMetric (I := I) Y x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact normalTotal_eq (I := I) Y x y hy
  have hdiff : DifferentiableAt Real (normalCoordMetric (I := I) Y x) z := by
    exact ((normal_coord_metric_cont_diff_on_exp_ball (I := I) Y x).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact DifferentialGeometry.Geometry.Connection.cov_eq_fderiv_add
    (normalTotal (I := I) Y x) (normalCoordMetric (I := I) Y x)
    hB hdiff hco V _hV v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq_fderiv ``Submission.DifferentialGeometry.CheegerGromovCompactness.normal_cov_eq_fderiv

end CheegerGromovCompactness
end DifferentialGeometry
