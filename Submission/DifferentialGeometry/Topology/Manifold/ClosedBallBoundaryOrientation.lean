import Submission.DifferentialGeometry.Topology.Manifold.HypersurfaceOrientation
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBallOrientation
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Module _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Ball target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private def b2 : _root_.Module.Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.b2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.b2 target :: scope.openDecls } }
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.i2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.i2 target :: scope.openDecls } }

def radialSphereNormalFrame {L : ℝ} (hL : 0 < L) (y : S2) : (ℝ × E2) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans
    ((PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
      (euclideanPolarDiffeomorph (E := E3) (n := 2)) (x := (y, L)) hL).mfderivToContinuousLinearEquiv (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame ``Submission.DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame

theorem radialSphereNormalFrame_apply {L : ℝ} (hL : 0 < L) (y : S2) (t : ℝ) (v : E2) :
    radialSphereNormalFrame hL y (t, v) = t • y.val + L • dIncl (n := 2) y v :=
  euclideanPolarMap_mfderiv (y, L) (v, t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame_apply ``Submission.DifferentialGeometry.Topology.Manifold.radialSphereNormalFrame_apply

private def scaledSphere (L : ℝ) (y : S2) : E3 := L • y.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.scaledSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.scaledSphere target :: scope.openDecls } }
private def sphereNormal (y : S2) : E3 := y.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphereNormal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphereNormal target :: scope.openDecls } }
private theorem scaledSphere_smooth (L : ℝ) : ContMDiff (𝓡 2) (𝓡 3) ∞ (scaledSphere L) := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun _ : S2 => L) := contMDiff_const
  exact hc.smul hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.scaledSphere_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.scaledSphere_smooth target :: scope.openDecls } }
private def scaledSphereDifferential (L : ℝ) (y : S2) : E2 →L[ℝ] E3 :=
  mfderiv (𝓡 2) (𝓡 3) (scaledSphere L) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.scaledSphereDifferential
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.scaledSphereDifferential target :: scope.openDecls } }
private theorem scaledSphere_derivative (L : ℝ) (y : S2) :
    scaledSphereDifferential L y = L • dIncl (n := 2) y := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : S2 → E3) := contMDiff_coe_sphere (n := 2)
  have h := mvfderiv_fun_smul (I := 𝓡 2)
    (mdifferentiableAt_const (c := L) (x := y)) (hs.mdifferentiableAt (by simp) (x := y))
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at h
  change mvfderiv (𝓡 2) (fun z : S2 => L • z.val) y = L • mvfderiv (𝓡 2) (Subtype.val : S2 → E3) y
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.scaledSphere_derivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.scaledSphere_derivative target :: scope.openDecls } }
private theorem sphereNormal_continuous : Continuous sphereNormal := continuous_subtype_val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphereNormal_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphereNormal_continuous target :: scope.openDecls } }
private theorem sphere_frame_eq {L : ℝ} (hL : 0 < L) (y : S2) :
    hypersurfaceNormalFrame (scaledSphere L) sphereNormal y = (radialSphereNormalFrame hL y : (ℝ × E2) →L[ℝ] E3) := by
  apply ContinuousLinearMap.ext
  intro v
  change v.1 • sphereNormal y + scaledSphereDifferential L y v.2 = _
  rw [scaledSphere_derivative]
  exact (radialSphereNormalFrame_apply hL y v.1 v.2).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphere_frame_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphere_frame_eq target :: scope.openDecls } }
private theorem sphere_frame_bijective {L : ℝ} (hL : 0 < L) (y : S2) :
    Bijective (hypersurfaceNormalFrame (scaledSphere L) sphereNormal y) := by
  rw [sphere_frame_eq hL y]
  exact (radialSphereNormalFrame hL y).bijective

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphere_frame_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphere_frame_bijective target :: scope.openDecls } }
private theorem sphere_frame_equiv {L : ℝ} (hL : 0 < L) (y : S2) :
    (hypersurfaceNormalFrameEquiv (scaledSphere L) sphereNormal (sphere_frame_bijective hL) y).toLinearEquiv =
      (radialSphereNormalFrame hL y).toLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun A : (ℝ × E2) →L[ℝ] E3 => A v) (sphere_frame_eq hL y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphere_frame_equiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphere_frame_equiv target :: scope.openDecls } }

def radialSphereSmoothOrientation {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    SmoothOrientation (𝓡 2) S2 :=
  hypersurfaceSmoothOrientation (scaledSphere L) sphereNormal (scaledSphere_smooth L)
    sphereNormal_continuous (sphere_frame_bijective hL) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation

theorem radialSphereSmoothOrientation_apply {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin 3)) (y : S2) :
    (radialSphereSmoothOrientation hL o).val y = Orientation.reindex ℝ E2 i2
      (normalFirstOrientation (radialSphereNormalFrame hL y).toLinearEquiv b2 o) := by
  change (hypersurfaceSmoothOrientation (scaledSphere L) sphereNormal (scaledSphere_smooth L)
    sphereNormal_continuous (sphere_frame_bijective hL) o).val y = _
  rw [hypersurfaceSmoothOrientation_apply, sphere_frame_equiv hL y]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.radialSphereSmoothOrientation_apply

def closedBallBoundaryAmbient {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E3 := by
  let := closedBallChartedSpace hL
  exact fun b => b.val.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryAmbient ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryAmbient

def closedBallBoundaryRadialNormal {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E3 := by
  let := closedBallChartedSpace hL
  exact fun b => L⁻¹ • b.val.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal

private theorem boundary_ambient_smooth {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ContMDiff (𝓡 2) (𝓡 3) ∞ (closedBallBoundaryAmbient hL) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact (isSmoothEmbedding_closedBall_inclusion hL).contMDiff.comp
    (boundaryInclusion_contMDiff (I := 𝓡∂ 3) (M := Ball L))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundary_ambient_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundary_ambient_smooth target :: scope.openDecls } }
private theorem boundary_normal_continuous {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    Continuous (closedBallBoundaryRadialNormal hL) := by
  let := closedBallChartedSpace hL
  change Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => L⁻¹ • b.val.val)
  have hb : Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => b.val.val) :=
    (show Continuous (Subtype.val : Ball L → E3) from continuous_subtype_val).comp
      (show Continuous (fun b : BoundaryManifold (𝓡∂ 3) (Ball L) => b.val) from continuous_subtype_val)
  exact hb.const_smul L⁻¹

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundary_normal_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundary_normal_continuous target :: scope.openDecls } }

theorem closedBallBoundaryRadialNormal_outward {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      ‖closedBallBoundaryRadialNormal hL b‖ = 1 ∧
      ∀ s : ℝ, 0 < s → L < ‖closedBallBoundaryAmbient hL b + s • closedBallBoundaryRadialNormal hL b‖ := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  let y := closedBallBoundaryDiffeomorph hL b
  have hn : closedBallBoundaryRadialNormal hL b = y.val := rfl
  have ha : closedBallBoundaryAmbient hL b = L • y.val := by
    change b.val.val = L • (L⁻¹ • b.val.val)
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hy : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
  refine ⟨hn ▸ hy, ?_⟩
  intro s hs
  rw [ha, hn, ← add_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hL hs), hy, mul_one]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal_outward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal_outward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal_outward ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryRadialNormal_outward

private def boundaryDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡 3) (closedBallBoundaryAmbient hL) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundaryDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundaryDerivative target :: scope.openDecls } }
private def boundaryNormalizationDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 ≃L[ℝ] E2 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => (closedBallBoundaryDiffeomorph hL).mfderivToContinuousLinearEquiv (by simp) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundaryNormalizationDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundaryNormalizationDerivative target :: scope.openDecls } }

private theorem boundary_derivative_chain {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      boundaryDerivative hL b = (scaledSphereDifferential L (closedBallBoundaryDiffeomorph hL b)).comp
        (boundaryNormalizationDerivative hL b : E2 →L[ℝ] E2) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  have he : scaledSphere L ∘ closedBallBoundaryDiffeomorph hL = closedBallBoundaryAmbient hL := by
    funext x
    change L • (L⁻¹ • x.val.val) = x.val.val
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have h := mfderiv_comp b ((scaledSphere_smooth L).mdifferentiableAt (by simp))
    ((closedBallBoundaryDiffeomorph hL).contMDiff.mdifferentiableAt (by simp))
  rw [he] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundary_derivative_chain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundary_derivative_chain target :: scope.openDecls } }

private theorem boundary_frame_eq {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      hypersurfaceNormalFrame (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL) b =
        ((((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b)).trans
          (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b))) : (ℝ × E2) →L[ℝ] E3) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  apply ContinuousLinearMap.ext
  intro v
  change v.1 • closedBallBoundaryRadialNormal hL b + boundaryDerivative hL b v.2 = _
  rw [boundary_derivative_chain hL b, scaledSphere_derivative]
  exact (radialSphereNormalFrame_apply hL (closedBallBoundaryDiffeomorph hL b) v.1
    (boundaryNormalizationDerivative hL b v.2)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundary_frame_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundary_frame_eq target :: scope.openDecls } }

theorem closedBallBoundaryNormalFrame_bijective {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      Bijective (hypersurfaceNormalFrame (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL) b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rw [boundary_frame_eq hL b]
  exact (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b)).trans
    (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b))).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryNormalFrame_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryNormalFrame_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryNormalFrame_bijective ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryNormalFrame_bijective

def closedBallBoundarySmoothOrientation {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    SmoothOrientation (𝓡 2) (BoundaryManifold (𝓡∂ 3) (Ball L)) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact hypersurfaceSmoothOrientation (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL)
    (boundary_ambient_smooth hL) (boundary_normal_continuous hL) (closedBallBoundaryNormalFrame_bijective hL) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation

theorem closedBallBoundarySmoothOrientation_apply {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      (closedBallBoundarySmoothOrientation hL o).val b = Orientation.reindex ℝ E2 i2
        (normalFirstOrientation (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
          (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv b2 o) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_apply

private theorem map_reindex (A : E2 ≃ₗ[ℝ] E2) (q : Orientation ℝ E2 (Fin 2)) :
    Orientation.map (Fin (Module.finrank ℝ E2)) A (Orientation.reindex ℝ E2 i2 q) =
      Orientation.reindex ℝ E2 i2 (Orientation.map (Fin 2) A q) := by
  induction q using Module.Ray.ind
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.map_reindex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.map_reindex target :: scope.openDecls } }

theorem closedBallBoundarySmoothOrientation_normalization {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      tangentOrientationEquiv ((closedBallBoundaryDiffeomorph hL).mfderivToContinuousLinearEquiv (by simp) b).toLinearEquiv
        ((closedBallBoundarySmoothOrientation hL o).val b) =
          (radialSphereSmoothOrientation hL o).val (closedBallBoundaryDiffeomorph hL b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  have he : (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
      (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv =
      ((LinearEquiv.refl ℝ ℝ).prodCongr (boundaryNormalizationDerivative hL b).toLinearEquiv).trans
        (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b)).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun A : (ℝ × E2) →L[ℝ] E3 => A v) (boundary_frame_eq hL b)
  change tangentOrientationEquiv (boundaryNormalizationDerivative hL b).toLinearEquiv
    ((closedBallBoundarySmoothOrientation hL o).val b) = _
  rw [closedBallBoundarySmoothOrientation_apply, radialSphereSmoothOrientation_apply, tangentOrientationEquiv_self,
    map_reindex, he, normalFirstOrientation_change_boundary
      (radialSphereNormalFrame hL (closedBallBoundaryDiffeomorph hL b)).toLinearEquiv
      (boundaryNormalizationDerivative hL b).toLinearEquiv b2 b2 o]
  congr 1
  rw [← Orientation.map_symm, Equiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_normalization ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_normalization
end DifferentialGeometry.Topology.Manifold
