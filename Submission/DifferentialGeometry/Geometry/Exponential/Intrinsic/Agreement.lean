import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.Radial
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Uniqueness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem intrinsicGeodesic_initial
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    IsGeodesicOnWithInitial (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p v) _root_.Set.univ p v := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p v
  refine ⟨DifferentialGeometry.velocityLift (I := I) γ,
    DifferentialGeometry.velocityLift_proj (I := I) γ, ?_, ?_⟩
  · apply TotalSpace.ext (intrinsicGeodesic_zero (I := I) g hEnorm p v)
    exact heq_of_eq (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v)
  · exact isMIntegralCurveOn_velocityLift (I := I) g isOpen_univ
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn _root_.Set.univ)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_initial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_initial target :: scope.openDecls } }

theorem expDomain_eq_univ_of_completeSpace
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    expDomain (I := I) g p = univ := by
  classical
  apply _root_.Set.eq_univ_of_forall
  intro v
  by_cases hdim : Module.finrank ℝ E = 0
  · have hsub : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).mp hdim
    have hv : v = 0 := @Subsingleton.elim E hsub v 0
    rw [hv]
    exact zero_mem_expDomain (I := I) g p
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact ⟨intrinsicGeodesic (I := I) g hEnorm p v, _root_.Set.univ,
      isOpen_univ, _root_.PreconnectedSpace.isPreconnected_univ, _root_.Set.mem_univ _, _root_.Set.mem_univ _,
      intrinsicGeodesic_initial (I := I) g hEnorm p v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.expDomain_eq_univ_of_completeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.expDomain_eq_univ_of_completeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.expDomain_eq_univ_of_completeSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.expDomain_eq_univ_of_completeSpace

theorem maximalGeodesic_eq_intrinsicGeodesic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v = intrinsicGeodesic (I := I) g hEnorm p v := by
  funext t
  exact maximalGeodesic_eqOn g isOpen_univ _root_.PreconnectedSpace.isPreconnected_univ (_root_.Set.mem_univ _)
    (intrinsicGeodesic_initial (I := I) g hEnorm p v) (_root_.Set.mem_univ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eq_intrinsicGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eq_intrinsicGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eq_intrinsicGeodesic ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.maximalGeodesic_eq_intrinsicGeodesic

theorem expMap_eq_expMapIntrinsic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    expMap (I := I) g p = expMapIntrinsic (I := I) g hEnorm p := by
  funext v
  exact congrFun (maximalGeodesic_eq_intrinsicGeodesic (I := I) g hEnorm p v) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic

theorem radialCurve_eq_intrinsicGeodesic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    VolumeComparison.radialCurve (I := I) g p v =
      intrinsicGeodesic (I := I) g hEnorm p v := by
  funext t
  exact (expMap_smul (I := I) g p v t).trans
    (congrFun (maximalGeodesic_eq_intrinsicGeodesic (I := I) g hEnorm p v) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.radialCurve_eq_intrinsicGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.radialCurve_eq_intrinsicGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.radialCurve_eq_intrinsicGeodesic ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.radialCurve_eq_intrinsicGeodesic

end DifferentialGeometry.Geometry.Riemannian.Exponential
