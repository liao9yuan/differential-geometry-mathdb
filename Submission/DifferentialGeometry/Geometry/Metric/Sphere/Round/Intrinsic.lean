import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.GreatCircle
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Metric _root_.Module _root_.Submission.Module
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereModel_neZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereModel_neZero target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem dIncl_orth (p : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    ⟪(p : E), dIncl (n := n) p v⟫ = 0 := by
  rw [real_inner_comm]
  apply Submodule.inner_left_of_mem_orthogonal
    (Submodule.mem_span_singleton_self (p : E))
  rw [← range_mvfderiv_subtypeVal (n := n) p]
  exact ⟨v, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl_orth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl_orth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl_orth ``Submission.DifferentialGeometry.Geometry.dIncl_orth

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable
  [RiemannianBundle
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]
  [PseudoEMetricSpace (sphere (0 : E) 1)]
  [@CompleteSpace (sphere (0 : E) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : E) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : E) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]

theorem intrinsic_eq_gc
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (t : ℝ) :
    intrinsicGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p v t =
      greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v) t := by
  let γi :=
    intrinsicGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n))
      hEnorm p v
  let γc := greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v)
  have hgc :
      IsGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n)) γc := by
    intro s
    exact greatCircle_geodesic (n := n) p (dIncl (n := n) p v)
      hv (dIncl_orth p v) s
  have heq : Set.EqOn γi γc Set.univ := by
    apply geo_eqOn_of_initial (I := 𝓡 n) (roundMetric (E := E) (n := n))
      isOpen_univ _root_.PreconnectedSpace.isPreconnected_univ (Set.mem_univ 0)
    · exact
        (intrinsicGeodesic_isGeodesic (I := 𝓡 n)
          (roundMetric (E := E) (n := n)) hEnorm p v).isGeodesicOn Set.univ
    · exact hgc.isGeodesicOn Set.univ
    · exact
        (intrinsicGeodesic_continuous (I := 𝓡 n)
          (roundMetric (E := E) (n := n)) hEnorm p v).continuousOn
    · exact
        (greatCircle_smooth (n := n) p (dIncl (n := n) p v)
          hv (dIncl_orth p v)).continuous.continuousOn
    · simp [γi, γc]
    · dsimp only [γi, γc]
      rw [intrinsicGeodesic_mfderiv_zero]
      apply injective_mvfderiv_subtypeVal_sphere p
      have hvel :=
        greatCircle_velocity (n := n) p (dIncl (n := n) p v)
          hv (dIncl_orth p v) 0
      rw [greatCircle_zero] at hvel
      change dIncl (n := n) p v = dIncl (n := n) p
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v)) 0 1)
      simp only [Real.sin_zero, neg_zero, zero_smul, Real.cos_zero, one_smul,
        zero_add] at hvel
      with_unfolding_all exact hvel.symm
  exact heq (Set.mem_univ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.intrinsic_eq_gc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.intrinsic_eq_gc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.intrinsic_eq_gc ``Submission.DifferentialGeometry.Geometry.intrinsic_eq_gc

theorem round_exp_radial
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (r : ℝ) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (r • v) =
      greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v) r := by
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  exact intrinsic_eq_gc hEnorm p v hv r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_exp_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_exp_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_exp_radial ``Submission.DifferentialGeometry.Geometry.round_exp_radial

theorem round_exp_val
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := _root_.Metric.sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : _root_.Metric.sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (r : ℝ) :
    ((expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (r • v) : _root_.Metric.sphere (0 : E) 1) : E) =
      Real.cos r • (p : E) + Real.sin r • dIncl (n := n) p v := by
  rw [round_exp_radial hEnorm p v hv r, greatCircle_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.round_exp_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.round_exp_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.round_exp_val ``Submission.DifferentialGeometry.Geometry.round_exp_val

end Geometry
end DifferentialGeometry
