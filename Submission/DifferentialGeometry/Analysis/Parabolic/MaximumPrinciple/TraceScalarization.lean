import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.Trace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem parabolicOperatorWithDrift_trace
    [BoundarylessManifold I M]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible) (hsmooth : _root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (x : M) (X : ℝ → (y : M) → TangentSpace I y)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableWithinAt ℝ (fun q => A q x) (_root_.Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
      (fun q y => LinearMap.trace ℝ (V y) (A q y).toLinearMap) t x =
      LinearMap.trace ℝ (V x)
        (derivWithin (fun q => A q x) (_root_.Set.Icc 0 T) t -
          rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x -
          HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
            (fun y => A t y) x (X t x)).toLinearMap := by
  let : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  let L₀ : (V x →L[ℝ] V x) →ₗ[ℝ] ℝ :=
    { toFun := fun B => LinearMap.trace ℝ (V x) B.toLinearMap
      map_add' := by intro B C; simp
      map_smul' := by intro a B; simp }
  let L : (V x →L[ℝ] V x) →L[ℝ] ℝ := L₀.toContinuousLinearMap
  have htime : derivWithin (fun q => LinearMap.trace ℝ (V x) (A q x).toLinearMap)
      (_root_.Set.Icc 0 T) t = LinearMap.trace ℝ (V x)
        (derivWithin (fun q => A q x) (_root_.Set.Icc 0 T) t).toLinearMap := by
    exact (L.hasFDerivAt.comp_hasDerivWithinAt t hAt.hasDerivWithinAt).derivWithin
      ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)
  have hAspace : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) 2
      (fun y => (⟨y, A t y⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))) :=
    (A t).contMDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hlap : laplacianAt (I := I) G t
      (fun y => LinearMap.trace ℝ (V y) (A t y).toLinearMap) x =
      LinearMap.trace ℝ (V x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) cov (fun y => A t y) x).toLinearMap := by
    unfold laplacianAt
    rw [hGconn]
    exact (trace_rawBundleEndomorphismConnLap_eq_laplacian_of_isMetricCompatible
      (G.metric t) cov hcov hsmooth (fun y => A t y) hAspace x).symm
  have hdrift : driftTerm (I := I) G t (X t)
      (fun y => LinearMap.trace ℝ (V y) (A t y).toLinearMap) x =
      LinearMap.trace ℝ (V x)
        (HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
          (fun y => A t y) x (X t x)).toLinearMap := by
    unfold driftTerm gradientAt
    rw [(G.metric t).symm, inner_gradientFun]
    exact HomConnectionGen.mvfderiv_trace_of_isMetricCompatible cov hcov
      ((A t).contMDiff.mdifferentiableAt (by simp)) (X t x)
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [htime, hlap, hdrift]
  simp only [ContinuousLinearMap.toLinearMap_sub, map_sub]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift_trace ``Submission.DifferentialGeometry.Analysis.Parabolic.parabolicOperatorWithDrift_trace

end DifferentialGeometry.Analysis.Parabolic
