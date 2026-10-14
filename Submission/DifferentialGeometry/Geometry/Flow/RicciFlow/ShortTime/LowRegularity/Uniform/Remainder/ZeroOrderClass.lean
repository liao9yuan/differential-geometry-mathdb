import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Remainder.ZeroOrderBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.DeTurck.RHSFirstDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

structure ZeroOrderNonlinearityParameters where
  zeroBd : ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ZeroOrderNonlinearityParameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ZeroOrderNonlinearityParameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ZeroOrderNonlinearityParameters ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ZeroOrderNonlinearityParameters

structure HasUniformZeroOrderNonlinearityBound
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (Z : ZeroOrderNonlinearityParameters) : Prop where
  zero_nonneg : 0 ≤ Z.zeroBd
  zero : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    ∀ {R δ : ℝ} (hR : 0 < R) (hδ : δ < 1)
      (hreal : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ)
      (_hcore : Continuous
        (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ hreal)),
      ‖deTurckRemainderOnLowerState (I := I) (M := M) g gBase hR hδ hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hR.le⟩‖ ≤ Z.zeroBd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasUniformZeroOrderNonlinearityBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasUniformZeroOrderNonlinearityBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasUniformZeroOrderNonlinearityBound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HasUniformZeroOrderNonlinearityBound

noncomputable def zeroOrderNonlinearityParameters
    (gBase : SmoothRiemannianMetric I M) (Λ Ksup : ℝ) : ZeroOrderNonlinearityParameters where
  zeroBd := zeroStateRemainderBound Ksup Λ
    ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
    (Module.finrank ℝ E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zeroOrderNonlinearityParameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zeroOrderNonlinearityParameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zeroOrderNonlinearityParameters ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zeroOrderNonlinearityParameters

theorem has_uniform_zero_order_nonlinearity_bound
    (gBase : SmoothRiemannianMetric I M) {Λ Ksup : ℝ}
    (hKsup : 0 ≤ Ksup)
    (hsup : ∀ g : SmoothRiemannianMetric I M,
      (∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v) →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g gBase Λ →
      ∀ j : ℕ, j ≤ 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((iteratedCovGrad (I := I) g 0 2 j
            (deTurckRHSSection (I := I) gBase g)).toSection x) ≤ Ksup ^ 2) :
    HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ
      (zeroOrderNonlinearityParameters (I := I) (M := M) gBase Λ Ksup) := by
  refine ⟨?_, ?_⟩
  · exact nZeroC_nonneg hKsup Λ
      ((riemannianVolumeMeasure (I := I) (M := M) gBase).real Set.univ)
      (Module.finrank ℝ E)
  · intro g hEq hjet R δ hR hδ hreal hcore
    have hcomp : ∀ (x : M) (v : TangentSpace I x),
        Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
          g.inner x v v ≤ Λ * gBase.inner x v v :=
      fun x v => hEq.2 x (Set.mem_univ x) v
    have hsupg := hsup g hcomp
      (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) (hjet 3 (by norm_num))
    simpa only [zeroOrderNonlinearityParameters] using
      zero_state_remainder_uniform_bound (I := I) (M := M) gBase g hR hδ hreal hcore hKsup hEq hsupg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.has_uniform_zero_order_nonlinearity_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.has_uniform_zero_order_nonlinearity_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.has_uniform_zero_order_nonlinearity_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.has_uniform_zero_order_nonlinearity_bound

theorem exists_uniform_zero_order_nonlinearity_parameters
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ Z : ZeroOrderNonlinearityParameters,
      HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ Z := by
  obtain ⟨Ksup, hKsup, hsup⟩ :=
    uniformKsupLeOne (I := I) (M := M) gBase hΛ
  exact ⟨zeroOrderNonlinearityParameters (I := I) (M := M) gBase Λ Ksup,
    has_uniform_zero_order_nonlinearity_bound (I := I) (M := M) gBase hKsup hsup⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_zero_order_nonlinearity_parameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_zero_order_nonlinearity_parameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_zero_order_nonlinearity_parameters ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_zero_order_nonlinearity_parameters

theorem zero_order_nonlinearity_bound_of_uniform_parameters
    {gBase : SmoothRiemannianMetric I M} {Λ : ℝ} {Z : ZeroOrderNonlinearityParameters}
    (hZ : HasUniformZeroOrderNonlinearityBound (I := I) (M := M) gBase Λ Z)
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hjet : ∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
    {δ Ctop B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ
      (lowRegularityMetricRealization (I := I) (M := M) g
        (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal))) :
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ Z.zeroBd := by
  simpa only [boundedDeTurckRemainderOnLowerState] using hZ.zero g hEq hjet
    (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ
    (lowRegularityMetricRealization (I := I) (M := M) g
      (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal) hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_order_nonlinearity_bound_of_uniform_parameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_order_nonlinearity_bound_of_uniform_parameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_order_nonlinearity_bound_of_uniform_parameters ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_order_nonlinearity_bound_of_uniform_parameters

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
