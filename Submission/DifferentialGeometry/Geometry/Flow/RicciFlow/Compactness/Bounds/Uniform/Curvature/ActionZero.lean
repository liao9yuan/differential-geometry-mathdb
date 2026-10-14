import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.FirstJet

import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.FirstOrder.Bounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.UniformBochner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def uniformPtCurvZeroC (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  ptCurvZeroC d
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
    (rmOneOpC Λ Kb₀ Kb₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformPtCurvZeroC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformPtCurvZeroC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformPtCurvZeroC ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformPtCurvZeroC

noncomputable def uniformPtCurvThreeC (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  ptCurvRankC d 3
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
    (rmOneOpC Λ Kb₀ Kb₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformPtCurvThreeC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformPtCurvThreeC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformPtCurvThreeC ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformPtCurvThreeC

theorem uniformCurvAction0_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    IsCurvAction0 (I := I) (M := M) g₀ 2
      (uniformPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  have hR0 := uniformCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hcomp hjet1 hjet2
  have hC1 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ :=
    rmOneOpC_nonneg (le_trans zero_le_one hΛ) hKb₁_nonneg
  have hR1 := uniformRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
  refine IsCurvAction0.mk
    (ptCurvZeroC_nonneg (Module.finrank ℝ E)
      (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
      (rmOneOpC Λ Kb₀ Kb₁)) ?_
  intro S
  have h := ptCurv_zero_of (I := I) (M := M) g₀ hR0 hC1 hR1 S
  simpa only [uniformPtCurvZeroC, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero, zero_add] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformCurvAction0_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformCurvAction0_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformCurvAction0_of ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformCurvAction0_of

theorem uniformCurvAction3_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    IsCurvAction0 (I := I) (M := M) g₀ 3
      (uniformPtCurvThreeC (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  have hR0 := uniformCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hcomp hjet1 hjet2
  have hC1 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ :=
    rmOneOpC_nonneg (le_trans zero_le_one hΛ) hKb₁_nonneg
  have hR1 := uniformRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
  refine IsCurvAction0.mk
    (ptCurvRankC_nonneg (Module.finrank ℝ E) 3
      (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
      (rmOneOpC Λ Kb₀ Kb₁)) ?_
  intro S
  have h := ptCurv_zero_rank_of (I := I) (M := M) g₀ 3 hR0 hC1 hR1 S
  simpa only [uniformPtCurvThreeC, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero, zero_add] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformCurvAction3_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformCurvAction3_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformCurvAction3_of ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformCurvAction3_of

end RicciFlow
end PDE
end DifferentialGeometry

end
