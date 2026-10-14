import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Algebra.TensorDecomposition
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ReloweringDivergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
variable {Idx : Type*} [Fintype Idx]

theorem sdecRem_eq_sub_divergence
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (P : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (b : Module.Basis Idx ℝ (TangentSpace I x))
    (R₀ : Idx → Idx → Idx → Idx → ℝ)
    (Rm2dot : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x) :
    sdecRem (I := I) g₁ g₂ P b R₀ Rm2dot =
      lowOfComp (I := I) g₁ b R₀ + gapDot (I := I) g₁ g₂ Rm2dot -
        covDiv0SField (I := I) g₁
          (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
            metricNabla0S (I := I) g₁ P) x := by
  have h := congrArg (fun F => F x)
    (covariant_divergence_relowering_defect (I := I) g₁ g₂ P)
  change covDiv0SField (I := I) g₁
      (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
        metricNabla0S (I := I) g₁ P) x =
    (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ P) -
      roughLap0SField (I := I) g₁ P) x +
    metricTraceFirstTwoField (I := I) g₁
      (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ P)
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) x at h
  rw [sdecRem, h]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sdecRem_eq_sub_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sdecRem_eq_sub_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sdecRem_eq_sub_divergence ``Submission.DifferentialGeometry.PDE.RicciFlow.sdecRem_eq_sub_divergence

theorem covDiv_sdecFlux_add_sdecRem_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) {x : M}
    (Tf₂ P : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 4)
    (b : Module.Basis Idx ℝ (TangentSpace I x))
    (R₀ : Idx → Idx → Idx → Idx → ℝ)
    (Rm2dot : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x) :
    covDiv0SField (I := I) g₁ (sdecFlux (I := I) g₁ g₂ Tf₂ P) x +
        sdecRem (I := I) g₁ g₂ P b R₀ Rm2dot =
      covDiv0SField (I := I) g₁
        (sdecFlux (I := I) g₁ g₂ Tf₂ P -
          (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ P) -
            metricNabla0S (I := I) g₁ P)) x +
        lowOfComp (I := I) g₁ b R₀ + gapDot (I := I) g₁ g₂ Rm2dot := by
  simp only [sdecRem_eq_sub_divergence, covDiv0SField_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDiv_sdecFlux_add_sdecRem_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDiv_sdecFlux_add_sdecRem_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDiv_sdecFlux_add_sdecRem_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.covDiv_sdecFlux_add_sdecRem_eq

end DifferentialGeometry.PDE.RicciFlow
