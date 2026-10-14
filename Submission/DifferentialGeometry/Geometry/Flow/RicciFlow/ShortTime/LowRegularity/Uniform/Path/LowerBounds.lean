import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.CovariantTensorBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem lower_jet_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ₀ : SmoothCcTensor g 2 2) (Φ₁ : SmoothCcTensor g 3 2)
          (U : SmoothCcTensor g 0 2) (A₀ A₁ : ℝ),
          0 ≤ A₀ → 0 ≤ A₁ →
          (∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g 2 2 j Φ₀‖ ^ 2) ≤ A₀ ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ A₁ ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U +
                operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
                  (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
            C * (A₀ + A₁) *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨C₀, hC₀, hzero⟩ :=
    operatorFieldApplication_h1_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨C₁, hC₁, hone⟩ :=
    operatorFieldApplication_h2cov_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, ?_⟩
  intro g hEq hjet Φ₀ Φ₁ U A₀ A₁ hA₀ hA₁ hΦ₀ hΦ₁
  have hzero' := hzero g hEq hjet Φ₀ U A₀ hA₀ hΦ₀
  have hone' := hone g hEq hjet Φ₁ U A₁ hA₁ hΦ₁
  have hnorm : 0 ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := norm_nonneg _
  rw [ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U)‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
              (covGrad (I := I) (M := M) g 0 2 U))‖ := norm_add_le _ _
    _ ≤ C₀ * A₀ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * A₁ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
      add_le_add hzero' hone'
    _ ≤ C₀ * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₀) hnorm
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₁) hnorm
    _ = (C₀ + C₁) * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lower_jet_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lower_jet_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lower_jet_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lower_jet_uniform

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
