import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem norm_scalarSmul_le
    (q : SmoothRiemannianMetric I M) (r s : ℕ) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (S : SmoothCcTensor q r s) :
    ‖scalarSmul (I := I) (M := M) q r s ζ S‖ ≤ C * ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  let base : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q r s x (S.toFun x) (S.toFun x)
  let weighted : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q r s x
      ((scalarSmul (I := I) (M := M) q r s ζ S).toFun x)
      ((scalarSmul (I := I) (M := M) q r s ζ S).toFun x)
  have hpoint : ∀ x : M, weighted x ≤ C ^ 2 * base x := by
    intro x
    have hsq : ((ζ : M → Real) x) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hζ x)
    have hbase : 0 ≤ base x :=
      tensorInnerPointwise_nonneg (I := I) (M := M) q r s x (S.toFun x)
    dsimp only [weighted, base]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    nlinarith [mul_le_mul_of_nonneg_right hsq hbase]
  have hweighted : _root_.MeasureTheory.Integrable weighted μ := by
    exact (SmoothCcTensor.memL2_toFun
      (scalarSmul (I := I) (M := M) q r s ζ S)).integrable_inner_self
  have hbase : _root_.MeasureTheory.Integrable base μ := by
    exact (SmoothCcTensor.memL2_toFun S).integrable_inner_self
  have hint : (∫ x, weighted x ∂μ) ≤ ∫ x, C ^ 2 * base x ∂μ :=
    _root_.MeasureTheory.integral_mono_ae hweighted (hbase.const_mul (C ^ 2))
      (Filter.Eventually.of_forall hpoint)
  rw [_root_.MeasureTheory.integral_const_mul] at hint
  have hsq :
      ‖scalarSmul (I := I) (M := M) q r s ζ S‖ ^ 2 ≤
        (C * ‖S‖) ^ 2 := by
    simpa only [← real_inner_self_eq_norm_sq,
      SmoothCcTensor.inner_def, tensorL2Inner, weighted, base, μ, mul_pow] using hint
  have hrhs : 0 ≤ C * ‖S‖ := mul_nonneg hC (norm_nonneg S)
  nlinarith [norm_nonneg
    (scalarSmul (I := I) (M := M) q r s ζ S)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_scalarSmul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_scalarSmul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_scalarSmul_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.norm_scalarSmul_le

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
end

end
