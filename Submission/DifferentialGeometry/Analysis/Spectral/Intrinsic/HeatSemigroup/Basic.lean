import Submission.DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.Spectral.SemigroupContinuity
import Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private noncomputable def intrinsicEigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    HilbertBasis (TensorEigenIdx (I := I) (M := M) g r s) ℝ (TensorL2 r s g) :=
  tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.intrinsicEigenbasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.intrinsicEigenbasis target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma intrinsic_lambda_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
  fun i => tensor_lambda_nonneg (I := I) (M := M) i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.intrinsic_lambda_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.intrinsic_lambda_nonneg target :: scope.openDecls } }

noncomputable def tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  abstractSpectralSemigroup (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup

theorem tensorHeatSemigroup_apply_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorHeatSemigroup (I := I) (M := M) g r s 0 =
      ContinuousLinearMap.id ℝ (TensorL2 r s g) :=
  abstractSpectralSemigroup_apply_zero (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_zero ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_zero

theorem tensorHeatSemigroup_apply_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t s' : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s') :
    tensorHeatSemigroup (I := I) (M := M) g r s (t + s') =
      (tensorHeatSemigroup (I := I) (M := M) g r s t).comp
        (tensorHeatSemigroup (I := I) (M := M) g r s s') :=
  abstractSpectralSemigroup_apply_add (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_add ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_apply_add

theorem tensorHeatSemigroup_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    ‖tensorHeatSemigroup (I := I) (M := M) g r s t‖ ≤ 1 :=
  abstractSpectralSemigroup_opNorm_le_one (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_opNorm_le_one

theorem tensorHeatSemigroup_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : TensorL2 r s g) :
    ContinuousOn (fun t : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s t T)
      (Set.Ici (0 : ℝ)) :=
  abstractSpectralSemigroup_continuousOn (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_continuousOn ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_continuousOn

theorem tensorHeatSemigroup_inner_eigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
          u₀⟫_ℝ := by
  classical
  set b := intrinsicEigenbasis (I := I) (M := M) g r s with hb_def
  change ⟪b i, tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b i, u₀⟫_ℝ
  have h_apply :
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ =
        ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j := by
    unfold tensorHeatSemigroup
    rw [abstractSpectralSemigroup_apply_of_nonneg b
      (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀]
  rw [h_apply]
  have h_summable :=
    summable_heatTerm b (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀
  have h_hsum := h_summable.hasSum
  have h_inner_hsum := h_hsum.mapL (innerSL ℝ (b i))
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ⟪b i, b j⟫_ℝ = if j = i then (1 : ℝ) else 0 := by
    intro j
    rw [show ⟪b i, b j⟫_ℝ = ⟪b j, b i⟫_ℝ from real_inner_comm _ _]
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      (innerSL ℝ (b i))
          (heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j) =
        if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0 := by
    intro j
    change ⟪b i,
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_smul_right, h_inner_eq]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have h_inner_hsum' : HasSum (fun j =>
      if j = i then
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
          ⟪b j, u₀⟫_ℝ
      else 0)
      ((innerSL ℝ (b i))
        (∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j)) :=
    HasSum.congr_fun h_inner_hsum fun j => (h_summand_eq j).symm
  have h_tsum_ite :
      ∑' j : TensorEigenIdx (I := I) (M := M) g r s,
        (if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0) =
      heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
        ⟪b i, u₀⟫_ℝ := by
    rw [tsum_ite_eq i]
  have h_eq := h_inner_hsum'.tsum_eq
  rw [h_tsum_ite] at h_eq
  have h_inner_val :
      ⟪b i, ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j⟫_ℝ =
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
          ⟪b i, u₀⟫_ℝ := h_eq.symm
  rw [h_inner_val, heatCoeff_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_inner_eigenbasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_inner_eigenbasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_inner_eigenbasis ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroup_inner_eigenbasis

end Spectral
end Analysis
end DifferentialGeometry

end
