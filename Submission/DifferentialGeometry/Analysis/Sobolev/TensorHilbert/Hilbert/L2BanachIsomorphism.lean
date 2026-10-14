import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.PartitionOfUnity.ReverseZerothOrderBound
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicSobolev

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def smoothCcTensorHsLinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorHs g r s 0 ≃ₗ[ℝ] SmoothCcTensor g r s where
  toFun := SmoothCcTensorHs.toCcTensor
  invFun := fun T => ⟨T⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl
  map_add' S T := SmoothCcTensorHs.toCcTensor_add S T
  map_smul' c S := SmoothCcTensorHs.toCcTensor_smul c S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma smoothCcTensorHsLinearEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensorHs g r s 0) :
    smoothCcTensorHsLinearEquiv (I := I) (M := M) g r s S = S.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma smoothCcTensorHsLinearEquiv_symm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    (smoothCcTensorHsLinearEquiv (I := I) (M := M) g r s).symm T = ⟨T⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_symm_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHsLinearEquiv_symm_apply

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCcTensorHs_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensorHs g r s 0) :
    ‖S‖ = (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S.toCcTensor).toReal := by
  rcases S with ⟨T⟩
  have h1 := tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k := 0) T
  have h2 : ‖((⟨T⟩ : SmoothCcTensorHs g r s 0) :
        TensorPouSobolevHilbert g r s 0)‖ =
      ‖(⟨T⟩ : SmoothCcTensorHs g r s 0)‖ :=
    UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s 0)
  have h_eq : SmoothCcTensor.toHs (g := g) (r := r) (s := s) 0 T =
      ((⟨T⟩ : SmoothCcTensorHs g r s 0) :
        TensorPouSobolevHilbert g r s 0) := rfl
  rw [h_eq] at h1
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHs_norm_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.smoothCcTensorHs_norm_eq target :: scope.openDecls } }

noncomputable def TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C₁ C₂ : ℝ)
    (h_norm_le : ∀ T : SmoothCcTensor g r s,
      ‖T‖ ≤ C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal)
    (h_norm_ge : ∀ T : SmoothCcTensor g r s,
      (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤ C₂ * ‖T‖) :
    TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g :=
  let f : SmoothCcTensorHs g r s 0 ≃ₗ[ℝ] SmoothCcTensor g r s :=
    smoothCcTensorHsLinearEquiv (I := I) (M := M) g r s
  let e₁ : SmoothCcTensorHs g r s 0 →ₗ[ℝ]
      TensorPouSobolevHilbert g r s 0 :=
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s 0 →L[ℝ]
        UniformSpace.Completion (SmoothCcTensorHs g r s 0)).toLinearMap
  let e₂ : SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g :=
    (UniformSpace.Completion.toComplL :
      SmoothCcTensor g r s →L[ℝ]
        UniformSpace.Completion (SmoothCcTensor g r s)).toLinearMap
  f.extend e₁ e₂
    (by
      change DenseRange (UniformSpace.Completion.toComplL :
        SmoothCcTensorHs g r s 0 →L[ℝ]
          UniformSpace.Completion (SmoothCcTensorHs g r s 0))
      rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s 0 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 0)) =
          ((↑) : SmoothCcTensorHs g r s 0 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 0)) from
        UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.denseRange_coe)
    ⟨C₁, by
      intro S
      have hfS : f S = S.toCcTensor := rfl
      have he₂T : ‖e₂ (f S)‖ = ‖S.toCcTensor‖ := by
        rw [hfS]
        change ‖((S.toCcTensor : SmoothCcTensor g r s) :
          UniformSpace.Completion (SmoothCcTensor g r s))‖ =
          ‖S.toCcTensor‖
        exact UniformSpace.Completion.norm_coe S.toCcTensor
      have he₁S : ‖e₁ S‖ = ‖S‖ := by
        change ‖((S : SmoothCcTensorHs g r s 0) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 0))‖ = ‖S‖
        exact UniformSpace.Completion.norm_coe S
      rw [he₂T, he₁S]
      have hS_norm : ‖S‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S.toCcTensor).toReal :=
        smoothCcTensorHs_norm_eq (I := I) (M := M) g S
      rw [hS_norm]
      exact h_norm_le S.toCcTensor⟩
    (by
      change DenseRange (UniformSpace.Completion.toComplL :
        SmoothCcTensor g r s →L[ℝ]
          UniformSpace.Completion (SmoothCcTensor g r s))
      rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensor g r s →
            UniformSpace.Completion (SmoothCcTensor g r s)) =
          ((↑) : SmoothCcTensor g r s →
            UniformSpace.Completion (SmoothCcTensor g r s)) from
        UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.denseRange_coe)
    ⟨C₂, by
      intro T
      have hfsymmT : f.symm T = ⟨T⟩ := rfl
      have he₁ST : ‖e₁ (f.symm T)‖ = ‖(⟨T⟩ : SmoothCcTensorHs g r s 0)‖ := by
        rw [hfsymmT]
        change ‖((⟨T⟩ : SmoothCcTensorHs g r s 0) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 0))‖ =
          ‖(⟨T⟩ : SmoothCcTensorHs g r s 0)‖
        exact UniformSpace.Completion.norm_coe
          (⟨T⟩ : SmoothCcTensorHs g r s 0)
      have he₂T : ‖e₂ T‖ = ‖T‖ := by
        change ‖((T : SmoothCcTensor g r s) :
          UniformSpace.Completion (SmoothCcTensor g r s))‖ = ‖T‖
        exact UniformSpace.Completion.norm_coe T
      rw [he₁ST, he₂T]
      have hT_norm : ‖(⟨T⟩ : SmoothCcTensorHs g r s 0)‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal := by
        have := smoothCcTensorHs_norm_eq (I := I) (M := M) g
          (⟨T⟩ : SmoothCcTensorHs g r s 0)
        simpa using this
      rw [hT_norm]
      exact h_norm_ge T⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv

theorem exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤ C₂ * ‖T‖ :=
  DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm_zero_toReal_le_norm
    (I := I) (M := M) g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm

noncomputable def TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquivOfForward
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C₁ : ℝ)
    (h_norm_le : ∀ T : SmoothCcTensor g r s,
      ‖T‖ ≤ C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal) :
    TensorPouSobolevHilbert g r s 0 ≃L[ℝ] TensorL2 r s g :=
  TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquiv
    (I := I) (M := M) g r s C₁
    (exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm
      (I := I) (M := M) g r s).choose
    h_norm_le
    (exists_tensorPouSobolevHsNorm_zero_le_const_mul_norm
      (I := I) (M := M) g r s).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquivOfForward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquivOfForward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquivOfForward ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.TensorPouSobolevHilbert.toTensorL2ContinuousLinearEquivOfForward

end IntrinsicSobolev
end Sobolev
end Analysis
end DifferentialGeometry

end
