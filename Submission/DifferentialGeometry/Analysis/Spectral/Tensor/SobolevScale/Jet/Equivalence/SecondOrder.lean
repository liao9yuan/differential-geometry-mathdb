import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.FractionalPower
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.L2BanachIsomorphism
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHs_order2_equiv_pouSobolev
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 2 T).toReal :=
  iterated_nabla_vs_iterated_partial_equivalence_H1
    (I := I) (M := M) g r s 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHs_order2_equiv_pouSobolev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHs_order2_equiv_pouSobolev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHs_order2_equiv_pouSobolev ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHs_order2_equiv_pouSobolev

def tensorHsOrder2IsometryEquivTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorHs (I := I) (M := M) g r s 2 ≃ₗᵢ[ℝ] TensorL2 r s g :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M)
      (g := g) (r := r) (s := s) 2 0).trans
    (tensorHsZeroEquivL2 (I := I) (M := M)
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
        (I := I) (M := M) g r s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorHsOrder2IsometryEquivTensorL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorHsOrder2IsometryEquivTensorL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorHsOrder2IsometryEquivTensorL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorHsOrder2IsometryEquivTensorL2

def Order2NormEquivOnSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Nspec : SmoothCcTensor g r s → ℝ) (C₁ C₂ : ℝ) : Prop :=
  (∀ T : SmoothCcTensor g r s,
      Nspec T ≤ C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal) ∧
    (∀ T : SmoothCcTensor g r s,
      (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤ C₂ * Nspec T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Order2NormEquivOnSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Order2NormEquivOnSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Order2NormEquivOnSmooth ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Order2NormEquivOnSmooth

noncomputable def smoothCcTensorHs2LinearEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s where
  toFun := SmoothCcTensorHs.toCcTensor
  invFun := fun T => ⟨T⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl
  map_add' S T := SmoothCcTensorHs.toCcTensor_add S T
  map_smul' c S := SmoothCcTensorHs.toCcTensor_smul c S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2LinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2LinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2LinearEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2LinearEquiv

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothCcTensorHs2_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensorHs g r s 2) :
    ‖S‖ = (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal := by
  rcases S with ⟨T⟩
  have h1 := tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k := 2) T
  have h2 : ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2)‖ =
      ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ :=
    UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s 2)
  have h_eq : SmoothCcTensor.toHs (g := g) (r := r) (s := s) 2 T =
      ((⟨T⟩ : SmoothCcTensorHs g r s 2) :
        TensorPouSobolevHilbert g r s 2) := rfl
  rw [h_eq] at h1
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2_norm_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensorHs2_norm_eq target :: scope.openDecls } }

noncomputable def tensorPouSobolevHilbertOrder2ContinuousLinearEquivOfNormEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e₂ : SmoothCcTensor g r s →ₗ[ℝ] F)
    (he₂_dense : DenseRange e₂)
    (Nspec : SmoothCcTensor g r s → ℝ)
    (he₂_norm : ∀ T : SmoothCcTensor g r s, ‖e₂ T‖ = Nspec T)
    (C₁ C₂ : ℝ)
    (h_equiv : Order2NormEquivOnSmooth (I := I) (M := M) g r s Nspec C₁ C₂) :
    TensorPouSobolevHilbert g r s 2 ≃L[ℝ] F :=
  let f : SmoothCcTensorHs g r s 2 ≃ₗ[ℝ] SmoothCcTensor g r s :=
    smoothCcTensorHs2LinearEquiv (I := I) (M := M) g r s
  let e₁ : SmoothCcTensorHs g r s 2 →ₗ[ℝ] TensorPouSobolevHilbert g r s 2 :=
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s 2 →L[ℝ]
        UniformSpace.Completion (SmoothCcTensorHs g r s 2)).toLinearMap
  f.extend e₁ e₂
    (by
      change DenseRange (UniformSpace.Completion.toComplL :
        SmoothCcTensorHs g r s 2 →L[ℝ]
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))
      rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) =
          ((↑) : SmoothCcTensorHs g r s 2 →
            UniformSpace.Completion (SmoothCcTensorHs g r s 2)) from
        UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.denseRange_coe)
    ⟨C₁, by
      intro S
      have hfS : f S = S.toCcTensor := rfl
      have he₂T : ‖e₂ (f S)‖ = Nspec S.toCcTensor := by
        rw [hfS]; exact he₂_norm S.toCcTensor
      have he₁S : ‖e₁ S‖ = ‖S‖ := by
        change ‖((S : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ = ‖S‖
        exact UniformSpace.Completion.norm_coe S
      rw [he₂T, he₁S]
      have hS_norm : ‖S‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 S.toCcTensor).toReal :=
        smoothCcTensorHs2_norm_eq (I := I) (M := M) g S
      rw [hS_norm]
      exact h_equiv.1 S.toCcTensor⟩
    he₂_dense
    ⟨C₂, by
      intro T
      have hfsymmT : f.symm T = ⟨T⟩ := rfl
      have he₁ST : ‖e₁ (f.symm T)‖ = ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ := by
        rw [hfsymmT]
        change ‖((⟨T⟩ : SmoothCcTensorHs g r s 2) :
          UniformSpace.Completion (SmoothCcTensorHs g r s 2))‖ =
          ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖
        exact UniformSpace.Completion.norm_coe
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
      have he₂T : ‖e₂ T‖ = Nspec T := he₂_norm T
      rw [he₁ST, he₂T]
      have hT_norm : ‖(⟨T⟩ : SmoothCcTensorHs g r s 2)‖ =
          (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
        have := smoothCcTensorHs2_norm_eq (I := I) (M := M) g
          (⟨T⟩ : SmoothCcTensorHs g r s 2)
        simpa using this
      rw [hT_norm]
      exact h_equiv.2 T⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHilbertOrder2ContinuousLinearEquivOfNormEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHilbertOrder2ContinuousLinearEquivOfNormEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHilbertOrder2ContinuousLinearEquivOfNormEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.tensorPouSobolevHilbertOrder2ContinuousLinearEquivOfNormEquiv

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
