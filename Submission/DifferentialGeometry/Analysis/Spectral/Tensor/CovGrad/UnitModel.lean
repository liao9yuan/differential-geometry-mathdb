import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => E) (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor

def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel

@[simp] theorem unitModel_zero (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x = 0 := by
  rw [unitModel, SmoothCcTensor.toSection_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_zero

@[simp] theorem unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + T) x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s T x := by
  rw [unitModel, unitModel, unitModel, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, add_apply, Tensor0SSpace.toModel_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add

@[simp] theorem unitModel_neg (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (-S) x = -unitModel (I := I) (M := M) g s S x := by
  rw [unitModel, unitModel, SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg,
    Pi.neg_apply, neg_apply, Tensor0SSpace.toModel_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_neg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_neg

@[simp] theorem unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - T) x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s T x := by
  simpa only [sub_eq_add_neg, unitModel_neg] using
    unitModel_add (I := I) (M := M) g s S (-T) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub

@[simp] theorem unitModel_smul (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • S) x =
      c • unitModel (I := I) (M := M) g s S x := by
  rw [unitModel, unitModel, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, smul_apply, Tensor0SSpace.toModel_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
