import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def tensorHsCongr (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    TensorHs (I := I) (M := M) g r s a ≃ₗᵢ[ℝ]
      TensorHs (I := I) (M := M) g r s b := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr

def tensorHsCongrL (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) :
    TensorHs (I := I) (M := M) g r s a →L[ℝ]
      TensorHs (I := I) (M := M) g r s b :=
  (tensorHsCongr (I := I) (M := M) g r s h).toLinearIsometry.toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsCongr_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongr (I := I) (M := M) g r s (rfl : a = a) =
      LinearIsometryEquiv.refl ℝ _ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_refl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_refl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsCongrL_refl (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) :
    tensorHsCongrL (I := I) (M := M) g r s (rfl : a = a) =
      ContinuousLinearMap.id ℝ (TensorHs (I := I) (M := M) g r s a) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_refl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_refl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongrL_apply {a b : ℝ} (h : a = b)
    (u : TensorHs (I := I) (M := M) g r s a) :
    tensorHsCongrL (I := I) (M := M) g r s h u =
      tensorHsCongr (I := I) (M := M) g r s h u :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_tensorHsCongr {a b : ℝ} (h : a = b)
    (u : TensorHs (I := I) (M := M) g r s a) :
    ‖tensorHsCongr (I := I) (M := M) g r s h u‖ = ‖u‖ :=
  (tensorHsCongr (I := I) (M := M) g r s h).norm_map u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_tensorHsCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_tensorHsCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_tensorHsCongr ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_tensorHsCongr

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongr_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : TensorHs (I := I) (M := M) g r s b) :
    tensorHsCongr (I := I) (M := M) g r s hac
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab u) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hcd
        (tensorHsCongr (I := I) (M := M) g r s hbd u) := by
  cases hac
  cases hbd
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_incl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongr_incl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongrL_incl {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d) :
    (tensorHsCongrL (I := I) (M := M) g r s hac).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hcd).comp
        (tensorHsCongrL (I := I) (M := M) g r s hbd) := by
  cases hac
  cases hbd
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_incl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsCongrL_incl

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_congr_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (h : a = b)
    (L : X →L[ℝ] TensorHs (I := I) (M := M) g r s a) :
    ‖(tensorHsCongrL (I := I) (M := M) g r s h).comp L‖ = ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_congr_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_congr_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_congr_comp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.norm_congr_comp

omit [NeZero (Module.finrank ℝ E)] in
theorem opNorm_comp_congr_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a b : ℝ} (h : a = b)
    (L : TensorHs (I := I) (M := M) g r s b →L[ℝ] X) :
    ‖L.comp (tensorHsCongrL (I := I) (M := M) g r s h)‖ ≤ ‖L‖ := by
  cases h
  rw [tensorHsCongrL_refl, ContinuousLinearMap.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.opNorm_comp_congr_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.opNorm_comp_congr_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.opNorm_comp_congr_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.opNorm_comp_congr_le

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
