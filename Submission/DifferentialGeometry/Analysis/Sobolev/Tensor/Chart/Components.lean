import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartComp_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComp_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm (toEuclidean.symm y)) := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_mem ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_mem

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComp_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_notMem ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_apply_of_notMem

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_add ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_smul (I := I) (M := M) g r s c S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_smul ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) α Idx Jdx =
      (fun _ => (0 : ℝ)) := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s
    (0 : ℝ) (0 : SmoothCcTensor g r s) α Idx Jdx
  rw [zero_smul] at h
  funext y
  have hy := congrFun h y
  simpa using hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (-S) α Idx Jdx =
      -tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s (-1 : ℝ) S α Idx Jdx
  rw [neg_one_smul] at h
  rw [h, neg_one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_neg ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_neg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx -
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  rw [sub_eq_add_neg, tensorChartComp_add, tensorChartComp_neg, ← sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_sub

noncomputable def tensorChartCompₗ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    SmoothCcTensor g r s →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) where
  toFun S := tensorChartComp (I := I) (M := M) g r s S α Idx Jdx
  map_add' S₁ S₂ := tensorChartComp_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx
  map_smul' c S := tensorChartComp_smul (I := I) (M := M) g r s c S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartCompₗ_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (S : SmoothCcTensor g r s) :
    tensorChartCompₗ (I := I) (M := M) g r s α Idx Jdx S =
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartCompₗ_apply

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (𝓘(ℝ, ℝ)) ∞
      (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contMDiff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  have h := tensorChartComp_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  rwa [contMDiff_iff_contDiff] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiff

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiffOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_contDiffOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComp_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_hasCompactSupport

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComp_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_continuous ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_continuous

noncomputable def tensorChartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    TensorRSModel r s ℝ E :=
  tensorChartPushedRawModel (I := I) (M := M) g r s S α y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartPushed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      tensorChartPushedRawModel (I := I) (M := M) g r s S α y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_def ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eq_sum_tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx := by
  simp only [tensorChartPushed_def, tensorChartComp_def]
  exact chartPushedRaw_eq_sum_tensorChartComponent
    (I := I) (M := M) g r s S α y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_sum_tensorChartComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_sum_tensorChartComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_sum_tensorChartComp ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_sum_tensorChartComp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0)) :
    tensorChartPushed (I := I) (M := M) g r s S α = (fun _ => 0) := by
  funext y
  rw [tensorChartPushed_eq_sum_tensorChartComp]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx]
  rw [zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComp_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : SmoothCcTensor g r s} (hS : S = 0) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0) := by
  rw [hS]
  exact tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_section_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_section_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_section_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.tensorChartComp_eq_zero_of_section_eq_zero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem card_tensorChartComp_index (r s : ℕ) :
    Fintype.card
        ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) =
      (Module.finrank ℝ E) ^ (r + s) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.card_tensorChartComp_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.card_tensorChartComp_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.card_tensorChartComp_index ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.card_tensorChartComp_index

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
