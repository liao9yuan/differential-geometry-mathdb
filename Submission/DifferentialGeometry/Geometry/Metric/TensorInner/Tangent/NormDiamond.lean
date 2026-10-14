import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.ContinuousRiemannianMetric
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor0SBundle_enorm_eq_riemannianBundle_enorm
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  have hinner : (_root_.Inner.inner ℝ v v : ℝ) = g.inner x v v := rfl
  rw [hinner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm ``Submission.DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm

section MetricNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMetricNorm (g : SmoothRiemannianMetric I M)
    [_root_.Bundle.RiemannianBundle (fun (x : M) => TangentSpace I x)] : Prop :=
  ∀ (x : M) (w : TangentSpace I x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMetricNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMetricNorm

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem isMetricNorm_of_riemannianBundle (g : SmoothRiemannianMetric I M) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    IsMetricNorm (I := I) (M := M) g :=
  fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle ``Submission.DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem IsMetricNorm.inner_eq
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    (x : M) (v w : TangentSpace I x) : _root_.Inner.inner ℝ v w = g.inner x v w := by
  have hdiag (z : TangentSpace I x) : _root_.Inner.inner ℝ z z = g.inner x z z := by
    have hn : ‖z‖ = Real.sqrt (g.inner x z z) := by
      have h := hEnorm x z
      rw [← ofReal_norm] at h
      have ht := congrArg ENNReal.toReal h
      simpa only [ENNReal.toReal_ofReal (norm_nonneg z),
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using ht
    rw [real_inner_self_eq_norm_sq, hn,
      Real.sq_sqrt (metric_inner_self_nonneg (I := I) g x z)]
  have h := hdiag (v + w)
  simp only [inner_add_left, inner_add_right, map_add, add_apply] at h
  rw [hdiag v, hdiag w, g.symm x w v] at h
  linarith [real_inner_comm v w]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.IsMetricNorm
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.inner_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.inner_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.inner_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.inner_eq

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem IsMetricNorm.isContinuousRiemannianBundle
    [_root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g) :
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
  ⟨g.inner, g.contMDiff.continuous, hEnorm.inner_eq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.isContinuousRiemannianBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.isContinuousRiemannianBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.isContinuousRiemannianBundle ``Submission.DifferentialGeometry.Geometry.Riemannian.IsMetricNorm.isContinuousRiemannianBundle

end MetricNorm

end DifferentialGeometry.Geometry.Riemannian

end
