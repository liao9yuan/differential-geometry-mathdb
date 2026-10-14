import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def conformalMetricOfContDiff (g : SmoothRiemannianMetric I M) (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) : SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * F x) • g.inner x
  symm x v w := by
    simp only [smul_apply, smul_eq_mul, g.symm x v w]
  pos x v hv := by
    simpa only [smul_apply, smul_eq_mul] using mul_pos (Real.exp_pos _) (g.pos x v hv)
  isVonNBounded x := (scaleMetric (Real.exp (2 * F x)) (Real.exp_pos _) g).isVonNBounded x
  contMDiff := by
    let : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) :=
      fun x => inferInstance
    have hscale : ContMDiff I 𝓘(ℝ) ∞ (fun x => Real.exp (2 * F x)) :=
      Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hF)
    convert! hscale.smul_section
      (I := I) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      g.contMDiff using 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff ``Submission.DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff

@[simp] theorem conformalMetricOfContDiff_inner (g : SmoothRiemannianMetric I M) (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M) (v w : TangentSpace I x) :
    (conformalMetricOfContDiff g F hF).inner x v w = Real.exp (2 * F x) * g.inner x v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_inner ``Submission.DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_inner

theorem conformalMetricOfContDiff_const (g : SmoothRiemannianMetric I M) (c : ℝ) :
    conformalMetricOfContDiff g (fun _ => c) contMDiff_const =
      scaleMetric (Real.exp (2 * c)) (Real.exp_pos _) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_const ``Submission.DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_const

@[simp] theorem conformalMetricOfContDiff_zero (g : SmoothRiemannianMetric I M) :
    conformalMetricOfContDiff g (fun _ => 0) contMDiff_const = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp [conformalMetricOfContDiff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_zero ``Submission.DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_zero

theorem conformalMetricOfContDiff_add (g : SmoothRiemannianMetric I M) (F G : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hG : ContMDiff I 𝓘(ℝ) ∞ G) :
    conformalMetricOfContDiff g (F + G) (hF.add hG) =
      conformalMetricOfContDiff (conformalMetricOfContDiff g F hF) G hG := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [conformalMetricOfContDiff_inner, Pi.add_apply, mul_add, Real.exp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_add ``Submission.DifferentialGeometry.Geometry.Metric.conformalMetricOfContDiff_add

variable [FiniteDimensional ℝ E]

theorem metricSharp_conformalMetricOfContDiff (g : SmoothRiemannianMetric I M) (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : M) (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (conformalMetricOfContDiff g F hF) x α =
      Real.exp (-(2 * F x)) • metricSharp g x α := by
  apply (metricFlatMap (conformalMetricOfContDiff g F hF) x).injective
  ext v
  rw [metricFlatMap_apply, metricFlatMap_apply, inner_metricSharp, conformalMetricOfContDiff_inner,
    map_smul (g.inner x), smul_apply, inner_metricSharp]
  change α v = Real.exp (2 * F x) * (Real.exp (-(2 * F x)) * α v)
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricSharp_conformalMetricOfContDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricSharp_conformalMetricOfContDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricSharp_conformalMetricOfContDiff ``Submission.DifferentialGeometry.Geometry.Metric.metricSharp_conformalMetricOfContDiff

theorem gradFun_conformalMetricOfContDiff (g : SmoothRiemannianMetric I M) (F : M → ℝ)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (f : M → ℝ) (x : M) :
    gradFun (conformalMetricOfContDiff g F hF) f x =
      Real.exp (-(2 * F x)) • gradFun g f x :=
  metricSharp_conformalMetricOfContDiff g F hF x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.gradFun_conformalMetricOfContDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.gradFun_conformalMetricOfContDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.gradFun_conformalMetricOfContDiff ``Submission.DifferentialGeometry.Geometry.Metric.gradFun_conformalMetricOfContDiff

end DifferentialGeometry.Geometry.Metric
