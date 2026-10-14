import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def conformalMetric (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) : SmoothRiemannianMetric I M where
  inner x := Real.exp (2 * f x) • g.inner x
  symm x := (scaleMetric _ (Real.exp_pos _) g).symm x
  pos x := (scaleMetric _ (Real.exp_pos _) g).pos x
  isVonNBounded x := (scaleMetric _ (Real.exp_pos _) g).isVonNBounded x
  contMDiff := by
    have hs : ContMDiff I 𝓘(ℝ) ∞ (fun x => Real.exp (2 * f x)) :=
      Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hf)
    exact hs.smul_section g.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.conformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.conformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.conformalMetric ``Submission.DifferentialGeometry.Geometry.conformalMetric

@[simp] theorem conformalMetric_inner (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v w : TangentSpace I x) :
    (conformalMetric g f hf).inner x v w = Real.exp (2 * f x) * g.inner x v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.conformalMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.conformalMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.conformalMetric_inner ``Submission.DifferentialGeometry.Geometry.conformalMetric_inner


def euclideanMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    SmoothRiemannianMetric 𝓘(ℝ, V) V :=
  { riemannianMetricVectorSpace V with
    contMDiff := (riemannianMetricVectorSpace V).contMDiff.of_le le_top }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanMetric ``Submission.DifferentialGeometry.Geometry.euclideanMetric

@[simp] theorem euclideanMetric_inner (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x v w : V) :
    (euclideanMetric V).inner x v w = _root_.Inner.inner ℝ v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.euclideanMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.euclideanMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.euclideanMetric_inner ``Submission.DifferentialGeometry.Geometry.euclideanMetric_inner

end DifferentialGeometry.Geometry
