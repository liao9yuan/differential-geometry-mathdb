import Submission.DifferentialGeometry.Geometry.Metric.Family.TensorNorm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricDifference

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_metricDiffSq_family
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x)) :
    Continuous (fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) := by
  apply continuous_normSq0S_family g₁ (fun t x => metricDiffAt (g₁ t) (g₂ t) x) hg₁
  convert hg₁.add (hg₂.const_smul (-1)) using 1
  simp only [metricDiffAt, neg_one_smul, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.continuous_metricDiffSq_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.continuous_metricDiffSq_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.continuous_metricDiffSq_family ``Submission.DifferentialGeometry.PDE.RicciFlow.continuous_metricDiffSq_family

theorem continuousOn_metricDiffSq_family
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    (x : M) : ContinuousOn (fun t => metricDiffSq (g₁ t) (g₂ t) x) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hpair : Continuous (fun t : K => (t, x)) := continuous_id.prodMk continuous_const
  have hc : Continuous (fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) :=
    continuous_metricDiffSq_family (I := I) g₁ g₂ hg₁ hg₂
  exact Continuous.comp (f := fun t : K => (t, x))
    (g := fun q : K × M => metricDiffSq (g₁ q.1.1) (g₂ q.1.1) q.2) hc hpair

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.continuousOn_metricDiffSq_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.continuousOn_metricDiffSq_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.continuousOn_metricDiffSq_family ``Submission.DifferentialGeometry.PDE.RicciFlow.continuousOn_metricDiffSq_family

theorem tendsto_metricDiffSq_of_metricTensor_continuous
    {K : Set ℝ} (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (hg₁ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₁ t) x))
    (hg₂ : tensor0SFamilyContinuousOnSet 2 K (fun t x => metricTensorField (g₂ t) x))
    {a : ℝ} (ha : a ∈ K) (hinit : g₁ a = g₂ a) (x : M) :
    Tendsto (fun t => metricDiffSq (g₁ t) (g₂ t) x) (𝓝[K] a) (𝓝 0) := by
  have h := (continuousOn_metricDiffSq_family g₁ g₂ hg₁ hg₂ x) a ha
  have hz : metricDiffSq (g₁ a) (g₂ a) x = 0 := by
    rw [hinit, metricDiffSq, metricDiffAt_self]
    exact (normSq0S_eq_zero_iff (g₂ a) x 2 0).2 rfl
  exact hz ▸ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tendsto_metricDiffSq_of_metricTensor_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tendsto_metricDiffSq_of_metricTensor_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tendsto_metricDiffSq_of_metricTensor_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.tendsto_metricDiffSq_of_metricTensor_continuous

end DifferentialGeometry.PDE.RicciFlow
