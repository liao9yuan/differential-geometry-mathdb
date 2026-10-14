import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem metric_right_derivative_of_closed_gram
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hRF : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) t)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (g t).inner x v w)
      (-2 * ricciTensor (g a) x v w) (_root_.Set.Ici a) a := by
  have hmetric := metricFamilySmoothOn_of_chartGram g hab
    (fun x₀ i j => (hgram x₀ i j).mono (Set.prod_mono_left _root_.Set.Ioo_subset_Icc_self))
    (fun x₀ i j => ((hgram x₀ i j).mono
      (Set.prod_mono_left _root_.Set.Ico_subset_Icc_self)).continuousOn)
  have hRicField := ricciCont_of_joint g (_root_.Set.Icc a b) (uniqueDiffOn_Icc hab) hgram
  apply metric_right_derivative_of_interior hab g hmetric.coeff_cont ?_ hRF x v w
  intro y u z
  have hRic : ContinuousOn (fun t => ricciTensor (g t) y u z) (_root_.Set.Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : _root_.Set.Icc a b => ricciTensor (g t.val) y u z)
    have h := hRicField.eval_continuous
      (P := _root_.Set.Icc a b) (τ := Subtype.val) (b := fun _ => y)
      continuous_subtype_val (fun t => t.property) continuous_const
      (v := fun i _ => vec2 u z i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using h
  exact hRic.mono _root_.Set.Ico_subset_Icc_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_closed_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_closed_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_closed_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_closed_gram

theorem solutionOn_of_closed_gram
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (_root_.Set.Icc a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (hRF : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) t) :
    IsSolutionOn
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)) := by
  apply solutionOn_of_joint hab g
  · intro x₀ i j
    exact (hgram x₀ i j).mono (Set.prod_mono_left _root_.Set.Ico_subset_Icc_self)
  · intro t ht x v w
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · subst t
      exact metric_right_derivative_of_closed_gram hab g hgram hRF x v w
    · exact (hRF t ⟨hlt, ht.2⟩ x v w).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solutionOn_of_closed_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solutionOn_of_closed_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solutionOn_of_closed_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.solutionOn_of_closed_gram

end DifferentialGeometry.PDE.RicciFlow

end
