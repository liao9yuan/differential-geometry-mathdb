import Submission.DifferentialGeometry.Geometry.Metric.Family.Cartesian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMaximalExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem exists_standard_solution_extending_bounded_flow
    {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := E3) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hslab : _root_.Set.Icc 0 T ⊆ D.carrier) (hreg : _root_.Set.Ioo 0 T ⊆ D.regular)
    (hinitial : S.base.metric 0 = StandardCap.metric)
    (hgram : ∀ (x : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric p.1) x p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x).baseSet))
    {C : ℝ} (hcurv : ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) :
    ∃ Q : StandardSolution, ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ t ∈ _root_.Set.Ico 0 T, Q.val.metric t = S.base.metric t := by
  have hcomplete : ∀ t ∈ _root_.Set.Icc 0 T, RiemannianMetricComplete (S.base.metric t) := by
    intro t ht
    apply complete_of_curvature_bound S hS hslab hreg hcurv ht ⟨le_rfl, hT.le⟩
    rw [hinitial]
    exact StandardCap.metric_complete
  have hdomain : (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)).carrier =
      Ico 0 T := by rw [lifetimeInterval_ofReal T hT]; rfl
  let P : PartialStandardSolution := {
    lifetime := ENNReal.ofReal T
    lifetime_pos := ENNReal.ofReal_pos.mpr hT
    metric := S.base.metric
    smooth := by
      rw [hdomain]
      exact (cartesian_contDiffOn_of_chartGram S.base.metric (_root_.Set.Icc 0 T) hgram).mono
        (_root_.Set.prod_mono _root_.Set.Ico_subset_Icc_self Subset.rfl)
    equation := by
      rw [hdomain]
      intro t ht x v w
      apply (metricPDE_Icc S hS hslab hreg t (_root_.Set.Ico_subset_Icc_self ht) x v w).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)]
        with r hr hrT
      exact ⟨hr,hrT.le⟩
    initial := hinitial
    complete := fun t ht => hcomplete t (_root_.Set.Ico_subset_Icc_self (hdomain ▸ ht))
    curvature_bound := by
      intro a _ ha
      have haT : a < T := (ENNReal.ofReal_lt_ofReal_iff hT).mp ha
      exact ⟨Real.sqrt C, Real.sqrt_nonneg _, fun t ht x =>
        Real.sqrt_le_sqrt (hcurv t ⟨ht.1, ht.2.trans haT.le⟩ x)⟩ }
  obtain ⟨Q, hQ⟩ := P.exists_maximal_extension
  refine ⟨Q, hQ.1, fun t ht => hQ.2 t ?_⟩
  change t ∈ (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)).carrier
  rwa [hdomain]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_solution_extending_bounded_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_solution_extending_bounded_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_solution_extending_bounded_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_solution_extending_bounded_flow

end DifferentialGeometry.PDE.RicciFlow
