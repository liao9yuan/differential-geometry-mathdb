import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Metric.TerminalFamily
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedRegularity
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem standard_smooth_terminal_families_of_curvature_bound
    (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ENNReal.ofReal T ≤ S.lifetime →
        (∀ t ∈ _root_.Set.Ico 0 T, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ _root_.Set.Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ _root_.Set.Icc 0 T, MetricUniformEquivalentOn _root_.Set.univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ _root_.Set.Icc 0 T, ∀ t ∈ _root_.Set.Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (_root_.Set.Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          (∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Ici 0) t) ∧
          (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (G p.1) x₀ p.2 i j)
              (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          ∀ t ∈ _root_.Set.Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Icc 0 T) t := by
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ :=
    standard_metric_bounds_before_endpoint T K hT.le hK
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S hTS hRm
  obtain ⟨he, hc, hl⟩ := hb S hTS hRm
  obtain ⟨G, hEq, hComp, hEquiv, hCov, hLip, hJets⟩ :=
    exists_closed_terminal_family_of_reference_bounds (I := 𝓡 3) (M := E3)
      inferInstance DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete
      S.metric T Λ hT hΛ C L hL he hc hl
  have hpde : ∀ t ∈ _root_.Set.Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (G s).inner x v w)
        (-2 * ricciTensor (G t) x v w) (_root_.Set.Ici 0) t := by
    intro t ht x v w
    have hdom : t ∈ S.domain := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr ht.2 |>.trans_le hTS⟩
    have hgerm : (fun s => (G s).inner x v w) =ᶠ[𝓝[_root_.Set.Ici 0] t]
        (fun s => (S.metric s).inner x v w) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsT
      rw [hEq s ⟨hs, hsT⟩]
    rw [hEq t ht]
    exact (S.equation t hdom x v w).congr_of_eventuallyEq hgerm (by rw [hEq t ht])
  obtain ⟨hgram, hclosed⟩ := contMDiffOn_and_equation_Icc_of_spatial_jets G 0 T hT hJets
    (fun t ht x v w => (hpde t ⟨ht.1.le, ht.2⟩ x v w).hasDerivAt (Ici_mem_nhds ht.1))
  exact ⟨G, hEq, (hEq 0 ⟨le_rfl, hT⟩).trans S.initial, hComp, hEquiv,
    hCov, hLip, hJets, hpde, hgram, hclosed⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_smooth_terminal_families_of_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_smooth_terminal_families_of_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_smooth_terminal_families_of_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_smooth_terminal_families_of_curvature_bound
end DifferentialGeometry.PDE.RicciFlow
