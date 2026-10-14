import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalCompactFlows
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MixedMetricBounds
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem standard_uniform_terminal_compact_metric_bounds :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L D A : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧ (∀ N, 0 ≤ D N) ∧ (∀ N, 0 < A N) ∧
      ∃ ell : ℝ, 0 < ell ∧ ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ B : ℕ → ℝ,
      (∀ N, 0 ≤ B N) ∧ ∃ ΛZ : ℝ, 1 ≤ ΛZ ∧ ∃ CZ LZ : ℕ → ℝ,
      (∀ N, 0 ≤ CZ N) ∧ (∀ N, 0 ≤ LZ N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
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
          (∀ t ∈ _root_.Set.Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (_root_.Set.Icc 0 T) t) ∧
          (∀ (R : ℝ) (hR : 2 < R),
            RiemannianMetricComplete (metricTruncation (G T) R hR) ∧
            (∀ (x : E3) (v : TangentSpace (𝓡 3) x),
              ell * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
                (metricTruncation (G T) R hR).inner x v v) ∧
            (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w = (G T).inner x v w) ∧
            (∀ (x : E3), R - 1 ≤ ‖x‖ → ∀ (v w : TangentSpace (𝓡 3) x),
              (metricTruncation (G T) R hR).inner x v w =
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v w)) ∧
          (∀ (R : ℝ) (hR : 2 < R), transitionEnd + 4 ≤ R →
            (∀ N j : ℕ, j ≤ N → ∀ x : E3,
              metricDerivNorm j (metricTruncation (G T) R hR)
                DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D N) ∧
            (∀ k : ℕ, ∀ x : E3,
              Real.sqrt (normSq0S (metricTruncation (G T) R hR) x (4 + k)
                (iterCov (metricTruncation (G T) R hR) 4
                  (metricRm04 (metricTruncation (G T) R hR)) k x)) ≤ A k)) ∧
          ∀ (north : S3) (R : ℝ) (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R),
            transitionEnd + 4 ≤ R →
            ∃ Z : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
              IsSolutionOn Z ∧ Z.base.metric 0 = compactDoubleTruncationMetric north R hR (G T) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete (Z.base.metric t)) ∧
              (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
                ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                  (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (Z.base.metric p.1) x₀ p.2 i j)
                  (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
                HasDerivWithinAt (fun r => (Z.base.metric r).inner x v w)
                  (-2 * ricciTensor (Z.base.metric t) x v w) (_root_.Set.Ici 0) t) ∧
              (∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                Real.sqrt (normSq0S (Z.base.metric t) x (4 + a)
                  (iteratedCovariantTimeDerivWithin Z.base.metric
                    (fun r => nablaKRm04Field Z r a x) (_root_.Set.Icc 0 τ) b t)) ≤ B N) ∧
              (∀ x ∈ Metric.ball (0 : E3) (R + 1), ∀ v w : E3,
                (Z.base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (metricTruncation (G T) R (by linarith [le_max_right transitionEnd 2])).inner x v w) ∧
              (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ v w : E3,
                (Z.base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (G T).inner x v w) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, MetricUniformEquivalentOn _root_.Set.univ
                (Z.base.metric 0) (Z.base.metric t) ΛZ) ∧
              (∀ N : ℕ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                metricCovDerivNorm N (Z.base.metric t) (Z.base.metric 0) x ≤ CZ N) ∧
              ∀ N : ℕ, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                metricDerivNorm N (Z.base.metric s) (Z.base.metric t)
                  (Z.base.metric 0) x ≤ LZ N * |s - t| := by
  obtain ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, hfamily⟩ := standard_uniform_terminal_compact_flows
  obtain ⟨ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, henrich⟩ :=
    exists_uniform_metric_time_bounds_of_spatial_curvature_bounds
      (I := 𝓡 3) (M := S3) (by simp) τ hτ B hB
  refine ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows⟩ := hfamily S T hT hTα hTS
  refine ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, ?_⟩
  intro north R hR hlarge
  obtain ⟨Z, hZ, hz, hcomp, hg, hp, hm, hfull, hcore⟩ := hflows north R hR hlarge
  have hspatial (k : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (x : S3) :
      Real.sqrt (normSq0S (Z.base.metric t) x (4 + k)
        (nablaKRm04Field Z t k x)) ≤ B k := by
    exact hm k k 0 (by omega) t ht x
  obtain ⟨heZ, hcZ, hlZ⟩ := henrich Z hZ hg hp hspatial
  exact ⟨Z, hZ, hz, hcomp, hg, hp, hm, hfull, hcore, heZ, hcZ, hlZ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_compact_metric_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_compact_metric_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_compact_metric_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_compact_metric_bounds
end DifferentialGeometry.PDE.RicciFlow
