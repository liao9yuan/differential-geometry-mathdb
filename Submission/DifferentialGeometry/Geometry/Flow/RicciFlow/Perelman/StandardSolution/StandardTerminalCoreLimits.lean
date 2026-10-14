import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalCompactMetricBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCoreMaps
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteReferenceLimit
import Submission.DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap _root_.Submission.DifferentialGeometry.Geometry.Curvature
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

private theorem ricci_bound_of_mixed_zero
    (τ : ℝ) (hτ : 0 < τ)
    (Z : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le))
    (B : ℝ)
    (hRm : ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : S3,
      Real.sqrt (normSq0S (Z.base.metric t) y 4 (nablaKRm04Field Z t 0 y)) ≤ B) :
    ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : S3, ricciNorm Z t y ≤ 81 * B ^ 2 := by
  intro t ht y
  have hRsq := (Real.sqrt_le_iff.mp (hRm t ht y)).2
  have hh := ricTower_normSq_le Z t 0 y
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    Nat.reduceAdd, pow_succ, pow_zero] at hh
  change ricciNorm Z t y ≤ 81 *
    normSq0S (Z.base.metric t) y 4 (nablaKRm04Field Z t 0 y) at hh
  nlinarith only [hRsq, hh]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.ricci_bound_of_mixed_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.ricci_bound_of_mixed_zero target :: scope.openDecls } }

theorem standard_uniform_terminal_core_limits :
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
          (∀ (north : S3) (R : ℝ) (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R),
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
                  (Z.base.metric 0) x ≤ LZ N * |s - t|) ∧
          ∀ north : S3,
            ∃ Z : ℕ → SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
            ∃ hZ : ∀ j, IsSolutionOn (Z j),
              (∀ stage : ℕ,
                let R := compactCapApproximationRadius (stage + 2)
                let hR := compactCapApproximationRadius_large (stage + 2)
                (Z stage).base.metric 0 = compactDoubleTruncationMetric north R hR (G T) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete ((Z stage).base.metric t)) ∧
              (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
                ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                  (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix ((Z stage).base.metric p.1) x₀ p.2 i j)
                  (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
                HasDerivWithinAt (fun r => ((Z stage).base.metric r).inner x v w)
                  (-2 * ricciTensor ((Z stage).base.metric t) x v w) (_root_.Set.Ici 0) t) ∧
              (∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                Real.sqrt (normSq0S ((Z stage).base.metric t) x (4 + a)
                  (iteratedCovariantTimeDerivWithin (Z stage).base.metric
                    (fun r => nablaKRm04Field (Z stage) r a x) (_root_.Set.Icc 0 τ) b t)) ≤ B N) ∧
              (∀ x ∈ Metric.ball (0 : E3) (R + 1), ∀ v w : E3,
                ((Z stage).base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (metricTruncation (G T) R (by linarith [le_max_right transitionEnd 2])).inner x v w) ∧
              (∀ (x : E3), ‖x‖ ≤ R - 2 → ∀ v w : E3,
                ((Z stage).base.metric 0).inner (compactDoubleCapMap north R x)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
                    (G T).inner x v w) ∧
              (∀ t ∈ _root_.Set.Icc 0 τ, MetricUniformEquivalentOn _root_.Set.univ
                ((Z stage).base.metric 0) ((Z stage).base.metric t) ΛZ) ∧
              (∀ N : ℕ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                metricCovDerivNorm N ((Z stage).base.metric t) ((Z stage).base.metric 0) x ≤ CZ N) ∧
              ∀ N : ℕ, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
                metricDerivNorm N ((Z stage).base.metric s) ((Z stage).base.metric t)
                  ((Z stage).base.metric 0) x ≤ LZ N * |s - t|) ∧
              let Φ := compactCorePointedMaps (G T) north Z hZ
              let hsrc := compactCorePointedMaps_sourceSigma (G T) north Z hZ
              let htgt := compactCorePointedMaps_targetSigma (G T) north Z hZ
              ∃ bf : BumpFamily Φ,
              ∃ co : FlowMetricConvergenceData Φ (G T) bf hsrc htgt 0 τ,
                (∀ stage t, t ∈ _root_.Set.Icc 0 τ →
                  letI : TopologicalSpace (SourceDomain Φ stage) := sourceDomTop Φ stage
                  letI : ChartedSpace E3 (SourceDomain Φ stage) := sourceDomCharted Φ stage
                  letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ stage) := sourceDomSmooth Φ stage
                  ∀ (y : SourceDomain Φ stage) (v : TangentSpace (𝓡 3) y),
                    ΛZ⁻¹ * (G T).inner y.val v v ≤
                      (sourceMetric Φ hsrc htgt stage t).inner y v v) ∧
                (∀ q : ℕ, ∃ Cq : ℝ, ∀ stage t, t ∈ _root_.Set.Icc 0 τ → ∀ x ∈ bf.grow stage,
                  metricCovDerivNorm q (gSeqExt Φ (G T) bf hsrc htgt stage t) (G T) x ≤ Cq) ∧
                co.gInf 0 = G T ∧
                (∀ t ∈ _root_.Set.Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
                (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
                  ContinuousOn
                    (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (co.gInf p.1) x₀ i j) p.2)
                    (_root_.Set.Icc 0 τ ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
                (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
                  ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
                    (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) x₀ p.2 i j)
                    (_root_.Set.Icc 0 τ ×ˢ (_root_.FiberBundle.trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
                (∀ t ∈ _root_.Set.Ioo 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
                  HasDerivAt (fun r => (co.gInf r).inner x v w)
                    (-2 * ricciTensor (co.gInf t) x v w) t) ∧
                (∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
                  ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
                    metricDerivNorm a (co.gInf s) (co.gInf t) (G T) x ≤ Lp * |s - t|) ∧
                ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : E3,
                  Real.sqrt (normSq0S (co.gInf t) x 4 (metricRm04 (co.gInf t) x)) ≤ 567 * B 0 := by
  obtain ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, hfamily⟩ :=
      standard_uniform_terminal_compact_metric_bounds
  refine ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows⟩ := hfamily S T hT hTα hTS
  refine ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows, ?_⟩
  intro north
  choose Z hZ hz hcomp hg hp hm hfull hcore heZ hcZ hlZ using
    (fun j : ℕ => hflows north (compactCapApproximationRadius (j + 2))
      (compactCapApproximationRadius_large (j + 2)) (compactCapCoreApproximationRadius_large j))
  refine ⟨Z, hZ, (fun j => ⟨hz j, hcomp j, hg j, hp j, hm j,
    hfull j, hcore j, heZ j, hcZ j, hlZ j⟩), ?_⟩
  let Φ := compactCorePointedMaps (G T) north Z hZ
  let hsrc := compactCorePointedMaps_sourceSigma (G T) north Z hZ
  let htgt := compactCorePointedMaps_targetSigma (G T) north Z hZ
  have hi := compactCorePointedMaps_initial (G T) north Z hZ hz
  obtain ⟨hesrc, hbounds⟩ :=
    compactCorePointedMaps_reference_bounds (G T) north Z hZ hz τ ΛZ CZ LZ hCZ hLZ heZ hcZ hlZ
  obtain ⟨bf, co, hbound, hcovTail, hinit, hcomplete, hjlim, hglim, hplim, hllim⟩ :=
    exists_complete_closed_reference_limit Φ τ hτ subset_rfl subset_rfl
      (hc T ⟨hT.le, le_rfl⟩).complete hsrc htgt ΛZ hΛZ hi hesrc hbounds
  refine ⟨bf, co, hbound, hcovTail, hinit, hcomplete, hjlim, hglim, hplim, hllim, ?_⟩
  have hRicSeq := fun j => ricci_bound_of_mixed_zero τ hτ (Z j) (B 0)
    (hm j 0 0 0 (by norm_num))
  intro t ht x
  have hlow : 0 < ΛZ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛZ)
  have hconv := co.ricNorm_convergence_at Φ (G T) bf hsrc htgt 0 τ ΛZ⁻¹ hlow hbound hcovTail ht x
  have hRic : normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x) ≤ 81 * (B 0) ^ 2 := by
    apply le_of_tendsto hconv
    exact Filter.Eventually.of_forall (fun j => hRicSeq (co.φ j) t ht _)
  have hsqrt : Real.sqrt (normSq0S (co.gInf t) x 2 (metricRicci (co.gInf t) x)) ≤ 9 * B 0 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num) (hB 0), by nlinarith only [hRic]⟩
  have hthree := sqrt_normSq_metricRm04_le_ricci_three (co.gInf t) x
    (by change Module.finrank ℝ E3 = 3; exact finrank_euclideanSpace_fin)
  nlinarith only [hsqrt, hthree]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_core_limits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_core_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_core_limits ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_terminal_core_limits
end DifferentialGeometry.PDE.RicciFlow
