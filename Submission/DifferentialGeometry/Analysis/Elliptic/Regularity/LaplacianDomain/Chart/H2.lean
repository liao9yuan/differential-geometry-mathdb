import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ManifoldH2.NonSmooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.WeakPartialDerivativeBound
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.Density.Smooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainH2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem chartH2_localBound_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ 1 →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room :
      Metric.cthickening (1 : ℝ) (closure Ω'') ⊆
        chartTargetEuclid (I := I) (M := M) α) :
    ∃ (MBound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∀ i k, 0 ≤ MBound i k) ∧
      (∀ i k : Fin (Module.finrank ℝ E),
        ∃ g_ik : EuclN → ℝ,
          _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            ((chartBilinearH1ComplDataOfLaplacianDomain
              (I := I) (M := M) g α hu_h).weakPartial i) Ω'' ∧
          _root_.MeasureTheory.eLpNorm g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (MBound i k)) := by
  classical
  set D := chartBilinearH1ComplDataOfLaplacianDomain
    (I := I) (M := M) g α hu_h with hD_def
  obtain ⟨MBound, hM_nn, h_uniform_bd⟩ :=
    uniform_diffQuot_weakPartial_bound
      (I := I) (M := M) (g := g) (α := α) D
      hη hη_support hη_range hN h_fderiv_eta
      hΩ' hΩ'_chart hΩ'_compact hη_in_Ω' (R₀ := 1) one_pos hh_support_in_Ω'
      hη_one_on_Ω'' hΩ''_open.measurableSet
  have hh₀ : (0 : ℝ) < 1 := by norm_num
  have h_h2 :=
    exists_weak_second_partial_of_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hh₀ h_room
      hM_nn h_uniform_bd
  exact ⟨MBound, hM_nn, h_h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.chartH2_localBound_of_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.chartH2_localBound_of_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.chartH2_localBound_of_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainH2.chartH2_localBound_of_laplacianDomain

end LaplacianDomainH2
end Laplacian
end Analysis
end DifferentialGeometry
