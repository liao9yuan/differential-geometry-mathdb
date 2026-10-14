import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.WeakPartialDerivativeBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartH2NonSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_second_partial_bound_by_geometric_constant
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_open : IsOpen Ω'') (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ C_geom i k) ∧
      ∀ (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
        (i k : Fin (Module.finrank ℝ E)),
        ∃ g_ik : EuclN → ℝ,
          _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
          DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
            (D.weakPartial i) Ω'' ∧
          _root_.MeasureTheory.eLpNorm g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ≤
            ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (_root_.MeasureTheory.eLpNorm (D.weakPartial l) 2
                  ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (_root_.MeasureTheory.eLpNorm D.uChart 2
                  ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (_root_.MeasureTheory.eLpNorm D.fChart 2
                  ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    uniform_diffQuot_weakPartial_bound_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      hη hη_support hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_support_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  refine ⟨C_geom, hC_geom_nn, fun D i k => ?_⟩
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    exists_weak_second_partial_of_uniform_diffQuot_bound (I := I) (M := M) (g := g) (α := α)
      D hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      (MBound := fun i k => C_geom i k * Real.sqrt (
        (∑ l : Fin (Module.finrank ℝ E),
          (_root_.MeasureTheory.eLpNorm (D.weakPartial l) 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        + (_root_.MeasureTheory.eLpNorm D.uChart 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2
        + (_root_.MeasureTheory.eLpNorm D.fChart 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2))
      (hM_nn := fun i k => mul_nonneg (hC_geom_nn i k) (Real.sqrt_nonneg _))
      (h_uniform_bd := fun i k h hpos hle => hC_geom D hpos hle)
      i k
  exact ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_bound_by_geometric_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_bound_by_geometric_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_bound_by_geometric_constant ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_bound_by_geometric_constant

end ChartH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
