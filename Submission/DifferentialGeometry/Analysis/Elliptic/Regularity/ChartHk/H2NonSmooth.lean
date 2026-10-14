import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.LocalWeakLimit
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2

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

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_weak_second_partial_of_uniform_diffQuot_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {MBound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (hM_nn : ∀ i k, 0 ≤ MBound i k)
    (h_uniform_bd :
      ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
        (h : ℝ), 0 < |h| → |h| ≤ h₀ →
          _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
              ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'')
            ≤ ENNReal.ofReal (MBound i k)) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (D.weakPartial i) Ω'' ∧
      _root_.MeasureTheory.eLpNorm g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ≤
        ENNReal.ofReal (MBound i k) := by
  classical
  intro i k
  have h_cthick_compact : IsCompact (Metric.cthickening h₀ (closure Ω'')) :=
    hΩ''_compact_closure.cthickening
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :=
    h_cthick_compact.exists_cthickening_subset_open
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_room
  set Ω : Set EuclN := Metric.thickening δ (Metric.cthickening h₀ (closure Ω''))
    with hΩ_def
  have hΩ_open : IsOpen Ω := Metric.isOpen_thickening
  have h_cthick_in_Ω : Metric.cthickening h₀ (closure Ω'') ⊆ Ω :=
    Metric.self_subset_thickening hδ_pos _
  have hΩ_in_cthick : Ω ⊆ Metric.cthickening δ (Metric.cthickening h₀ (closure Ω'')) :=
    Metric.thickening_subset_cthickening _ _
  have h_cthick_outer_compact :
      IsCompact (Metric.cthickening δ (Metric.cthickening h₀ (closure Ω''))) :=
    h_cthick_compact.cthickening
  have h_closureΩ_subset :
      closure Ω ⊆ Metric.cthickening δ (Metric.cthickening h₀ (closure Ω'')) := by
    apply closure_minimal hΩ_in_cthick Metric.isClosed_cthickening
  have h_closureΩ_compact : IsCompact (closure Ω) :=
    h_cthick_outer_compact.of_isClosed_subset isClosed_closure h_closureΩ_subset
  have hΩ_in_chart : closure Ω ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ_subset.trans hδ_subset
  have h_room_Ω : Metric.cthickening h₀ (closure Ω'') ⊆ Ω := h_cthick_in_Ω
  have h_closureΩ''_in_Ω : closure Ω'' ⊆ Ω := by
    intro y hy
    apply h_cthick_in_Ω
    apply Metric.self_subset_cthickening _ hy
  have h_wp_memLp_closureΩ :
      _root_.MeasureTheory.MemLp (D.weakPartial i) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω)) :=
    D.weak_partial_locally_memLp i (closure Ω) h_closureΩ_compact hΩ_in_chart
  have h_wp_memLp_Ω :
      _root_.MeasureTheory.MemLp (D.weakPartial i) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω) :=
    h_wp_memLp_closureΩ.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      _root_.MeasureTheory.eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'')
        ≤ ENNReal.ofReal (MBound i k) :=
    fun h hh hh_le => h_uniform_bd i k h hh hh_le
  obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩ :=
    hasWeakPartialDeriv_of_diffQuot_uniform_bound_local
      (d := Module.finrank ℝ E)
      hΩ_open hΩ''_open hΩ''_compact_closure
      hh₀ h_room_Ω h_wp_memLp_Ω k (hM_nn i k) h_bdd
  exact ⟨g_ik, hg_ik_memLp, hg_ik_partial, hg_ik_norm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_of_uniform_diffQuot_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_of_uniform_diffQuot_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_of_uniform_diffQuot_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth.exists_weak_second_partial_of_uniform_diffQuot_bound

end ChartH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
