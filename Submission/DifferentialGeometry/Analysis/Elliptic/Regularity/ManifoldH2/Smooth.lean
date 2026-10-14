import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.ChartLocalLaplacian
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
theorem local_chart_pulled
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {w F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution w F)
    (hF_l2_local : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      _root_.MeasureTheory.MemLp F 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g : EuclN → ℝ,
      _root_.MeasureTheory.MemLp g 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g
        (fun y : EuclN => (fderiv ℝ w y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ w x) (EuclideanSpace.single j 1))^2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω', (w x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EuclN) := by
    intro y _; exact Set.mem_univ _
  obtain ⟨C, hC_nn, h_eng⟩ := local_smooth_solution
    (d := Module.finrank ℝ E)
    B hΩ'' hΩ''_compact_closure h_room
  intro i k
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_weak hF_l2_local i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled

omit [NeZero (Module.finrank ℝ E)] in
omit [FiniteDimensional ℝ E] in
theorem memLp_two_continuous_compactSupport_restrict
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (Ω' : Set EuclN) :
    MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω') := by
  have h_global : _root_.MeasureTheory.MemLp f 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    hf_cont.memLp_of_hasCompactSupport (μ := _root_.MeasureTheory.MeasureSpace.volume) (p := 2) hf_cs
  exact h_global.restrict _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.memLp_two_continuous_compactSupport_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ManifoldH2.memLp_two_continuous_compactSupport_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.memLp_two_continuous_compactSupport_restrict ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.memLp_two_continuous_compactSupport_restrict

theorem local_chart_pulled_manifold
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_cs : HasCompactSupport u)
    (hu_support : tsupport u ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E)
      (Set.univ : Set EuclN))
    {F : EuclN → ℝ}
    (h_weak : B.IsSmoothWeakSolution
      (chartPullback (I := I) α u) F)
    (hF_l2_local : ∀ {Ω' : Set EuclN}, IsCompact (closure Ω') →
      _root_.MeasureTheory.MemLp F 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'))
    {Ω'' : Set EuclN} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∀ i k : Fin (Module.finrank ℝ E), ∃ g_ik : EuclN → ℝ,
      _root_.MeasureTheory.MemLp g_ik 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (fun y : EuclN => (fderiv ℝ (chartPullback (I := I) α u) y)
          (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set EuclN, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧
        closure Ω' ⊆ (Set.univ : Set EuclN) ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g_ik x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((fderiv ℝ (chartPullback (I := I) α u) x)
                      (EuclideanSpace.single j 1))^2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω', (chartPullback (I := I) α u x)^2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) +
              ∫ x in Ω', (F x)^2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
  let _ := g
  let _ := hu_smooth
  let _ := hu_cs
  let _ := hu_support
  exact local_chart_pulled (E := E)
    B h_weak hF_l2_local hΩ'' hΩ''_compact_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled_manifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled_manifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled_manifold ``Submission.DifferentialGeometry.Analysis.Laplacian.ManifoldH2.local_chart_pulled_manifold

end ManifoldH2
end Laplacian
end Analysis
end DifferentialGeometry
