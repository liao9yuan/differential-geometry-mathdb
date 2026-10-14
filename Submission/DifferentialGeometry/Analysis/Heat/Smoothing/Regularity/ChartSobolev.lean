import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.SmoothRepresentative
import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Spectral.IteratedDomain
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Powers.EvenOrderBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartSideH2kBridge_iff_memWkpChart_two_k
    (k : ℕ) (u : M → ℝ) :
    ChartSideH2kBridge (I := I) (M := M) k u ↔
      MemWkpChart (I := I) (M := M) (2 * k) 2 u := by
  refine ⟨fun h => memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) k h, fun h => ?_⟩
  intro α
  exact h α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_iff_memWkpChart_two_k then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_iff_memWkpChart_two_k"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_iff_memWkpChart_two_k ``Submission.DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_iff_memWkpChart_two_k

theorem heatSemigroup_smooth_representative_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    {t : ℝ}
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  have h_iterated_regularity : ∀ k : ℕ,
      MemWkpChart (I := I) (M := M) (2 * k) 2
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
    intro k
    exact (chartSideH2kBridge_iff_memWkpChart_two_k
      (I := I) (M := M) k _).mp (h_bridges k)
  exact heatSemigroup_smooth_representative (I := I) (M := M) g u_0
    h_iterated_regularity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_chartSideBridges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_chartSideBridges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_chartSideBridges ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative_of_chartSideBridges

theorem heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges_uniform :
      ∀ t : ℝ, 0 < t → ∀ k : ℕ,
        ChartSideH2kBridge (I := I) (M := M) k
          (((heatSemigroup (I := I) (M := M) g t u_0 :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (∀ t : ℝ, 0 < t →
      ∃ u_smooth_t : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth_t ∧
        ((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] u_smooth_t) ∧
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact heatSemigroup_smooth_representative_of_chartSideBridges
      (I := I) (M := M) g u_0 (h_bridges_uniform t ht)
  · exact heatSemigroup_contMDiff_in_time (I := I) (M := M) g u_0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_chartSideBridges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_chartSideBridges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_chartSideBridges ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_chartSideBridges

theorem chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        ChartSideH2kBridge (I := I) (M := M) k
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_⟩
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact h_bridges k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts ``Submission.DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts

theorem laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        MemWkpChart (I := I) (M := M) (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
        wkpNormChart (I := I) (M := M) (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq, h_bridge_lift⟩ :=
    chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
      (I := I) (M := M) g ht u_0 h_bridges k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k h_bridge_lift).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k h_bridge_lift).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat ``Submission.DifferentialGeometry.Analysis.HeatEquation.laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat

theorem chartSideH2kBridge_heat_zero
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) 0
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, _hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 0
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_zero (I := I) (M := M) g u_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_zero ``Submission.DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_zero

theorem chartSideH2kBridge_heat_one
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) 1
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 1
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_one (I := I) (M := M) g hu_h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_one ``Submission.DifferentialGeometry.Analysis.HeatEquation.chartSideH2kBridge_heat_one

end HeatEquation
end Analysis
end DifferentialGeometry

end
