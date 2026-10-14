import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalSmoothConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRicciJetOperators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientConnectionC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientConnectionC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientConnectionC1 target :: scope.openDecls } }


theorem solution_chartChristoffel_jets_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (ht : t ≤ b) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) (r : ℕ) :
    ContinuousWithinAt
      (fun s => iteratedFDeriv ℝ r (chartChristoffel (I := I) (S.base.metric s) p i j k) y)
      (_root_.Set.Iic b) t := by
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := _root_.Set.Iic b) (x := t) ht]
  apply tendsto_iff_seq_tendsto.mpr
  intro τ hτ
  have hτt : _root_.Filter.Tendsto (fun n => (τ n).val) _root_.Filter.atTop (𝓝 t) :=
    continuous_subtype_val.continuousAt.tendsto.comp hτ
  have hW := isOpen_extChartAt_target (I := I) p
  have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
    hcarrier hregular ht p (fun n => (τ n).val) (fun n => (τ n).property) hτt
  have hchr := mapCInfConvergence_chartChristoffel_of_gram
    (fun n => S.base.metric (τ n).val) (S.base.metric t) p hW (fun _ hx => hx) hgram i j k
  have hs (s : ℝ) : ContDiffOn ℝ ∞
      (chartChristoffel (I := I) (S.base.metric s) p i j k) (extChartAt I p).target := by
    simpa only [hW.interior_eq] using
      chartChristoffel_contDiffOn_interior (I := I) (S.base.metric s) p i j k
  exact (MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv hW isCompact_singleton
    (singleton_subset_iff.mpr hy) hchr (fun n => hs (τ n).val) (hs t) r).tendsto_at
      (_root_.Set.mem_singleton y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_jets_continuousWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_jets_continuousWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_jets_continuousWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_jets_continuousWithinAt


theorem solution_chartChristoffel_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (ht : t ≤ b) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt (fun s => chartChristoffel (I := I) (S.base.metric s) p i j k y)
      (_root_.Set.Iic b) t := by
  rw [continuousWithinAt_iff_continuousAt_domRestrict _ (s := _root_.Set.Iic b) (x := t) ht]
  apply tendsto_iff_seq_tendsto.mpr
  intro τ hτ
  have hτt : _root_.Filter.Tendsto (fun n => (τ n).val) _root_.Filter.atTop (𝓝 t) :=
    continuous_subtype_val.continuousAt.tendsto.comp hτ
  have hgram := solution_chartGram_mapCInf_of_carrier_time_sequence S hS
    hcarrier hregular ht p (fun n => (τ n).val) (fun n => (τ n).property) hτt
  have hchr := mapCInfConvergence_chartChristoffel_of_gram
    (fun n => S.base.metric (τ n).val) (S.base.metric t) p
    (isOpen_extChartAt_target (I := I) p) (fun _ hx => hx) hgram i j k
  exact (tendstoUniformlyOn_of_cPConvergence
    (hchr {y} isCompact_singleton (singleton_subset_iff.mpr hy) 0)).tendsto_at
      (_root_.Set.mem_singleton y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_continuousWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_continuousWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_continuousWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartChristoffel_continuousWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
