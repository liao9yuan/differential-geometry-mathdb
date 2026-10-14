import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.UniformParameter
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.JetOperators
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalSmoothConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TimeJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJointSpatialJets
import Submission.DifferentialGeometry.Analysis.Calculus.MapConvergence.UniformParameter
import Submission.DifferentialGeometry.Topology.LocallyUniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance uniformOrdinaryC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformOrdinaryC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformOrdinaryC1 target :: scope.openDecls } }


theorem solution_chartGram_mapCInf_of_closed_time_sequence {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ _root_.Set.Icc c b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ _root_.Set.Icc c b)
    (hτt : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  exact mapCInfConvergenceOnCompacts_of_continuous_spatial_jets
    (isOpen_extChartAt_target (I := I) p)
    (fun t _ => chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j)
    (fun r => CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
      S hS hac hcb hslab hreg p r i j) τ hτ ht hτt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closed_time_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closed_time_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closed_time_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closed_time_sequence

theorem uniform_ordinary_metric_jets_on_compact_time {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {b : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Iic b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Iic b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Iic b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let F (T : SolutionOn (I := I) (M := M) D) (t : ℝ) (y : E) : ℝ :=
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (_root_.Set.Iic b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
  have hmodelGram (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) (t : ℝ) (ht : t ∈ J)
      (htend : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
      MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) (S₀.base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) := by
    intro Q hQ hQU m
    exact solution_chartGram_mapCInf_of_carrier_time_sequence S₀ hS₀ hcarrier hregular
      (hJb ht) p τ (fun n => hJb (hτ n)) htend i j Q hQ (hQU.trans hUt) m
  apply uniform_spatial_jets_of_sequential_convergence hU hJ.isSeqCompact
    (fun n => F (S n)) (F S₀)
    (fun n t ht => ordinary_metric_time_jet_components_contDiffOn (S n) (hS n)
      hcarrier hregular (hJb ht) q p hUt slots)
    (fun t ht => ordinary_metric_time_jet_components_contDiffOn S₀ hS₀
      hcarrier hregular (hJb ht) q p hUt slots) (K := K) (r := r)
  · intro θ hθ τ hτ t ht htend
    have hsourceGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) ((S (θ n)).base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) :=
      mapCInfConvergenceOnCompacts_of_uniform_spatial_jets hU
        (fun n t => chartGramOnE (I := I) ((S n).base.metric t) p i j)
        (fun t => chartGramOnE (I := I) (S₀.base.metric t) p i j)
        (fun n t _ => (chartGramOnE_contDiffOn (I := I) ((S n).base.metric t) p i j).mono hUt)
        (fun t _ => (chartGramOnE_contDiffOn (I := I) (S₀.base.metric t) p i j).mono hUt)
        (hgram i j) θ hθ τ hτ ht (hmodelGram τ hτ t ht htend i j)
    exact ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun n => S (θ n)) (fun n => hS (θ n)) S₀ hS₀
      hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt hsourceGram q slots
  · intro τ hτ t ht htend
    exact ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun _ => S₀) (fun _ => hS₀) S₀ hS₀
      hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt (hmodelGram τ hτ t ht htend) q slots
  · exact hK
  · exact hKU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time

theorem uniform_ordinary_metric_jets_on_compact_time_of_closed_interval {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let F (T : SolutionOn (I := I) (M := M) D) (t : ℝ) (y : E) : ℝ :=
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (_root_.Set.Icc c b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
  have hmodelGram (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) (t : ℝ) (ht : t ∈ J)
      (htend : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
      MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) (S₀.base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) := by
    intro Q hQ hQU m
    exact solution_chartGram_mapCInf_of_closed_time_sequence S₀ hS₀ hac hcb (by rw [hcarrier]) hregular
      (hJb ht) p τ (fun n => hJb (hτ n)) htend i j Q hQ (hQU.trans hUt) m
  apply uniform_spatial_jets_of_sequential_convergence hU hJ.isSeqCompact
    (fun n => F (S n)) (F S₀)
    (fun n t ht => ordinary_metric_time_jet_components_contDiffOn_of_closed_interval (S n) (hS n)
      hac hcb hcarrier hregular (hJb ht) q p hUt slots)
    (fun t ht => ordinary_metric_time_jet_components_contDiffOn_of_closed_interval S₀ hS₀
      hac hcb hcarrier hregular (hJb ht) q p hUt slots) (K := K) (r := r)
  · intro θ hθ τ hτ t ht htend
    have hsourceGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) ((S (θ n)).base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) :=
      mapCInfConvergenceOnCompacts_of_uniform_spatial_jets hU
        (fun n t => chartGramOnE (I := I) ((S n).base.metric t) p i j)
        (fun t => chartGramOnE (I := I) (S₀.base.metric t) p i j)
        (fun n t _ => (chartGramOnE_contDiffOn (I := I) ((S n).base.metric t) p i j).mono hUt)
        (fun t _ => (chartGramOnE_contDiffOn (I := I) (S₀.base.metric t) p i j).mono hUt)
        (hgram i j) θ hθ τ hτ ht (hmodelGram τ hτ t ht htend i j)
    exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
      (fun n => S (θ n)) (fun n => hS (θ n)) S₀ hS₀
      hac hcb hac hcb hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt hsourceGram q slots
  · intro τ hτ t ht htend
    exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
      (fun _ => S₀) (fun _ => hS₀) S₀ hS₀
      hac hcb hac hcb hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt (hmodelGram τ hτ t ht htend) q slots
  · exact hK
  · exact hKU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time_of_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time_of_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time_of_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_on_compact_time_of_closed_interval

theorem uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J,
        metricDerivNormSupOn K r ((S n).base.metric t) (S₀.base.metric t) R < epsilon)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  apply uniform_ordinary_metric_jets_on_compact_time_of_closed_interval S hS S₀ hS₀
    hac hcb hcarrier hregular hJ hJb p hU hUt _ hK hKU r q slots
  intro i j Q hQ hQU r epsilon hepsilon
  exact chartGram_jets_uniform_of_metric_convergence (fun n => (S n).base.metric) S₀.base.metric
    R hconv p i j hQ (hQU.trans hUt) r hepsilon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval

theorem uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M) (i j : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I p).target) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (g n t) p i j) y -
        iteratedFDeriv ℝ r (chartInvGramOnE (I := I) (S.base.metric t) p i j) y‖ ≤ epsilon := by
  apply uniform_spatial_jets_chartInvGram_of_gram hJ.isSeqCompact g S.base.metric p
    (isOpen_extChartAt_target (I := I) p) Subset.rfl _ _ i j hK hKt r
  · intro i j Q hQ hQt r epsilon hepsilon
    exact chartGram_jets_uniform_of_metric_convergence g S.base.metric R hconv
      p i j hQ hQt r hepsilon
  · intro i j r
    exact (CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
      S hS hac hcb hslab hreg p r i j).mono (_root_.Set.prod_mono_left hJb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval

omit [NeZero (Module.finrank ℝ E)] in
theorem uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M) (i j k : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I p).target) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (chartChristoffel (I := I) (g n t) p i j k) y -
        iteratedFDeriv ℝ r (chartChristoffel (I := I) (S.base.metric t) p i j k) y‖ ≤ epsilon := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (Fin.pos i)⟩
  apply uniform_spatial_jets_chartChristoffel_of_gram hJ.isSeqCompact g S.base.metric p
    (isOpen_extChartAt_target (I := I) p) Subset.rfl _ _ i j k hK hKt r
  · intro i j Q hQ hQt r epsilon hepsilon
    exact chartGram_jets_uniform_of_metric_convergence g S.base.metric R hconv
      p i j hQ hQt r hepsilon
  · intro i j r
    exact (CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
      S hS hac hcb hslab hreg p r i j).mono (_root_.Set.prod_mono_left hJb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval

theorem uniform_metricScalar_jets_of_metric_convergence_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I p).target) (r : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => metricScalarAt (g n t) ((extChartAt I p).symm z)) y -
        iteratedFDeriv ℝ r
          (fun z => metricScalarAt (S.base.metric t) ((extChartAt I p).symm z)) y‖ ≤ epsilon := by
  apply uniform_spatial_jets_metricScalar_of_gram hJ.isSeqCompact g S.base.metric p
    (isOpen_extChartAt_target (I := I) p) Subset.rfl _ _ hK hKt r
  · intro i j Q hQ hQt r epsilon hepsilon
    exact chartGram_jets_uniform_of_metric_convergence g S.base.metric R hconv
      p i j hQ hQt r hepsilon
  · intro i j r
    exact (CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
      S hS hac hcb hslab hreg p r i j).mono (_root_.Set.prod_mono_left hJb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metricScalar_jets_of_metric_convergence_on_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metricScalar_jets_of_metric_convergence_on_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metricScalar_jets_of_metric_convergence_on_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metricScalar_jets_of_metric_convergence_on_closed_interval

omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGram_locally_uniform_of_metric_convergence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M) (i j : Fin (Module.finrank ℝ E)) :
    TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E) => chartInvGramOnE (I := I) (g n z.1) p i j z.2)
      (fun z => chartInvGramOnE (I := I) (S.base.metric z.1) p i j z.2) _root_.Filter.atTop
      (_root_.Set.Ioo c b ×ˢ (extChartAt I p).target) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (Fin.pos i)⟩
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) p))).mpr
  intro Q hQt hQ
  have hK : IsCompact (Prod.snd '' Q) := hQ.image continuous_snd
  have hKt : Prod.snd '' Q ⊆ (extChartAt I p).target := by
    rintro y ⟨z, hz, rfl⟩
    exact (hQt hz).2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_chartInvGram_jets_of_metric_convergence_on_closed_interval
    S hS hac hcb hslab hreg g R _root_.CompactIccSpace.isCompact_Icc Subset.rfl hconv p i j hK hKt 0
      (epsilon / 2) (half_pos hepsilon)
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
  intro z hz
  have hh := hN n hn z.1 ⟨(hQt hz).1.1.le, (hQt hz).1.2.le⟩ z.2 ⟨z, hz, rfl⟩
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] at hh
  rw [dist_comm, dist_eq_norm]
  exact hh.trans_lt (half_lt_self hepsilon)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartInvGram_locally_uniform_of_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartInvGram_locally_uniform_of_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartInvGram_locally_uniform_of_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartInvGram_locally_uniform_of_metric_convergence

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_locally_uniform_of_metric_convergence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r (g n t) (S.base.metric t) R < epsilon)
    (p : M) (i j k : Fin (Module.finrank ℝ E)) :
    TendstoLocallyUniformlyOn
      (fun n (z : ℝ × E) => chartChristoffel (I := I) (g n z.1) p i j k z.2)
      (fun z => chartChristoffel (I := I) (S.base.metric z.1) p i j k z.2) _root_.Filter.atTop
      (_root_.Set.Ioo c b ×ˢ (extChartAt I p).target) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt (Fin.pos i)⟩
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) p))).mpr
  intro Q hQt hQ
  have hK : IsCompact (Prod.snd '' Q) := hQ.image continuous_snd
  have hKt : Prod.snd '' Q ⊆ (extChartAt I p).target := by
    rintro y ⟨z, hz, rfl⟩
    exact (hQt hz).2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := uniform_chartChristoffel_jets_of_metric_convergence_on_closed_interval
    S hS hac hcb hslab hreg g R _root_.CompactIccSpace.isCompact_Icc Subset.rfl hconv p i j k hK hKt 0
      (epsilon / 2) (half_pos hepsilon)
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
  intro z hz
  have hh := hN n hn z.1 ⟨(hQt hz).1.1.le, (hQt hz).1.2.le⟩ z.2 ⟨z, hz, rfl⟩
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] at hh
  rw [dist_comm, dist_eq_norm]
  exact hh.trans_lt (half_lt_self hepsilon)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffel_locally_uniform_of_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffel_locally_uniform_of_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffel_locally_uniform_of_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffel_locally_uniform_of_metric_convergence

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
