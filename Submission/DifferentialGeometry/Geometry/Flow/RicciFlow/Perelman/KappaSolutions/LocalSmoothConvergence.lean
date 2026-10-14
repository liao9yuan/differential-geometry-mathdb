import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialJetTimeContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem mapCInfConvOnCompacts_of_locally {U : Set E} {f : ℕ → E → F} {f₀ : E → F}
    (hloc : ∀ x ∈ U, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ MapCInfConvergenceOnCompacts W f f₀) :
    MapCInfConvergenceOnCompacts U f f₀ := by
  classical
  intro K hK hKU m ε hε
  choose W hW hxW hconv using fun x : K => hloc x.val (hKU x.property)
  have hcompact (x : K) : ∃ L : Set E, IsCompact L ∧ {x.val} ⊆ interior L ∧ L ⊆ W x :=
    exists_compact_between isCompact_singleton (hW x) (singleton_subset_iff.mpr (hxW x))
  choose L hL hxL hLW using hcompact
  obtain ⟨T, hcover⟩ := hK.elim_finite_subcover (fun x : K => interior (L x))
    (fun _ => isOpen_interior)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxL ⟨y, hy⟩ (_root_.Set.mem_singleton y)⟩)
  choose N hN using fun x : K => hconv x (L x) (hL x) (hLW x) m ε hε
  refine ⟨T.sup N, fun n hn r hr y hy => ?_⟩
  obtain ⟨x, hxT, hyL⟩ := mem_iUnion₂.mp (hcover hy)
  exact hN x n ((Finset.le_sup hxT).trans hn) r hr y (interior_subset hyL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mapCInfConvOnCompacts_of_locally then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mapCInfConvOnCompacts_of_locally"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mapCInfConvOnCompacts_of_locally ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mapCInfConvOnCompacts_of_locally

end Calculus

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]


theorem solution_chartGram_mapCInf_of_carrier_time_sequence {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (ht : t ≤ b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ≤ b)
    (hτt : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  apply mapCInfConvOnCompacts_of_locally
  intro y hy
  obtain ⟨W, hW, hxW, _hWt, hconv⟩ := solution_chartGram_mapCInf_of_time_tendsto
    S hS hcarrier hregular ht p ((extChartAt I p).symm y) ((extChartAt I p).map_target hy)
  refine ⟨W, hW, ?_, hconv τ hτ hτt i j⟩
  simpa only [(extChartAt I p).right_inv hy] using hxW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_carrier_time_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_carrier_time_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_carrier_time_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_carrier_time_sequence

theorem solution_chartGram_mapCInf_of_closedWindow_time_sequence {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ _root_.Set.Icc c b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ _root_.Set.Icc c b)
    (hτt : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  rcases ht.2.lt_or_eq with htb | htb
  · intro K hK hKt m
    apply mapCPConvergenceOn_of_tendstoUniformlyOn (isOpen_extChartAt_target p) hKt
      (fun n => (chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p i j).of_le
        (by exact_mod_cast le_top))
      ((chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j).of_le
        (by exact_mod_cast le_top))
    intro r _hr
    exact (solution_chartGram_jets_tendsto_regular S hS
      (hregular ⟨hac.trans_le ht.1, htb⟩) p hK hKt r i j).seq_tendstoUniformlyOn τ hτt
  · subst t
    let : ProperSpace E := FiniteDimensional.proper ℝ E
    apply mapCInfConvOnCompacts_of_locally
    intro y hy
    obtain ⟨W, hW, hyW, hWt, htime⟩ := solution_chartGram_jets_tendsto_terminal_at_chart_point
      S hS (hac.trans hcb) hslab hregular p ((extChartAt I p).symm y)
      ((extChartAt I p).map_target hy)
    refine ⟨W, hW, ?_, ?_⟩
    · simpa only [(extChartAt I p).right_inv hy] using hyW
    · intro K hK hKW m
      apply mapCPConvergenceOn_of_tendstoUniformlyOn hW hKW
        (fun n => ((chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p i j).mono hWt).of_le
          (by exact_mod_cast le_top))
        (((chartGramOnE_contDiffOn (I := I) (S.base.metric b) p i j).mono hWt).of_le
          (by exact_mod_cast le_top))
      intro r _hr
      have hu : TendstoUniformlyOn (fun s => iteratedFDeriv ℝ r
          (chartGramOnE (I := I) (S.base.metric s) p i j))
          (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric b) p i j))
          (𝓝[_root_.Set.Iic b] b) K := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        rw [← _root_.Set.Iio_insert, nhdsWithin_insert, _root_.Filter.eventually_sup, _root_.Filter.eventually_pure]
        constructor
        · exact fun z _hz => by simpa only [dist_self] using hε
        · exact (Metric.tendstoUniformlyOn_iff.mp ((htime r i j).mono hKW)) ε hε
      exact hu.seq_tendstoUniformlyOn τ
        (tendsto_nhdsWithin_iff.mpr ⟨hτt, Filter.Eventually.of_forall (fun n => (hτ n).2)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closedWindow_time_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closedWindow_time_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closedWindow_time_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.solution_chartGram_mapCInf_of_closedWindow_time_sequence

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
