import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialJetTimeContinuity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.UniformSpace.HeineCantor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem derivWithin_time_eq_fderivWithin
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hf : ContDiffOn ℝ ∞ f (J ×ˢ V))
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ V) :
    derivWithin (fun s => f (s, x)) J t =
      fderivWithin ℝ f (J ×ˢ V) (t, x) (1, 0) := by
  have hd := (hf.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt
  have hparam : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hmaps : _root_.Set.MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ V) := fun _ hs => ⟨hs, hx⟩
  exact (hd.comp_hasDerivWithinAt t hparam hmaps).derivWithin (hJ t ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.derivWithin_time_eq_fderivWithin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.derivWithin_time_eq_fderivWithin target :: scope.openDecls } }


theorem contDiffOn_iteratedDerivWithin_time
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ V)) (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => iteratedDerivWithin k (fun s => f (s, q.2)) J q.1)
      (J ×ˢ V) := by
  induction k with
  | zero => simpa only [iteratedDerivWithin_zero] using hf
  | succ k hk =>
    have hd := (hk.fderivWithin (hJ.prod hV.uniqueDiffOn) (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := (1, (0 : E))))
    apply hd.congr
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [iteratedDerivWithin_succ]
    exact derivWithin_time_eq_fderivWithin hJ hk ht hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_iteratedDerivWithin_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_iteratedDerivWithin_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_iteratedDerivWithin_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.contDiffOn_iteratedDerivWithin_time


theorem hasDerivWithinAt_iteratedDerivWithin_time
    {f : ℝ × E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ V)) (k : ℕ)
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ V) :
    HasDerivWithinAt (iteratedDerivWithin k (fun s => f (s, x)) J)
      (iteratedDerivWithin (k + 1) (fun s => f (s, x)) J t) J t := by
  have hk := contDiffOn_iteratedDerivWithin_time hJ hV hf k
  have hd := (hk.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).hasFDerivWithinAt
  have hparam : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hmaps : _root_.Set.MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ V) := fun _ hs => ⟨hs, hx⟩
  have h := hd.comp_hasDerivWithinAt t hparam hmaps
  have heq := derivWithin_time_eq_fderivWithin hJ hk ht hx
  rw [iteratedDerivWithin_succ]
  exact h.congr_deriv heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_iteratedDerivWithin_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_iteratedDerivWithin_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_iteratedDerivWithin_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_iteratedDerivWithin_time

end Calculus

open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]


theorem solution_chartGram_timeJets_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : ℝ × E => iteratedDerivWithin k
          (fun s => chartGramOnE (I := I) (S.base.metric s) p i j q.2) (_root_.Set.Icc c b) q.1)
          (_root_.Set.Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed S hS hac hcb hslab hreg p
  exact ⟨V, hV, hpV, hVt, fun k i j =>
    contDiffOn_iteratedDerivWithin_time (uniqueDiffOn_Icc hcb) hV (hgram i j) k⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_contDiffOn_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_contDiffOn_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_contDiffOn_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_contDiffOn_closed


theorem solution_chartGram_mixedJets_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ r k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun q : ℝ × E => iteratedFDeriv ℝ r
          (fun y => iteratedDerivWithin k
            (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (_root_.Set.Icc c b) q.1) q.2)
          (_root_.Set.Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hjets⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed S hS hac hcb hslab hreg p
  exact ⟨V, hV, hpV, hVt, fun r k i j =>
    KappaSolutions.spatial_iteratedFDeriv_contDiffOn
      (G := fun s y => iteratedDerivWithin k
        (fun u => chartGramOnE (I := I) (S.base.metric u) p i j y) (_root_.Set.Icc c b) s)
      hV (hjets k i j) r⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_mixedJets_contDiffOn_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_mixedJets_contDiffOn_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_mixedJets_contDiffOn_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_mixedJets_contDiffOn_closed


theorem solution_chartGram_timeJets_mapCInf_of_time_sequence
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      ∀ tau : ℕ → ℝ, (∀ n, tau n ∈ _root_.Set.Icc c b) → ∀ t ∈ _root_.Set.Icc c b,
        _root_.Filter.Tendsto tau _root_.Filter.atTop (𝓝 t) → ∀ k : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.CheegerGromovCompactness.MapCInfConvergenceOnCompacts V
            (fun n y => iteratedDerivWithin k
              (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (_root_.Set.Icc c b) (tau n))
            (fun y => iteratedDerivWithin k
              (fun s => chartGramOnE (I := I) (S.base.metric s) p i j y) (_root_.Set.Icc c b) t) := by
  obtain ⟨V, hV, hpV, hVt, htime⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed S hS hac hcb hslab hreg p
  refine ⟨V, hV, hpV, hVt, ?_⟩
  intro tau htau t ht htend k i j
  exact DifferentialGeometry.CheegerGromovCompactness.mapCInfConvergenceOnCompacts_of_tendsto_parameter
    (G := fun s y => iteratedDerivWithin k
      (fun u => chartGramOnE (I := I) (S.base.metric u) p i j y) (_root_.Set.Icc c b) s)
    hV (htime k i j) tau htau ht htend

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_mapCInf_of_time_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_mapCInf_of_time_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_mapCInf_of_time_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_timeJets_mapCInf_of_time_sequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
