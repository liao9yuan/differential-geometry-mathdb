import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenChartTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniformOrdinaryMetricJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

private local instance localExtensionC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localExtensionC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localExtensionC1 target :: scope.openDecls } }
private local instance localExtensionC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localExtensionC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localExtensionC2 target :: scope.openDecls } }

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
private theorem ambient_time_jet_eq_in_restricted_chart
    (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
    {D : RealTimeInterval} (T : SolutionOn (I := I) (M := V) D) (hT : IsSolutionOn T)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b) (ht : t ≤ b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ s, T.base.metric s = (g s).restrictOpen (I := I) V)
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ s, B 0 s = metricTensorField (g s))
    (hB : ∀ q s, s ≤ b → ∀ x : M,
      HasDerivWithinAt (fun u => B q u x) (B (q + 1) s x) (_root_.Set.Iic b) s)
    (p : V) {y : E} (hy : y ∈ (extChartAt I p).target) (q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    B q t ((extChartAt I (p : M)).symm y)
      (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm y)) =
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (_root_.Set.Iic b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)) := by
  let x : V := (extChartAt I p).symm y
  have hx : (x : M) ∈ (chartAt H (p : M)).source := by
    have hz := (extChartAt I p).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I), TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hz
    exact hz
  have hh := ambient_time_jet_chart_eq_local V T hT hcarrier hregular ht g hmetric B hBzero hB
    p x hx q slots
  have hval := extChartAt_opens_symm_coe V p hy
  have heq := congrArg (fun z : M => B q t z
    (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) z)) hval
  exact heq.symm.trans hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_eq_in_restricted_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_eq_in_restricted_chart target :: scope.openDecls } }


theorem local_extensions_uniform_mixed_coordinate_jets
    (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
    {D : RealTimeInterval} (T : ℕ → SolutionOn (I := I) (M := V) D)
    (hT : ∀ n, IsSolutionOn (T n))
    (L : SolutionOn (I := I) (M := M) D) (hL : IsSolutionOn L)
    {b : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (G : ℕ → ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ n s, (T n).base.metric s = (G n s).restrictOpen (I := I) V)
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField (G n s))
    (hCzero : ∀ s, C 0 s = metricTensorField (L.base.metric s))
    (hB : ∀ n q s, s ≤ b → ∀ x : M,
      HasDerivWithinAt (fun u => B n q u x) (B n (q + 1) s x) (_root_.Set.Iic b) s)
    (hC : ∀ q s, s ≤ b → ∀ x : M,
      HasDerivWithinAt (fun u => C q u x) (C (q + 1) s x) (_root_.Set.Iic b) s)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Iic b) (p : V)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G n t) (p : M) i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (L.base.metric t) (p : M) i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => B n q t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))) y -
        iteratedFDeriv ℝ r (fun z => C q t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))) y‖ ≤ ε := by
  let L₀ := solutionOnRestrictOpen (I := I) L V
  have hL₀ : IsSolutionOn L₀ := isSolutionOn_restrictOpen L hL V
  have hgramEq (g : SmoothRiemannianMetric I M) (m : ℕ)
      (i' j' : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ U) :
      iteratedFDeriv ℝ m (chartGramOnE (I := I) (g.restrictOpen (I := I) V) p i' j') y =
        iteratedFDeriv ℝ m (chartGramOnE (I := I) g (p : M) i' j') y := by
    have hh : chartGramOnE (I := I) (g.restrictOpen (I := I) V) p i' j' =ᶠ[𝓝 y]
        chartGramOnE (I := I) g (p : M) i' j' :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy)
        (fun z hz => chartGramOnE_restrictOpen_on_target g V p (hUt hz) i' j')
    exact (hh.iteratedFDeriv ℝ m).self_of_nhds
  have hlocalGram (i j : Fin (Module.finrank ℝ E)) (Q : Set E) (hQ : IsCompact Q)
      (hQU : Q ⊆ U) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ Q,
        ‖iteratedFDeriv ℝ m (chartGramOnE (I := I) ((T n).base.metric t) p i j) y -
          iteratedFDeriv ℝ m (chartGramOnE (I := I) (L₀.base.metric t) p i j) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := hgram i j Q hQ hQU m ε hε
    refine ⟨N, fun n hn t ht y hy => ?_⟩
    rw [hmetric n t]
    change ‖iteratedFDeriv ℝ m (chartGramOnE (I := I) ((G n t).restrictOpen (I := I) V) p i j) y -
      iteratedFDeriv ℝ m (chartGramOnE (I := I) ((L.base.metric t).restrictOpen (I := I) V) p i j) y‖ ≤ ε
    rw [hgramEq (G n t) m i j (hQU hy), hgramEq (L.base.metric t) m i j (hQU hy)]
    exact hN n hn t ht y hy
  let coords (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (z : E) : ℝ :=
    A ((extChartAt I (p : M)).symm z)
      (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))
  let actual (R : SolutionOn (I := I) (M := V) D) (s : ℝ) (z : E) : ℝ :=
    (iteratedDerivWithin q
      (fun t => metricTensorField (R.base.metric t) ((extChartAt I p).symm z)) (_root_.Set.Iic b) s)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))
  have hjetEq (R : SolutionOn (I := I) (M := V) D) (hR : IsSolutionOn R)
      (g : ℝ → SmoothRiemannianMetric I M)
      (hg : ∀ s, R.base.metric s = (g s).restrictOpen (I := I) V)
      (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
      (hA₀ : ∀ s, A 0 s = metricTensorField (g s))
      (hA : ∀ k s, s ≤ b → ∀ x : M,
        HasDerivWithinAt (fun u => A k u x) (A (k + 1) s x) (_root_.Set.Iic b) s)
      {s : ℝ} (hs : s ≤ b) {y : E} (hy : y ∈ U) :
      iteratedFDeriv ℝ r (coords (A q s)) y = iteratedFDeriv ℝ r (actual R s) y := by
    have hh : coords (A q s) =ᶠ[𝓝 y] actual R s :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz =>
        ambient_time_jet_eq_in_restricted_chart V R hR hcarrier hregular hs g hg A hA₀ hA
          p (hUt hz) q slots)
    exact (hh.iteratedFDeriv ℝ r).self_of_nhds
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_ordinary_metric_jets_on_compact_time T hT L₀ hL₀
    hcarrier hregular hJ hJb p hU hUt hlocalGram hK hKU r q slots ε hε
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  change ‖iteratedFDeriv ℝ r (coords (B n q t)) y - iteratedFDeriv ℝ r (coords (C q t)) y‖ ≤ ε
  rw [hjetEq (T n) (hT n) (G n) (hmetric n) (B n) (hBzero n) (hB n) (hJb ht) (hKU hy),
    hjetEq L₀ hL₀ L.base.metric (fun _ => rfl) C hCzero hC (hJb ht) (hKU hy)]
  exact hN n hn t ht y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
private theorem ambient_time_jet_eq_in_restricted_chart_on_closedWindow
    (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
    {D : RealTimeInterval} (T : SolutionOn (I := I) (M := V) D) (hT : IsSolutionOn T)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ _root_.Set.Icc c b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ s, T.base.metric s = (g s).restrictOpen (I := I) V)
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ s, B 0 s = metricTensorField (g s))
    (hB : ∀ q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun u => B q u x) (B (q + 1) s x) (_root_.Set.Icc c b) s)
    (p : V) {y : E} (hy : y ∈ (extChartAt I p).target) (q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    B q t ((extChartAt I (p : M)).symm y)
      (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm y)) =
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (_root_.Set.Icc c b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)) := by
  let x : V := (extChartAt I p).symm y
  have hx : (x : M) ∈ (chartAt H (p : M)).source := by
    have hz := (extChartAt I p).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I), TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hz
    exact hz
  have hh := ambient_time_jet_chart_eq_local_on_closedWindow V T hT hac hcb hslab hregular ht g hmetric B hBzero hB
    p x hx q slots
  have hval := extChartAt_opens_symm_coe V p hy
  have heq := congrArg (fun z : M => B q t z
    (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) z)) hval
  exact heq.symm.trans hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_eq_in_restricted_chart_on_closedWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_eq_in_restricted_chart_on_closedWindow target :: scope.openDecls } }


theorem local_extensions_uniform_mixed_coordinate_jets_on_closedWindow
    (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
    {D : ℕ → RealTimeInterval} {D₀ : RealTimeInterval}
    (T : (n : ℕ) → SolutionOn (I := I) (M := V) (D n))
    (hT : ∀ n, IsSolutionOn (T n))
    (L : SolutionOn (I := I) (M := M) D₀) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : ∀ n, _root_.Set.Icc a b ⊆ (D n).carrier) (hregular : ∀ n, _root_.Set.Ioo a b ⊆ (D n).regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    (G : ℕ → ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ n s, (T n).base.metric s = (G n s).restrictOpen (I := I) V)
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField (G n s))
    (hCzero : ∀ s, C 0 s = metricTensorField (L.base.metric s))
    (hB : ∀ n q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun u => B n q u x) (B n (q + 1) s x) (_root_.Set.Icc c b) s)
    (hC : ∀ q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun u => C q u x) (C (q + 1) s x) (_root_.Set.Icc c b) s)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b) (p : V)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G n t) (p : M) i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (L.base.metric t) (p : M) i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z => B n q t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))) y -
        iteratedFDeriv ℝ r (fun z => C q t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))) y‖ ≤ ε := by
  let L₀ := solutionOnRestrictOpen (I := I) L V
  have hL₀ : IsSolutionOn L₀ := isSolutionOn_restrictOpen L hL V
  have hgramEq (g : SmoothRiemannianMetric I M) (m : ℕ)
      (i' j' : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ U) :
      iteratedFDeriv ℝ m (chartGramOnE (I := I) (g.restrictOpen (I := I) V) p i' j') y =
        iteratedFDeriv ℝ m (chartGramOnE (I := I) g (p : M) i' j') y := by
    have hh : chartGramOnE (I := I) (g.restrictOpen (I := I) V) p i' j' =ᶠ[𝓝 y]
        chartGramOnE (I := I) g (p : M) i' j' :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy)
        (fun z hz => chartGramOnE_restrictOpen_on_target g V p (hUt hz) i' j')
    exact (hh.iteratedFDeriv ℝ m).self_of_nhds
  have hlocalGram (i j : Fin (Module.finrank ℝ E)) (Q : Set E) (hQ : IsCompact Q)
      (hQU : Q ⊆ U) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ Q,
        ‖iteratedFDeriv ℝ m (chartGramOnE (I := I) ((T n).base.metric t) p i j) y -
          iteratedFDeriv ℝ m (chartGramOnE (I := I) (L₀.base.metric t) p i j) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := hgram i j Q hQ hQU m ε hε
    refine ⟨N, fun n hn t ht y hy => ?_⟩
    rw [hmetric n t]
    change ‖iteratedFDeriv ℝ m (chartGramOnE (I := I) ((G n t).restrictOpen (I := I) V) p i j) y -
      iteratedFDeriv ℝ m (chartGramOnE (I := I) ((L.base.metric t).restrictOpen (I := I) V) p i j) y‖ ≤ ε
    rw [hgramEq (G n t) m i j (hQU hy), hgramEq (L.base.metric t) m i j (hQU hy)]
    exact hN n hn t ht y hy
  let coords (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (z : E) : ℝ :=
    A ((extChartAt I (p : M)).symm z)
      (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) ((extChartAt I (p : M)).symm z))
  let actual {D' : RealTimeInterval} (R : SolutionOn (I := I) (M := V) D') (s : ℝ) (z : E) : ℝ :=
    (iteratedDerivWithin q
      (fun t => metricTensorField (R.base.metric t) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) s)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))
  have hjetEq {D' : RealTimeInterval} (R : SolutionOn (I := I) (M := V) D')
      (hR : IsSolutionOn R) (hcarR : _root_.Set.Icc a b ⊆ D'.carrier) (hregR : _root_.Set.Ioo a b ⊆ D'.regular)
      (g : ℝ → SmoothRiemannianMetric I M)
      (hg : ∀ s, R.base.metric s = (g s).restrictOpen (I := I) V)
      (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
      (hA₀ : ∀ s, A 0 s = metricTensorField (g s))
      (hA : ∀ k s, s ∈ _root_.Set.Icc c b → ∀ x : M,
        HasDerivWithinAt (fun u => A k u x) (A (k + 1) s x) (_root_.Set.Icc c b) s)
      {s : ℝ} (hs : s ∈ _root_.Set.Icc c b) {y : E} (hy : y ∈ U) :
      iteratedFDeriv ℝ r (coords (A q s)) y = iteratedFDeriv ℝ r (actual R s) y := by
    have hh : coords (A q s) =ᶠ[𝓝 y] actual R s :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz =>
        ambient_time_jet_eq_in_restricted_chart_on_closedWindow V R hR hac hcb hcarR hregR hs g hg A hA₀ hA
          p (hUt hz) q slots)
    exact (hh.iteratedFDeriv ℝ r).self_of_nhds
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_metric_time_jets_on_compact_closedWindow T hT L₀ hL₀
    hac hcb hslab hregular hslab₀ hregular₀ hJ hJb p hU hUt hlocalGram hK hKU r q slots ε hε
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  change ‖iteratedFDeriv ℝ r (coords (B n q t)) y - iteratedFDeriv ℝ r (coords (C q t)) y‖ ≤ ε
  rw [hjetEq (T n) (hT n) (hslab n) (hregular n) (G n) (hmetric n) (B n) (hBzero n) (hB n) (hJb ht) (hKU hy),
    hjetEq L₀ hL₀ hslab₀ hregular₀ L.base.metric (fun _ => rfl) C hCzero hC (hJb ht) (hKU hy)]
  exact hN n hn t ht y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets_on_closedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets_on_closedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets_on_closedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.local_extensions_uniform_mixed_coordinate_jets_on_closedWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
