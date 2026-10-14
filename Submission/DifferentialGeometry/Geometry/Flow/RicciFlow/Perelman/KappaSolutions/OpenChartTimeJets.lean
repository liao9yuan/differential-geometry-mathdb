import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import Submission.DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricTimeJets
import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields

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
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


theorem scalar_time_towers_eq {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (f g : ℕ → ℝ → ℝ)
    (hf : ∀ q t, t ∈ J → HasDerivWithinAt (f q) (f (q + 1) t) J t)
    (hg : ∀ q t, t ∈ J → HasDerivWithinAt (g q) (g (q + 1) t) J t)
    (hzero : ∀ t ∈ J, f 0 t = g 0 t) : ∀ q t, t ∈ J → f q t = g q t := by
  exact DifferentialGeometry.Analysis.derivWithin_tower_eq f g
    (fun q t ht => ((hf q t ht).derivWithin (hJ t ht)).symm)
    (fun q t ht => ((hg q t ht).derivWithin (hJ t ht)).symm) hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_time_towers_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_time_towers_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_time_towers_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_time_towers_eq


section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem chartBasisVecFiber_restrictOpen (U : TopologicalSpace.Opens M) (p x : U)
    (hx : (x : M) ∈ (chartAt H (p : M)).source) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) p i x = chartBasisVecFiber (I := I) (p : M) i (x : M) := by
  let : Nonempty U := ⟨p⟩
  have hxU : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := U)) p).symmL ℝ x (chartModelBasis E i) =
    (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := M)) (p : M)).symmL ℝ (x : M) (chartModelBasis E i)
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hxU,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hx,
    tangentCoordChange_opens (I := I) p x x hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartBasisVecFiber_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartBasisVecFiber_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartBasisVecFiber_restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartBasisVecFiber_restrictOpen

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extChartAt_opens_symm_coe (U : TopologicalSpace.Opens M) (p : U) {y : E}
    (hy : y ∈ (extChartAt I p).target) :
    (((extChartAt I p).symm y : U) : M) = (extChartAt I (p : M)).symm y := by
  let : Nonempty U := ⟨p⟩
  have hyTarget : I.symm y ∈ (chartAt H p).target := by
    have hy' : (∃ z, I z = y) ∧ I.symm y ∈ (chartAt H p).target := by
      simpa [extChartAt] using hy
    exact hy'.2
  change ((chartAt H p).symm (I.symm y) : U) = (chartAt H (p : M)).symm (I.symm y)
  rw [TopologicalSpace.Opens.chartAt_eq] at hyTarget ⊢
  exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hyTarget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_symm_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_symm_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_symm_coe ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_symm_coe

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extChartAt_opens_target_subset (U : TopologicalSpace.Opens M) (p : U) :
    (extChartAt I p).target ⊆ (extChartAt I (p : M)).target := by
  intro y hy
  have hz := (extChartAt I p).map_target hy
  have hzM : (((extChartAt I p).symm y : U) : M) ∈ (extChartAt I (p : M)).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hz ⊢
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source] at hz
    exact hz
  have hxy : extChartAt I (p : M) (((extChartAt I p).symm y : U) : M) = y :=
    (extChartAt I p).right_inv hy
  rw [← hxy]
  exact (extChartAt I (p : M)).map_source hzM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_target_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_target_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_target_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.extChartAt_opens_target_subset


theorem chartGramOnE_restrictOpen_on_target (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [T2Space U] (p : U) {y : E}
    (hy : y ∈ (extChartAt I p).target) (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) (g.restrictOpen (I := I) U) p i j y =
      chartGramOnE (I := I) g (p : M) i j y := by
  have hz := (extChartAt I p).map_target hy
  have hzM : (((extChartAt I p).symm y : U) : M) ∈ (chartAt H (p : M)).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I), TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hz
    exact hz
  have hh := chartGram_open (I := I) g U p ((extChartAt I p).symm y) hzM i j
  rw [extChartAt_opens_symm_coe U p hy] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramOnE_restrictOpen_on_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramOnE_restrictOpen_on_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramOnE_restrictOpen_on_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartGramOnE_restrictOpen_on_target

end Charts

section Time

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance openTimeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTimeC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openTimeC1 target :: scope.openDecls } }


theorem ambient_time_jet_chart_eq_local
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (T : SolutionOn (I := I) (M := U) D) (hT : IsSolutionOn T)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b) (ht : t ≤ b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ s, T.base.metric s = (g s).restrictOpen (I := I) U)
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ s, B 0 s = metricTensorField (g s))
    (hB : ∀ q s, s ≤ b → ∀ x : M,
      HasDerivWithinAt (fun u => B q u x) (B (q + 1) s x) (_root_.Set.Iic b) s)
    (p x : U) (hx : (x : M) ∈ (chartAt H (p : M)).source) (q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    B q t (x : M) (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) (x : M)) =
      (iteratedDerivWithin q (fun s => metricTensorField (T.base.metric s) x) (_root_.Set.Iic b) t)
        (fun j => chartBasisVecFiber (I := I) p (slots j) x) := by
  obtain ⟨C, hCzero, hC⟩ := exists_ancient_ordinary_metric_time_jets T hT hcarrier hregular
  let vM : Fin 2 → TangentSpace I (x : M) :=
    fun j => chartBasisVecFiber (I := I) (p : M) (slots j) (x : M)
  let vU : Fin 2 → TangentSpace I x := fun j => chartBasisVecFiber (I := I) p (slots j) x
  let f (q : ℕ) (s : ℝ) := B q s (x : M) vM
  let h (q : ℕ) (s : ℝ) := C q s x vU
  have hf (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Iic b) :
      HasDerivWithinAt (f q) (f (q + 1) s) (_root_.Set.Iic b) s :=
    (tensor0SEvalCLM (I := I) (x := (x : M)) vM).hasFDerivAt.comp_hasDerivWithinAt s
      (hB q s hs (x : M))
  have hh (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Iic b) :
      HasDerivWithinAt (h q) (h (q + 1) s) (_root_.Set.Iic b) s :=
    (tensor0SEvalCLM (I := I) (x := x) vU).hasFDerivAt.comp_hasDerivWithinAt s
      (hC q s hs x).2
  have hzero (s : ℝ) (_hs : s ∈ _root_.Set.Iic b) : f 0 s = h 0 s := by
    change B 0 s (x : M) vM = C 0 s x vU
    calc
      _ = (g s).inner (x : M) (vM 0) (vM 1) := by rw [hBzero, metricTensorField_apply]
      _ = (T.base.metric s).inner x (vU 0) (vU 1) := by
        rw [hmetric, SmoothRiemannianMetric.restrictOpen_inner]
        dsimp only [vM, vU]
        rw [chartBasisVecFiber_restrictOpen U p x hx, chartBasisVecFiber_restrictOpen U p x hx]
      _ = C 0 s x vU := by rw [hCzero, metricTensorField_apply]
  have heq := scalar_time_towers_eq (uniqueDiffOn_Iic b) f h hf hh hzero q t ht
  change B q t (x : M) vM = C q t x vU at heq
  rw [(hC q t ht x).1] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local

theorem ambient_time_jet_chart_eq_local_on_closedWindow
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (T : SolutionOn (I := I) (M := U) D) (hT : IsSolutionOn T)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ _root_.Set.Icc c b)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hmetric : ∀ s, T.base.metric s = (g s).restrictOpen (I := I) U)
    (B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ s, B 0 s = metricTensorField (g s))
    (hB : ∀ q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun u => B q u x) (B (q + 1) s x) (_root_.Set.Icc c b) s)
    (p x : U) (hx : (x : M) ∈ (chartAt H (p : M)).source) (q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    B q t (x : M) (fun j => chartBasisVecFiber (I := I) (p : M) (slots j) (x : M)) =
      (iteratedDerivWithin q (fun s => metricTensorField (T.base.metric s) x) (_root_.Set.Icc c b) t)
        (fun j => chartBasisVecFiber (I := I) p (slots j) x) := by
  obtain ⟨C, hCzero, hC⟩ := CanonicalNeighborhood.FiniteHorn.exists_closedWindow_metric_time_fields T hT hac hcb hslab hregular
  let vM : Fin 2 → TangentSpace I (x : M) :=
    fun j => chartBasisVecFiber (I := I) (p : M) (slots j) (x : M)
  let vU : Fin 2 → TangentSpace I x := fun j => chartBasisVecFiber (I := I) p (slots j) x
  let f (q : ℕ) (s : ℝ) := B q s (x : M) vM
  let h (q : ℕ) (s : ℝ) := C q s x vU
  have hf (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc c b) :
      HasDerivWithinAt (f q) (f (q + 1) s) (_root_.Set.Icc c b) s :=
    (tensor0SEvalCLM (I := I) (x := (x : M)) vM).hasFDerivAt.comp_hasDerivWithinAt s
      (hB q s hs (x : M))
  have hh (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc c b) :
      HasDerivWithinAt (h q) (h (q + 1) s) (_root_.Set.Icc c b) s :=
    (tensor0SEvalCLM (I := I) (x := x) vU).hasFDerivAt.comp_hasDerivWithinAt s
      (hC q s hs x).2
  have hzero (s : ℝ) (_hs : s ∈ _root_.Set.Icc c b) : f 0 s = h 0 s := by
    change B 0 s (x : M) vM = C 0 s x vU
    calc
      _ = (g s).inner (x : M) (vM 0) (vM 1) := by rw [hBzero, metricTensorField_apply]
      _ = (T.base.metric s).inner x (vU 0) (vU 1) := by
        rw [hmetric, SmoothRiemannianMetric.restrictOpen_inner]
        dsimp only [vM, vU]
        rw [chartBasisVecFiber_restrictOpen U p x hx, chartBasisVecFiber_restrictOpen U p x hx]
      _ = C 0 s x vU := by rw [hCzero, metricTensorField_apply]
  have heq := scalar_time_towers_eq (uniqueDiffOn_Icc hcb) f h hf hh hzero q t ht
  change B q t (x : M) vM = C q t x vU at heq
  rw [(hC q t ht x).1] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local_on_closedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local_on_closedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local_on_closedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ambient_time_jet_chart_eq_local_on_closedWindow

end Time
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
