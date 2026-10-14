import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators


theorem derivWithin_tower_eq_of_genuine {times : Set ℝ} (htimes : UniqueDiffOn ℝ times)
    (f g : ℕ → ℝ → ℝ)
    (hf : ∀ q t, t ∈ times → f (q + 1) t = derivWithin (f q) times t)
    (hg : ∀ q t, t ∈ times → HasDerivWithinAt (g q) (g (q + 1) t) times t)
    (hzero : ∀ t ∈ times, f 0 t = g 0 t) :
    ∀ q t, t ∈ times → f q t = g q t := by
  exact DifferentialGeometry.Analysis.derivWithin_tower_eq f g hf
    (fun q t ht => ((hg q t ht).derivWithin (htimes t ht)).symm) hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.derivWithin_tower_eq_of_genuine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.derivWithin_tower_eq_of_genuine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.derivWithin_tower_eq_of_genuine ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.derivWithin_tower_eq_of_genuine


universe u v uE uH

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless]
  {N : Type v} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance comparisonTimeSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonTimeSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonTimeSourceC1 target :: scope.openDecls } }
private local instance comparisonTimeLimitC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonTimeLimitC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonTimeLimitC1 target :: scope.openDecls } }

private theorem comparisonMetric_time_contDiff
    {D : RealTimeInterval}
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T)
    (hcarrier : D.carrier = _root_.Set.Iic (0 : ℝ)) (hregular : D.regular = _root_.Set.Iio (0 : ℝ))
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) (x : N) :
    ContDiffOn ℝ ∞ (fun t => metricTensorField (T.base.metric t) x) (_root_.Set.Icc a b) := by
  classical
  have hslab : _root_.Set.Icc (a - 1) b ⊆ D.carrier := by
    rw [hcarrier]
    exact fun _ ht => ht.2.trans hb
  have hreg : _root_.Set.Ioo (a - 1) b ⊆ D.regular := by
    rw [hregular]
    exact fun _ ht => ht.2.trans_le hb
  obtain ⟨V, _hV, hxV, _hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed T hT (a := a - 1) (c := a) (b := b)
      (by linarith) hab hslab hreg x
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace J) x).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace J) x
  let basis := chartBasisFamily (I := J) x hx
  have hc (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => component0S (I := J) basis (metricTensorField (T.base.metric t) x) slots)
        (_root_.Set.Icc a b) := by
    have hm := (hgram (slots 0) (slots 1)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hxV⟩)
    apply hm.congr
    intro t _ht
    change (T.base.metric t).inner x (basis (slots 0)) (basis (slots 1)) =
      chartGramOnE (I := J) (T.base.metric t) x (slots 0) (slots 1) (extChartAt J x x)
    dsimp only [basis]
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    simp only [chartGramOnE, chartGramMatrix_apply,
      (extChartAt J x).left_inv (mem_extChartAt_source x)]
  have hsum : ContDiffOn ℝ ∞
      (fun t => ∑ slots, component0S (I := J) basis (metricTensorField (T.base.metric t) x) slots •
        tensor0SBasis (I := J) basis 2 slots) (_root_.Set.Icc a b) :=
    ContDiffOn.sum fun slots _ => (hc slots).smul_const _
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonMetric_time_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.comparisonMetric_time_contDiff target :: scope.openDecls } }


theorem metricComparison_hasDerivWithinAt
    {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T)
    (hcarrier : D.carrier = _root_.Set.Iic (0 : ℝ)) (hregular : D.regular = _root_.Set.Iio (0 : ℝ))
    {f : N → M} {K : Set N} {a b epsilon : ℝ} {order : ℕ}
    (C : MetricComparisonOn T.base.metric S.base.metric f K (_root_.Set.Icc a b) order epsilon)
    (hab : a < b) (hb : b ≤ 0)
    (q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : N) (hx : x ∈ K)
    (v : Fin 2 → TangentSpace J x) :
    HasDerivWithinAt (fun s => C.jet q s x v) (C.jet (q + 1) t x v) (_root_.Set.Icc a b) t := by
  let w : Fin 2 → TangentSpace I3 (f x) := fun j => mfderiv J I3 f x (v j)
  have hsource : ContDiffOn ℝ ∞
      (fun s => (S.base.metric s).inner (f x) (w 0) (w 1)) (_root_.Set.Icc a b) := by
    have hh := (tensor0SEvalCLM (I := I3) (x := f x) w).contDiff.comp_contDiffOn
      (comparisonMetric_time_contDiff S hS hcarrier hregular hab hb (f x))
    change ContDiffOn ℝ ∞ (fun s => metricTensorField (S.base.metric s) (f x) w)
      (_root_.Set.Icc a b) at hh
    simpa only [metricTensorField_apply] using hh
  have hlimit : ContDiffOn ℝ ∞
      (fun s => (T.base.metric s).inner x (v 0) (v 1)) (_root_.Set.Icc a b) := by
    have hh := (tensor0SEvalCLM (I := J) (x := x) v).contDiff.comp_contDiffOn
      (comparisonMetric_time_contDiff T hT hcarrier hregular hab hb x)
    change ContDiffOn ℝ ∞ (fun s => metricTensorField (T.base.metric s) x v)
      (_root_.Set.Icc a b) at hh
    simpa only [metricTensorField_apply] using hh
  let g (r : ℕ) (s : ℝ) : ℝ := iteratedDerivWithin r
    (fun u => (S.base.metric u).inner (f x) (w 0) (w 1) -
      (T.base.metric u).inner x (v 0) (v 1)) (_root_.Set.Icc a b) s
  have hg (r : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) :
      HasDerivWithinAt (g r) (g (r + 1) s) (_root_.Set.Icc a b) s := by
    have hr : (r : WithTop ℕ∞) < ∞ :=
      WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top r)
    have hd := ((hsource.sub hlimit).differentiableOn_iteratedDerivWithin
      hr (uniqueDiffOn_Icc hab) s hs).hasDerivWithinAt
    rw [← iteratedDerivWithin_succ] at hd
    exact hd
  have hzero (s : ℝ) (_hs : s ∈ _root_.Set.Icc a b) : C.jet 0 s x v = g 0 s := by
    rw [C.jet_zero, C.pullback_eq s x hx]
    simp only [g, iteratedDerivWithin_zero, w]
  have heq := derivWithin_tower_eq_of_genuine (uniqueDiffOn_Icc hab)
    (fun r s => C.jet r s x v) g (fun r s hs => C.jet_succ r s hs x hx v) hg hzero
  have hd := (hg q t ht).congr_deriv (heq (q + 1) t ht).symm
  exact hd.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun s hs => heq q s hs)) (heq q t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComparison_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComparison_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComparison_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComparison_hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
