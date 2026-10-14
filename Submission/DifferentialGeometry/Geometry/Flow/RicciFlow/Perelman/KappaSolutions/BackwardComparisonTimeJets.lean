import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ComparisonTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardNeck
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance backwardComparisonC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonC1 target :: scope.openDecls } }

private local instance backwardComparisonSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonSphereDimension target :: scope.openDecls } }

private local instance backwardComparisonBufferSigma (epsilon : ℝ) :
    SigmaCompactSpace (spatialNeckBuffer epsilon) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel (spatialNeckBuffer epsilon).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonBufferSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardComparisonBufferSigma target :: scope.openDecls } }

private theorem ancientMetricTensor_contDiffOn
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) (x : F.M) :
    ContDiffOn ℝ ∞ (fun t => metricTensorField (F.S.base.metric t) x) (_root_.Set.Icc a b) := by
  classical
  have hslab : _root_.Set.Icc (a - 1) b ⊆ ancientTimeInterval.carrier := fun _ ht => ht.2.trans hb
  have hreg : _root_.Set.Ioo (a - 1) b ⊆ ancientTimeInterval.regular := fun _ ht => ht.2.trans_le hb
  obtain ⟨V, _hV, hxV, _hVt, hgram⟩ :=
    solution_chartGram_contDiffOn_closed F.S F.isSolution (a := a - 1) (c := a) (b := b)
      (by linarith) hab hslab hreg x
  have hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace I3) x).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace I3) x
  let basis := DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I3) x hx
  have hc (slots : Fin 2 → Fin (Module.finrank ℝ ThreeSpace)) :
      ContDiffOn ℝ ∞
        (fun t => component0S (I := I3) basis (metricTensorField (F.S.base.metric t) x) slots)
        (_root_.Set.Icc a b) := by
    have hm := (hgram (slots 0) (slots 1)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hxV⟩)
    apply hm.congr
    intro t _ht
    change (F.S.base.metric t).inner x (basis (slots 0)) (basis (slots 1)) =
      chartGramOnE (I := I3) (F.S.base.metric t) x (slots 0) (slots 1) (extChartAt I3 x x)
    dsimp only [basis]
    rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply,
      DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
    simp only [chartGramOnE, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      (extChartAt I3 x).left_inv (mem_extChartAt_source x)]
  have hsum : ContDiffOn ℝ ∞
      (fun t => ∑ slots, component0S (I := I3) basis (metricTensorField (F.S.base.metric t) x) slots •
        tensor0SBasis (I := I3) basis 2 slots) (_root_.Set.Icc a b) :=
    ContDiffOn.sum fun slots _ => (hc slots).smul_const _
  simpa only [← tensor0SBasis_repr, Module.Basis.sum_repr] using hsum

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMetricTensor_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientMetricTensor_contDiffOn target :: scope.openDecls } }


theorem backwardMetricComparison_hasDerivWithinAt
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℝ) (htau : 0 < tau) (epsilon : ℝ)
    {f : spatialNeckBuffer epsilon → F.M} {order : ℕ} {eta : ℝ}
    (C : MetricComparisonOn
      (fun theta => strongNeckBackgroundMetric epsilon (1 - theta))
      (backwardScaledMetric F.S tau htau) f _root_.Set.univ (_root_.Set.Icc (1 : ℝ) 3) order eta)
    (q : ℕ) (theta : ℝ) (htheta : theta ∈ _root_.Set.Icc (1 : ℝ) 3)
    (x : spatialNeckBuffer epsilon) (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun r => C.jet q r x v) (C.jet (q + 1) theta x v)
      (_root_.Set.Icc (1 : ℝ) 3) theta := by
  let w : Fin 2 → TangentSpace I3 (f x) :=
    fun j => mfderiv SpatialNeckCylinderModel I3 f x (v j)
  have hsource0 : ContDiffOn ℝ ∞
      (fun t => (F.S.base.metric t).inner (f x) (w 0) (w 1)) (_root_.Set.Icc (-3 * tau) (-tau)) := by
    have hh := (tensor0SEvalCLM (I := I3) (x := f x) w).contDiff.comp_contDiffOn
      (ancientMetricTensor_contDiffOn F (by linarith : -3 * tau < -tau)
        (neg_nonpos.mpr htau.le) (f x))
    change ContDiffOn ℝ ∞ (fun t => metricTensorField (F.S.base.metric t) (f x) w)
      (_root_.Set.Icc (-3 * tau) (-tau)) at hh
    simpa only [metricTensorField_apply] using hh
  have hmap : _root_.Set.MapsTo (fun t : ℝ => -tau * t) (_root_.Set.Icc (1 : ℝ) 3) (_root_.Set.Icc (-3 * tau) (-tau)) := by
    intro t ht
    have hlo := mul_le_mul_of_nonneg_left ht.2 htau.le
    have hhi := mul_le_mul_of_nonneg_left ht.1 htau.le
    constructor <;> nlinarith
  have hsource : ContDiffOn ℝ ∞
      (fun t => (backwardScaledMetric F.S tau htau t).inner (f x) (w 0) (w 1))
      (_root_.Set.Icc (1 : ℝ) 3) := by
    simp only [backwardScaledMetric, scaleMetric_inner]
    exact contDiffOn_const.mul (hsource0.comp (contDiffOn_const.mul contDiffOn_id) hmap)
  let horizontal := (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
    (x : SpatialNeckCylinder).1 (v 0).1 (v 1).1
  let axial := (v 0).2 * (v 1).2
  have hlimit : ContDiffOn ℝ ∞
      (fun t => (strongNeckBackgroundMetric epsilon (1 - t)).inner x (v 0) (v 1))
      (_root_.Set.Icc (1 : ℝ) 3) := by
    have hlinear : ContDiffOn ℝ ∞ (fun t : ℝ => 2 * t * horizontal + axial) (_root_.Set.Icc (1 : ℝ) 3) :=
      ((contDiffOn_const.mul contDiffOn_id).mul contDiffOn_const).add contDiffOn_const
    apply hlinear.congr
    intro t ht
    rw [strongNeckBackgroundMetric_of_nonpos epsilon (1 - t) (sub_nonpos.mpr ht.1),
      SmoothRiemannianMetric.restrictOpen_inner]
    erw [scalarOneShrinkingCylinderMetric_inner]
    dsimp only [horizontal, axial]
    ring
  let g (b : ℕ) (t : ℝ) := iteratedDerivWithin b
    (fun r => (backwardScaledMetric F.S tau htau r).inner (f x) (w 0) (w 1) -
      (strongNeckBackgroundMetric epsilon (1 - r)).inner x (v 0) (v 1)) (_root_.Set.Icc (1 : ℝ) 3) t
  have htimes : UniqueDiffOn ℝ (_root_.Set.Icc (1 : ℝ) 3) := uniqueDiffOn_Icc (by norm_num)
  have hg (b : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc (1 : ℝ) 3) :
      HasDerivWithinAt (g b) (g (b + 1) t) (_root_.Set.Icc (1 : ℝ) 3) t := by
    have hb : (b : WithTop ℕ∞) < ∞ :=
      WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top b)
    have hd := ((hsource.sub hlimit).differentiableOn_iteratedDerivWithin hb htimes t ht).hasDerivWithinAt
    rw [← iteratedDerivWithin_succ] at hd
    exact hd
  have hzero (t : ℝ) (_ht : t ∈ _root_.Set.Icc (1 : ℝ) 3) : C.jet 0 t x v = g 0 t := by
    rw [C.jet_zero, C.pullback_eq t x (_root_.Set.mem_univ x)]
    simp only [g, iteratedDerivWithin_zero, w]
  have heq := derivWithin_tower_eq_of_genuine htimes
    (fun b t => C.jet b t x v) g (fun b t ht => C.jet_succ b t ht x (_root_.Set.mem_univ x) v) hg hzero
  have hd := (hg q theta htheta).congr_deriv (heq (q + 1) theta htheta).symm
  exact hd.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun t ht => heq q t ht))
    (heq q theta htheta)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparison_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparison_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparison_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardMetricComparison_hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
