import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLocalGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance collapsedBallTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallTopology
local instance collapsedBallCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallCharted
local instance collapsedBallSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSmooth
local instance collapsedBallC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallC1
local instance collapsedBallT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallT2
local instance collapsedBallSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.collapsedBallSigma
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem curvature_controlled_point_scalar_le
    (hdim : Module.finrank ℝ E = 3) {r : ℝ} (hr : 0 < r) (x : F.M)
    (hcontrol : r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) : F.S.scalar 0 x ≤ 9 / r ^ 2 := by
  have hq := pointedFlow_rmNormSq_nonneg F 0 x
  have hsqrt := Real.sqrt_nonneg (F.rmNormSq (I := I) 0 x)
  have hsquare := Real.sq_sqrt hq
  have hproductSquare : (r ^ 2 * Real.sqrt (F.rmNormSq (I := I) 0 x)) ^ 2 ≤ 1 := by
    calc
      (r ^ 2 * Real.sqrt (F.rmNormSq (I := I) 0 x)) ^ 2 =
          r ^ 4 * F.rmNormSq (I := I) 0 x := by rw [mul_pow, hsquare]; ring
      _ ≤ 1 := hcontrol
  have hproduct : r ^ 2 * Real.sqrt (F.rmNormSq (I := I) 0 x) ≤ 1 :=
    (sq_le_sq₀ (mul_nonneg (sq_nonneg r) hsqrt) zero_le_one).mp (by simpa using hproductSquare)
  have hscalar := scalar_abs_le_rm (F.S.base.metric 0) x
  change |F.S.scalar 0 x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
    Real.sqrt (F.rmNormSq (I := I) 0 x) at hscalar
  rw [hdim] at hscalar
  norm_num at hscalar
  have hscalarUpper : F.S.scalar 0 x ≤ 9 * Real.sqrt (F.rmNormSq (I := I) 0 x) :=
    (le_abs_self (F.S.scalar 0 x)).trans hscalar
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hscalarUpper (sq_nonneg r)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvature_controlled_point_scalar_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.curvature_controlled_point_scalar_le target :: scope.openDecls } }


theorem ancientKappaThree_controlledBall_scalar_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p : F.M) {r : ℝ} (hr : 0 < r)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1)
    {t : ℝ} (ht : t ≤ 0) {x : F.M} (hx : x ∈ riemannianBallOf (F.S.base.metric 0) p r) :
    0 ≤ F.S.scalar t x ∧ F.S.scalar t x ≤ 9 / r ^ 2 := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨(hC t ht x).1, ?_⟩
  exact ((ancientKappaThree_toKLim F hF hdim).scalar_le_terminal ht x).trans
    (curvature_controlled_point_scalar_le F hdim hr x (hcontrol x hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_scalar_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_scalar_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_scalar_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_scalar_bound


theorem ancientKappaThree_controlledBall_backward_volume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p : F.M) {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) :
    riemannianBallOf (F.S.base.metric (-(theta * r ^ 2))) p r ⊆
        riemannianBallOf (F.S.base.metric 0) p r ∧
    riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-(theta * r ^ 2)))
        (riemannianBallOf (F.S.base.metric (-(theta * r ^ 2))) p r) ≤
      ENNReal.ofReal (Real.exp ((27 / 2 : ℝ) * theta)) *
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
          (riemannianBallOf (F.S.base.metric 0) p r) := by
  have hK := ancientKappaThree_toKLim F hF hdim
  have htime : -(theta * r ^ 2) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hballs : riemannianBallOf (F.S.base.metric (-(theta * r ^ 2))) p r ⊆
      riemannianBallOf (F.S.base.metric 0) p r := by
    intro x hx
    exact (hK.edist_le htime le_rfl p x).trans_lt hx
  refine ⟨hballs, ?_⟩
  have hQ : Real.sqrt (Real.exp (9 * theta) ^ Module.finrank ℝ E) =
      Real.exp ((27 / 2 : ℝ) * theta) := by
    rw [hdim]
    have hsq : Real.exp ((27 / 2 : ℝ) * theta) ^ 2 = Real.exp (9 * theta) ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]
  have hopen : MeasurableSet (riemannianBallOf (F.S.base.metric 0) p r) :=
    (isOpen_lt (continuous_riemannianEDist (F.S.base.metric 0) p) continuous_const).measurableSet
  have hmetric : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      ∀ v : TangentSpace I x,
        (F.S.base.metric (-(theta * r ^ 2))).inner x v v ≤
          Real.exp (9 * theta) * (F.S.base.metric 0).inner x v v := by
    intro x hx v
    have h := hK.metric_inner_le_exp_terminal_bound htime x
      (curvature_controlled_point_scalar_le F hdim hr x (hcontrol x hx)) v
    have heq : (9 / r ^ 2) * (-(-(theta * r ^ 2))) = 9 * theta := by
      field_simp [hr.ne']
    simpa only [heq] using h
  have hvolume := riemannianVolumeMeasure_le_on (F.S.base.metric 0)
    (F.S.base.metric (-(theta * r ^ 2))) hopen (Real.exp_pos (9 * theta)) hmetric
  rw [hQ] at hvolume
  exact (_root_.MeasureTheory.measure_mono hballs).trans hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_backward_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_backward_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_backward_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_backward_volume


theorem ancientKappaThree_controlledBall_pole_reducedCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p : F.M) {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1) :
    lCost F.S 0 p p (theta * r ^ 2) / (2 * Real.sqrt (theta * r ^ 2)) ≤ 3 * theta := by
  have htau : 0 < theta * r ^ 2 := by positivity
  have hp : p ∈ riemannianBallOf (F.S.base.metric 0) p r := by
    change riemannianEDistOf (F.S.base.metric 0) p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hscalar : ∀ s ∈ _root_.Set.Icc 0 (theta * r ^ 2), ∀ x : F.M, 0 ≤ F.S.scalar (0 - s) x := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs x
    exact (hC (0 - s) (by change 0 - s ≤ 0; linarith [hs.1]) x).1
  have hbound : ∀ s ∈ _root_.Set.Icc 0 (theta * r ^ 2), F.S.scalar (0 - s) p ≤ 9 / r ^ 2 := by
    intro s hs
    exact (ancientKappaThree_controlledBall_scalar_bound F hF hdim p hr hcontrol
      (by linarith [hs.1]) hp).2
  have hcontinuous : ContinuousOn (fun s : ℝ => F.S.scalar (0 - s) p) (_root_.Set.Icc 0 (theta * r ^ 2)) := by
    have hmaps : _root_.Set.MapsTo (fun s : ℝ => (0 - s, p)) (_root_.Set.Icc 0 (theta * r ^ 2))
        (ancientTimeInterval.carrier ×ˢ _root_.Set.univ) := by
      intro s hs
      exact ⟨by change 0 - s ≤ 0; linarith [hs.1], _root_.Set.mem_univ p⟩
    have h := F.isSolution.scalarCont.comp
      (((continuous_const.sub continuous_id).prodMk continuous_const).continuousOn)
      hmaps
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using h
  have h := reducedCost_at_pole_le F.S 0 htau hscalar p hbound hcontinuous
  convert h using 1
  field_simp [hr.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_pole_reducedCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_pole_reducedCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_pole_reducedCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_controlledBall_pole_reducedCost

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
