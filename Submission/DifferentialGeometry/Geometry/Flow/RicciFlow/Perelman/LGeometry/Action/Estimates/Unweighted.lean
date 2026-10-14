import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityComposition
import Mathlib.MeasureTheory.Function.Jacobian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lintegral_sub_sq_time
    (f : ℝ → ℝ≥0∞) (T a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) :
    (∫⁻ t in _root_.Set.Ioo (T - c ^ 2) (T - a ^ 2), f t) =
      ∫⁻ r in _root_.Set.Ioo a c, ENNReal.ofReal (2 * r) * f (T - r ^ 2) := by
  let F := fun r : ℝ => T - r ^ 2
  have himage : F '' _root_.Set.Ioo a c = _root_.Set.Ioo (T - c ^ 2) (T - a ^ 2) := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      dsimp only [F]
      have hr0 : 0 ≤ r := ha.trans hr.1.le
      constructor <;> nlinarith [hr.1, hr.2, sq_nonneg (r - a), sq_nonneg (c - r)]
    · intro ht
      have hrad : 0 ≤ T - t := by nlinarith [sq_nonneg a, ht.2]
      have hs := Real.sq_sqrt hrad
      have hs0 := Real.sqrt_nonneg (T - t)
      refine ⟨Real.sqrt (T - t), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [ht.2]
      · nlinarith [ht.1, ha.trans hac]
      · dsimp only [F]
        linarith
  have hF (r : ℝ) : HasFDerivAt F ((-2 * r) • ContinuousLinearMap.id ℝ ℝ) r := by
    have h : HasDerivAt F (-2 * r) r := by
      convert (hasDerivAt_pow 2 r).const_sub T using 1 <;> first | rfl | ring
    convert h.hasFDerivAt using 1
    all_goals first | rfl | (ext; simp [smul_eq_mul])
  have hinj : _root_.Set.InjOn F (_root_.Set.Ioo a c) := by
    intro r hr u hu heq
    dsimp only [F] at heq
    have hr0 : 0 ≤ r := ha.trans hr.1.le
    have hu0 : 0 ≤ u := ha.trans hu.1.le
    nlinarith
  have hh := _root_.MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := _root_.MeasureTheory.MeasureSpace.volume) measurableSet_Ioo (fun r _ => (hF r).hasFDerivWithinAt) hinj f
  rw [himage] at hh
  refine hh.trans (_root_.MeasureTheory.lintegral_congr_ae ?_)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : 0 ≤ r := ha.trans hr.1.le
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_smul, Module.finrank_self,
    pow_one, LinearMap.det_id, mul_one, F]
  rw [abs_of_nonpos (by nlinarith : -2 * r ≤ 0)]
  congr 2
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_sub_sq_time
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_sub_sq_time target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lRegularizedLagrangian_eq_physical_density
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (alpha : ℝ → M)
    {r : ℝ} (hr : 0 < r) :
    lRegularizedLagrangian S T alpha r = 2 * r ^ 2 *
      (S.scalar (T - r ^ 2) (alpha r) +
        (S.base.metric (T - r ^ 2)).inner (alpha r)
          (lVelocity (I := I) (fun t => alpha (Real.sqrt (T - t))) (T - r ^ 2))
          (lVelocity (I := I) (fun t => alpha (Real.sqrt (T - t))) (T - r ^ 2))) := by
  have hvel := lVelocity_comp_affine_time (I := I)
    (squareRootReparametrization alpha) T (-1) (T - r ^ 2) (by norm_num)
  have hfun : (fun t : ℝ => squareRootReparametrization alpha (T + t / (-1))) =
      (fun t => alpha (Real.sqrt (T - t))) := by
    funext t
    simp [squareRootReparametrization, div_eq_mul_inv, sub_eq_add_neg]
  have hclock : T + (T - r ^ 2) / (-1) = r ^ 2 := by ring
  rw [hfun, hclock] at hvel
  norm_num only [inv_neg, inv_one, neg_smul, one_smul] at hvel
  have hsq := lVelocity_squareRootReparametrization_of_pos (I := I) alpha (sq_pos_of_pos hr)
  rw [Real.sqrt_sq hr.le] at hsq
  let v : TangentSpace I (alpha r) :=
    lVelocity (I := I) (squareRootReparametrization alpha) (r ^ 2)
  have hsq' : lVelocity (I := I) alpha r = (2 * r) • v := by
    with_unfolding_all exact hsq
  have hvel' : lVelocity (I := I) (fun t => alpha (Real.sqrt (T - t))) (T - r ^ 2) =
      (-v : TangentSpace I (alpha r)) := by
    with_unfolding_all exact hvel
  unfold lRegularizedLagrangian
  rw [hsq', hvel']
  simp only [map_smul, smul_apply, smul_eq_mul, map_neg, neg_apply, neg_neg]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_eq_physical_density
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedLagrangian_eq_physical_density target :: scope.openDecls } }

theorem sqrt_mul_unweighted_action_le_lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T b s : ℝ) (hbs : b ≤ s) (hsT : s ≤ T)
    (alpha : ℝ → M)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume
      (Real.sqrt (T - s)) (Real.sqrt (T - b)))
    (hscalar : ∀ t ∈ _root_.Set.Ioo b s, 0 ≤ S.scalar t (alpha (Real.sqrt (T - t)))) :
    ENNReal.ofReal (Real.sqrt (T - s)) *
      (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
        (S.scalar t (alpha (Real.sqrt (T - t))) +
          (S.base.metric t).inner (alpha (Real.sqrt (T - t)))
            (lVelocity (I := I) (fun u => alpha (Real.sqrt (T - u))) t)
            (lVelocity (I := I) (fun u => alpha (Real.sqrt (T - u))) t))) ≤
      ENNReal.ofReal (lRegularizedAction S T alpha
        (Real.sqrt (T - s)) (Real.sqrt (T - b))) := by
  let a := Real.sqrt (T - s)
  let c := Real.sqrt (T - b)
  let U := fun t : ℝ => S.scalar t (alpha (Real.sqrt (T - t))) +
    (S.base.metric t).inner (alpha (Real.sqrt (T - t)))
      (lVelocity (I := I) (fun u => alpha (Real.sqrt (T - u))) t)
      (lVelocity (I := I) (fun u => alpha (Real.sqrt (T - u))) t)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hac : a ≤ c := Real.sqrt_le_sqrt (sub_le_sub_left hbs T)
  have ha2 : a ^ 2 = T - s := Real.sq_sqrt (sub_nonneg.mpr hsT)
  have hc2 : c ^ 2 = T - b := Real.sq_sqrt (sub_nonneg.mpr (hbs.trans hsT))
  have htime {r : ℝ} (hr : r ∈ _root_.Set.Ioo a c) : T - r ^ 2 ∈ _root_.Set.Ioo b s := by
    have hr0 : 0 ≤ r := ha.trans hr.1.le
    have hleft := (sq_lt_sq₀ ha hr0).mpr hr.1
    have hright := (sq_lt_sq₀ hr0 hc).mpr hr.2
    constructor <;> nlinarith
  have hU {r : ℝ} (hr : r ∈ _root_.Set.Ioo a c) : 0 ≤ U (T - r ^ 2) :=
    add_nonneg (hscalar _ (htime hr)) (metric_inner_self_nonneg _ _ _)
  have hdensity {r : ℝ} (hr : r ∈ _root_.Set.Ioo a c) :
      lRegularizedLagrangian S T alpha r = 2 * r ^ 2 * U (T - r ^ 2) := by
    have hrpos : 0 < r := ha.trans_lt hr.1
    have heq : T - (T - r ^ 2) = r ^ 2 := by ring
    dsimp only [U]
    rw [heq, Real.sqrt_sq hrpos.le]
    exact lRegularizedLagrangian_eq_physical_density S T alpha hrpos
  have hLag : ∀ᵐ r ∂volume.restrict (_root_.Set.Ioo a c), 0 ≤ lRegularizedLagrangian S T alpha r := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hdensity hr]
    exact mul_nonneg (by positivity) (hU hr)
  have hIntegral :
      (∫⁻ r in _root_.Set.Ioo a c, ENNReal.ofReal (lRegularizedLagrangian S T alpha r)) =
        ENNReal.ofReal (lRegularizedAction S T alpha a c) := by
    have hrestrict : volume.restrict (_root_.Set.Ioo a c) = volume.restrict (_root_.Set.Ioc a c) :=
      Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Ioc
    have hi : _root_.MeasureTheory.Integrable (lRegularizedLagrangian S T alpha) (volume.restrict (_root_.Set.Ioo a c)) := by
      rw [hrestrict]
      exact hint.1
    rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi hLag,
      ← _root_.MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hac]
    rfl
  have hchange : (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal (U t)) =
      ∫⁻ r in _root_.Set.Ioo a c, ENNReal.ofReal (2 * r) * ENNReal.ofReal (U (T - r ^ 2)) := by
    have h := lintegral_sub_sq_time (fun t => ENNReal.ofReal (U t)) T a c ha hac
    have hb : T - c ^ 2 = b := by rw [hc2]; ring
    have hs : T - a ^ 2 = s := by rw [ha2]; ring
    rw [hb, hs, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Ioc] at h
    exact h
  change ENNReal.ofReal a * (∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal (U t)) ≤
    ENNReal.ofReal (lRegularizedAction S T alpha a c)
  rw [hchange, ← _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hIntegral]
  apply _root_.MeasureTheory.lintegral_mono_ae
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : 0 ≤ r := ha.trans hr.1.le
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * r), ← ENNReal.ofReal_mul ha]
  apply ENNReal.ofReal_le_ofReal
  calc
    a * (2 * r * U (T - r ^ 2)) = (a * (2 * r)) * U (T - r ^ 2) := by ring
    _ ≤ (2 * r ^ 2) * U (T - r ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.mpr hr.1.le) hr0]) (hU hr)
    _ = lRegularizedLagrangian S T alpha r := (hdensity hr).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.sqrt_mul_unweighted_action_le_lRegularizedAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.sqrt_mul_unweighted_action_le_lRegularizedAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.sqrt_mul_unweighted_action_le_lRegularizedAction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.sqrt_mul_unweighted_action_le_lRegularizedAction

end DifferentialGeometry.PDE.RicciFlow.Perelman
