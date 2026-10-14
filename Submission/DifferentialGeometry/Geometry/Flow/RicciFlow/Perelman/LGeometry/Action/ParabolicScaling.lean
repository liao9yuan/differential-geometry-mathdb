import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityComposition
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem lintegral_affine_time
    (f : ℝ → ℝ≥0∞) (b s q : ℝ) (hq : 0 < q) :
    (∫⁻ t in _root_.Set.Ioc 0 (q * (s - b)), ENNReal.ofReal q⁻¹ * f (b + t / q)) =
      ∫⁻ t in _root_.Set.Ioc b s, f t := by
  let F := fun t : ℝ => b + t / q
  have himage : F '' _root_.Set.Ioc 0 (q * (s - b)) = _root_.Set.Ioc b s := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      change b < b + u / q ∧ b + u / q ≤ s
      constructor
      · exact lt_add_of_pos_right b (div_pos hu.1 hq)
      · have hh : u / q ≤ s - b := (div_le_iff₀ hq).mpr (by nlinarith [hu.2])
        nlinarith
    · intro ht
      refine ⟨q * (t - b), ⟨mul_pos hq (sub_pos.mpr ht.1),
        mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 b) hq.le⟩, ?_⟩
      dsimp only [F]
      field_simp
      ring
  have hF (t : ℝ) : HasFDerivAt F (q⁻¹ • ContinuousLinearMap.id ℝ ℝ) t := by
    convert (((hasFDerivAt_id t).const_smul q⁻¹).const_add b) using 1
    all_goals first | rfl | (ext x; simp [F, div_eq_mul_inv, mul_comm, smul_eq_mul])
  have hinj : Function.Injective F := by
    intro x y hxy
    dsimp only [F] at hxy
    exact (div_left_inj' hq.ne').mp (add_left_cancel hxy)
  have hh := _root_.MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := _root_.MeasureTheory.MeasureSpace.volume) (s := _root_.Set.Ioc 0 (q * (s - b))) measurableSet_Ioc (fun t _ => (hF t).hasFDerivWithinAt) hinj.injOn f
  rw [himage] at hh
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_smul, Module.finrank_self,
    pow_one, LinearMap.det_id, mul_one, abs_of_pos (inv_pos.mpr hq)] using hh.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_affine_time
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lintegral_affine_time target :: scope.openDecls } }

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

theorem unweighted_action_parabolic_rescaling
    (g : ℝ → SmoothRiemannianMetric I M) (alpha : ℝ → M)
    (b s q : ℝ) (hq : 0 < q) :
    (∫⁻ t in _root_.Set.Ioc 0 (q * (s - b)), ENNReal.ofReal
      (metricScalarAt (scaleMetric q hq (g (b + t / q))) (alpha (b + t / q)) +
        (scaleMetric q hq (g (b + t / q))).inner (alpha (b + t / q))
          (lVelocity (I := I) (fun u => alpha (b + u / q)) t)
          (lVelocity (I := I) (fun u => alpha (b + u / q)) t))) =
      ∫⁻ t in _root_.Set.Ioc b s, ENNReal.ofReal
        (metricScalarAt (g t) (alpha t) +
          (g t).inner (alpha t) (lVelocity (I := I) alpha t) (lVelocity (I := I) alpha t)) := by
  rw [← lintegral_affine_time (fun t => ENNReal.ofReal
    (metricScalarAt (g t) (alpha t) +
      (g t).inner (alpha t) (lVelocity (I := I) alpha t) (lVelocity (I := I) alpha t))) b s q hq]
  apply _root_.MeasureTheory.lintegral_congr
  intro t
  rw [metricScalarAt_scaleMetric, lVelocity_comp_affine_time alpha b q t hq.ne']
  simp only [scaleMetric_inner, map_smul, smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (inv_pos.mpr hq).le]
  congr 1
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_parabolic_rescaling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_parabolic_rescaling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_parabolic_rescaling ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unweighted_action_parabolic_rescaling


end DifferentialGeometry.PDE.RicciFlow.Perelman
