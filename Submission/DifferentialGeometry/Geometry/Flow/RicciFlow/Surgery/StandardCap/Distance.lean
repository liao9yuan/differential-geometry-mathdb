import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Topology.MetricSpace.ProperSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.InnerProductSpace _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance metricBundle : _root_.Bundle.RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
  ⟨metric.toRiemannianMetric⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricBundle target :: scope.openDecls } }

private local instance metricContinuous :
    IsContinuousRiemannianBundle E3 (fun x : E3 => TangentSpace (𝓡 3) x) :=
  ⟨metric.inner, metric.contMDiff.continuous, fun _ _ _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricContinuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricContinuous target :: scope.openDecls } }

private theorem metric_enorm (x : E3) (v : TangentSpace (𝓡 3) x) :
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (metric.inner x v v)) := by
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_enorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_enorm target :: scope.openDecls } }

theorem edist_le_euclidean (x y : E3) : riemannianEDistOf metric x y ≤ _root_.EDist.edist x y := by
  let γ := ContinuousAffineMap.lineMap (R := ℝ) x y
  change _root_.Manifold.riemannianEDist (𝓡 3) x y ≤ _
  have h := _root_.Manifold.riemannianEDist_le_pathELength (I := 𝓡 3) (x := x) (y := y) (γ := γ) (a := 0) (b := 1)
    (contMDiffOn_iff_contDiffOn.mpr γ.contDiff.contDiffOn)
    (by simp [γ, ContinuousAffineMap.coe_lineMap_eq])
    (by simp [γ, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
  refine h.trans ?_
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderivWithin_Icc, ← lintegral_fderiv_lineMap_eq_edist]
  refine _root_.MeasureTheory.setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [metric_enorm]
  simp only [mfderivWithin_eq_fderivWithin]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt
    (metric_inner_le (γ t) (fderivWithin ℝ γ (_root_.Set.Icc 0 1) t 1))).trans_eq
      (Real.sqrt_sq (norm_nonneg _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_le_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_le_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_le_euclidean ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_le_euclidean

private def regularizedRadius (ε : ℝ) (x : E3) : ℝ := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius target :: scope.openDecls } }

private theorem regularizedRadius_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedRadius ε) := by
  apply ((contDiff_norm_sq ℝ).add contDiff_const).sqrt
  intro x
  exact ne_of_gt (by nlinarith [sq_nonneg ‖x‖])

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_smooth target :: scope.openDecls } }

private theorem regularizedRadius_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (x : E3) :
    HasFDerivAt (regularizedRadius ε)
      ((regularizedRadius ε x)⁻¹ • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).sqrt
    (ne_of_gt (show 0 < ‖x‖ ^ 2 + ε ^ 2 by nlinarith [sq_nonneg ‖x‖]))
  convert h using 1 <;> try rfl
  ext v
  simp [regularizedRadius, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_hasFDerivAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_hasFDerivAt target :: scope.openDecls } }

private theorem metric_self_nonneg (x v : E3) : 0 ≤ metric.inner x v v := by
  by_cases hv : v = 0
  · rw [metric_inner]
    subst v
    simp only [map_zero, le_refl]
  · exact (metric.pos x v hv).le

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_self_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_self_nonneg target :: scope.openDecls } }

private theorem radial_inner_sq_le (x v : E3) :
    ⟪x, v⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * metric.inner x v v := by
  have h := real_inner_mul_inner_self_le
    (show TangentSpace (𝓡 3) x from x) (show TangentSpace (𝓡 3) x from v)
  change metric.inner x x v * metric.inner x x v ≤ metric.inner x x x * metric.inner x v v at h
  simpa only [metric_inner_radial, real_inner_self_eq_norm_sq, pow_two] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_inner_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_inner_sq_le target :: scope.openDecls } }

private theorem regularizedRadius_deriv_le {ε : ℝ} (hε : 0 < ε) (x v : E3) :
    ‖fderiv ℝ (regularizedRadius ε) x v‖ ≤ Real.sqrt (metric.inner x v v) := by
  rw [(regularizedRadius_hasFDerivAt hε x).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Real.norm_eq_abs]
  have hden : 0 < regularizedRadius ε x := by
    apply Real.sqrt_pos.mpr
    nlinarith [sq_nonneg ‖x‖]
  have hden2 : regularizedRadius ε x ^ 2 = ‖x‖ ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg ‖x‖])
  have hsq : ((regularizedRadius ε x)⁻¹ * ⟪x, v⟫_ℝ) ^ 2 ≤ metric.inner x v v := by
    rw [mul_comm, ← div_eq_mul_inv, div_pow, div_le_iff₀ (sq_pos_of_pos hden)]
    calc ⟪x, v⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * metric.inner x v v := radial_inner_sq_le x v
      _ ≤ metric.inner x v v * regularizedRadius ε x ^ 2 := by
        rw [hden2]
        nlinarith [mul_nonneg (sq_nonneg ε) (metric_self_nonneg x v)]
  calc |(regularizedRadius ε x)⁻¹ * ⟪x, v⟫_ℝ| =
      Real.sqrt (((regularizedRadius ε x)⁻¹ * ⟪x, v⟫_ℝ)^2) := Real.sqrt_sq_eq_abs _ |>.symm
    _ ≤ Real.sqrt (metric.inner x v v) := Real.sqrt_le_sqrt hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_deriv_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_deriv_le target :: scope.openDecls } }

private theorem regularizedRadius_sub_le_length {ε : ℝ} (hε : 0 < ε)
    {γ : ℝ → E3} (hγ : ContDiff ℝ 1 γ) :
    ENNReal.ofReal |regularizedRadius ε (γ 1) - regularizedRadius ε (γ 0)| ≤
      pathELength (𝓡 3) γ 0 1 := by
  have hc : ContDiff ℝ 1 (regularizedRadius ε ∘ γ) :=
    ((regularizedRadius_smooth hε).of_le (by simp)).comp hγ
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hc.contDiffOn zero_le_one
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  refine (show ENNReal.ofReal |regularizedRadius ε (γ 1) - regularizedRadius ε (γ 0)| ≤
      ∫⁻ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (regularizedRadius ε ∘ γ) t‖ₑ from by
        simpa only [Function.comp_apply, ← ofReal_norm, Real.norm_eq_abs] using h).trans ?_
  refine _root_.MeasureTheory.setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [metric_enorm, mfderiv_eq_fderiv, ← ofReal_norm]
  change ENNReal.ofReal ‖deriv (regularizedRadius ε ∘ γ) t‖ ≤
    ENNReal.ofReal (Real.sqrt (metric.inner (γ t) (deriv γ t) (deriv γ t)))
  rw [fderiv_comp_deriv t (regularizedRadius_smooth hε |>.differentiable (by simp) |>.differentiableAt)
    (hγ.differentiable one_ne_zero |>.differentiableAt)]
  exact ENNReal.ofReal_le_ofReal (regularizedRadius_deriv_le hε (γ t) (deriv γ t))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_sub_le_length
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.regularizedRadius_sub_le_length target :: scope.openDecls } }

private theorem norm_sub_norm_le_length {γ : ℝ → E3} (hγ : ContDiff ℝ 1 γ) :
    ENNReal.ofReal |‖γ 1‖ - ‖γ 0‖| ≤ _root_.Manifold.pathELength (𝓡 3) γ 0 1 := by
  have hc : Continuous (fun ε : ℝ =>
      ENNReal.ofReal |regularizedRadius ε (γ 1) - regularizedRadius ε (γ 0)|) := by
    apply ENNReal.continuous_ofReal.comp
    unfold regularizedRadius
    fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ =>
      ENNReal.ofReal |regularizedRadius ε (γ 1) - regularizedRadius ε (γ 0)|)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal |‖γ 1‖ - ‖γ 0‖|)) := by
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [regularizedRadius, zero_pow two_ne_zero, add_zero,
      Real.sqrt_sq (norm_nonneg _)]
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact regularizedRadius_sub_le_length hε hγ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.norm_sub_norm_le_length
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.norm_sub_norm_le_length target :: scope.openDecls } }

theorem radial_difference_le_edist (x y : E3) :
    ENNReal.ofReal |‖y‖ - ‖x‖| ≤ riemannianEDistOf metric x y := by
  change _ ≤ _root_.Manifold.riemannianEDist (𝓡 3) x y
  by_contra! h
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
    _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt h zero_lt_one
  have hbound := norm_sub_norm_le_length (contMDiff_iff_contDiff.mp hγ)
  rw [hγ0, hγ1] at hbound
  exact hbound.not_gt hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_difference_le_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_difference_le_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_difference_le_edist ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radial_difference_le_edist

@[simp] theorem edist_zero (x : E3) : riemannianEDistOf metric 0 x = ENNReal.ofReal ‖x‖ := by
  apply le_antisymm
  · simpa only [edist_dist, dist_zero_left] using edist_le_euclidean 0 x
  · simpa only [norm_zero, sub_zero, abs_of_nonneg (norm_nonneg _)] using
      radial_difference_le_edist 0 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_zero

theorem edist_ne_top (x y : E3) : riemannianEDistOf metric x y ≠ ⊤ :=
  ne_top_of_le_ne_top (_root_.edist_ne_top x y) (edist_le_euclidean x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_ne_top ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_ne_top

theorem distance_zero (x : E3) : (riemannianEDistOf metric 0 x).toReal = ‖x‖ := by
  rw [edist_zero, ENNReal.toReal_ofReal (norm_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.distance_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.distance_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.distance_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.distance_zero

theorem metric_closedBall_zero (r : ℝ≥0) :
    {x : E3 | riemannianEDistOf metric 0 x ≤ r} = Metric.closedBall (0 : E3) r := by
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, edist_zero]
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff r.coe_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_closedBall_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_closedBall_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_closedBall_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_closedBall_zero

theorem edist_radial {e : E3} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    riemannianEDistOf metric (a • e) (b • e) = ENNReal.ofReal |a - b| := by
  apply le_antisymm
  · refine (edist_le_euclidean (a • e) (b • e)).trans_eq ?_
    rw [edist_dist, dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
  · simpa only [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg ha,
      abs_of_nonneg hb, abs_sub_comm] using radial_difference_le_edist (a • e) (b • e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_radial ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_radial

private theorem compact_euclidean_radial_ball (r : ℝ) :
    IsCompact {x : E3 | ‖x‖ ≤ r} := by
  simpa only [Metric.closedBall, dist_zero_right] using
    (_root_.ProperSpace.isCompact_closedBall (0 : E3) r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compact_euclidean_radial_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.compact_euclidean_radial_ball target :: scope.openDecls } }

private abbrev intrinsicMetricSpace : MetricSpace E3 :=
  letI : EMetricSpace E3 := EMetricSpace.ofRiemannianMetric (𝓡 3) E3
  EMetricSpace.toMetricSpace (fun x y => edist_ne_top x y)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace target :: scope.openDecls } }

private theorem intrinsicMetricSpace_dist_zero (x : E3) :
    @_root_.Dist.dist E3 intrinsicMetricSpace.toDist 0 x = ‖x‖ := distance_zero x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace_dist_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace_dist_zero target :: scope.openDecls } }

private theorem intrinsicMetricSpace_proper :
    @ProperSpace E3 intrinsicMetricSpace.toPseudoMetricSpace := by
  let : PseudoMetricSpace E3 := intrinsicMetricSpace.toPseudoMetricSpace
  let : Dist E3 := intrinsicMetricSpace.toDist
  apply ProperSpace.of_seq_closedBall (x := (0 : E3)) (r := fun r : ℝ => r) Filter.tendsto_id
  apply Filter.Eventually.of_forall
  intro r
  convert compact_euclidean_radial_ball r using 1 <;> try rfl
  ext x
  change _root_.Dist.dist x 0 ≤ r ↔ ‖x‖ ≤ r
  rw [dist_comm]
  exact Iff.of_eq (congrArg (fun s => s ≤ r) (intrinsicMetricSpace_dist_zero x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace_proper
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicMetricSpace_proper target :: scope.openDecls } }

theorem metric_complete : RiemannianMetricComplete metric :=
  ⟨@complete_of_proper E3 intrinsicMetricSpace.toPseudoMetricSpace intrinsicMetricSpace_proper⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete

theorem isCompact_metric_closedBall (x : E3) (r : ℝ≥0) :
    IsCompact {y : E3 | riemannianEDistOf metric x y ≤ r} := by
  let : PseudoMetricSpace E3 := intrinsicMetricSpace.toPseudoMetricSpace
  let : PseudoEMetricSpace E3 := intrinsicMetricSpace.toPseudoEMetricSpace
  let : ProperSpace E3 := intrinsicMetricSpace_proper
  have h := _root_.ProperSpace.isCompact_closedBall x (r : ℝ)
  rw [← Metric.closedEBall_coe] at h
  have hset : Metric.closedEBall x r = {y : E3 | riemannianEDistOf metric x y ≤ r} := by
    ext y
    change riemannianEDistOf metric y x ≤ r ↔ _
    rw [show riemannianEDistOf metric y x = riemannianEDistOf metric x y from
      _root_.Manifold.riemannianEDist_comm]
    rfl
  rw [hset] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_metric_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_metric_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_metric_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_metric_closedBall

def core : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | riemannianEDistOf metric 0 x ≤ ENNReal.ofReal transitionEnd}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.core ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.core

theorem core_eq_radial : core = {x : E3 | ‖x‖ ≤ transitionEnd} := by
  ext x
  simp only [core, Set.mem_ofPred_eq, edist_zero,
    ENNReal.ofReal_le_ofReal_iff transitionEnd_pos.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_radial ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_radial

theorem core_eq_closedBall : core = Metric.closedBall (0 : E3) transitionEnd := by
  rw [core_eq_radial]
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.core_eq_closedBall

theorem isCompact_core : IsCompact core := by
  rw [core_eq_radial]
  exact compact_euclidean_radial_ball transitionEnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_core ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.isCompact_core

end DifferentialGeometry.PDE.RicciFlow.StandardCap
