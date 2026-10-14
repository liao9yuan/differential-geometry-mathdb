import Submission.DifferentialGeometry.Geometry.Comparison.Distance.EndpointRate
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Connected.TotallyDisconnected
import Submission.DifferentialGeometry.Geometry.Metric.Path.Speed
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_of_curve_speed_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc a b))
    (hC : ∀ t ∈ _root_.Set.Ioo a b, Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) ≤ C) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal C * ENNReal.ofReal (b - a) := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  apply Manifold.riemannianEDist_le_of_curve_speed_bound hab hγ
  intro t ht
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  exact ENNReal.ofReal_le_ofReal (hC t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_le_of_curve_speed_bound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem riemannian_curve_edist_le_of_speed_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hC : ∀ t, Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))) ≤ C) (x y : ℝ) :
    riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist 𝓘(ℝ, E) (γ x) (γ y) ≤ _
  have hnorm (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)‖ₑ ≤ (C : ℝ≥0∞) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    simpa only [ENNReal.ofReal_coe_nnreal] using! ENNReal.ofReal_le_ofReal (hC t)
  have hordered (a b : ℝ) (hab : a ≤ b) :
      Manifold.riemannianEDist 𝓘(ℝ, E) (γ a) (γ b) ≤ (C : ℝ≥0∞) * _root_.EDist.edist a b := by
    apply (_root_.Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl hab).trans
    rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      (∫⁻ t in _root_.Set.Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)‖ₑ) ≤
          ∫⁻ _t in _root_.Set.Icc a b, (C : ℝ≥0∞) := _root_.MeasureTheory.lintegral_mono (fun t => hnorm t)
      _ = (C : ℝ≥0∞) * _root_.EDist.edist a b := by
        rw [_root_.MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · rw [_root_.Manifold.riemannianEDist_comm, _root_.PseudoEMetricSpace.edist_comm x y]
    exact hordered y x hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannian_curve_edist_le_of_speed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannian_curve_edist_le_of_speed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannian_curve_edist_le_of_speed_bound ``Submission.DifferentialGeometry.Geometry.riemannian_curve_edist_le_of_speed_bound

end DifferentialGeometry.Geometry

noncomputable section
open _root_.Filter

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem inner_mfderiv_self_eq_sq_of_edist_eq_on_interval
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b c t : ℝ} (hc : 0 ≤ c)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (_root_.Set.Icc a b)) (ht : t ∈ _root_.Set.Ioo a b)
    (hdist : ∀ s ∈ _root_.Set.Icc a b, ∀ u ∈ _root_.Set.Icc a b,
      riemannianEDistOf g (γ s) (γ u) = ENNReal.ofReal (c * |s - u|)) :
    g.inner (γ t) (mfderiv 𝓘(ℝ) I γ t 1) (mfderiv 𝓘(ℝ) I γ t 1) = c ^ 2 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    have hpre := isPreconnected_Icc.image γ hγ.continuousOn
    have heq : γ t = γ b := hpre.subsingleton
      ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩ ⟨b, ⟨ht.1.le.trans ht.2.le, le_rfl⟩, rfl⟩
    have hz := hdist t ⟨ht.1.le, ht.2.le⟩ b ⟨ht.1.le.trans ht.2.le, le_rfl⟩
    rw [heq, riemannianEDistOf_self] at hz
    have hprod : c * |t - b| ≤ 0 := ENNReal.ofReal_eq_zero.mp hz.symm
    have hc0 : c = 0 := by
      have hpos : 0 < |t - b| := abs_pos.mpr (sub_ne_zero.mpr ht.2.ne)
      nlinarith
    let _ : Subsingleton (TangentSpace I (γ t)) := (inferInstance : Subsingleton E)
    have hzero : mfderiv 𝓘(ℝ) I γ t (1 : ℝ) = 0 := Subsingleton.elim _ _
    change (g.inner (γ t) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ) I γ t 1) (mfderiv 𝓘(ℝ) I γ t 1) = c ^ 2
    change (mfderiv 𝓘(ℝ) I γ t 1 : E) = 0 at hzero
    simp only [hc0, hzero, map_zero, zero_pow (by norm_num : 2 ≠ 0)]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hdiff : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by decide)
  have hspeed := riemannianEDistOf_div_tendsto_speed g γ t hdiff
  have hlimit : _root_.Filter.Tendsto
      (fun h : ℝ => (riemannianEDistOf g (γ (t + h)) (γ t)).toReal / h)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT (sub_pos.mpr ht.2)] with h hh
    have hmem : t + h ∈ _root_.Set.Icc a b := ⟨by linarith [hh.1, ht.1], by linarith [hh.2]⟩
    rw [hdist (t + h) hmem t ⟨ht.1.le, ht.2.le⟩, add_sub_cancel_left,
      abs_of_pos hh.1, ENNReal.toReal_ofReal (mul_nonneg hc hh.1.le)]
    field_simp [hh.1.ne']
  have hsqrt := tendsto_nhds_unique hspeed hlimit
  exact (Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg g _ _)).symm.trans
    (congrArg (fun z : ℝ => z ^ 2) hsqrt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_sq_of_edist_eq_on_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_sq_of_edist_eq_on_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_sq_of_edist_eq_on_interval ``Submission.DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_sq_of_edist_eq_on_interval

theorem inner_mfderiv_self_eq_one_of_edist_eq_on_interval
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (_root_.Set.Icc a b)) (ht : t ∈ _root_.Set.Ioo a b)
    (hdist : ∀ s ∈ _root_.Set.Icc a b, ∀ u ∈ _root_.Set.Icc a b,
      riemannianEDistOf g (γ s) (γ u) = ENNReal.ofReal |s - u|) :
    g.inner (γ t) (mfderiv 𝓘(ℝ) I γ t 1) (mfderiv 𝓘(ℝ) I γ t 1) = 1 := by
  simpa only [one_pow] using inner_mfderiv_self_eq_sq_of_edist_eq_on_interval g
    (c := 1) zero_le_one hγ ht (by simpa only [one_mul] using hdist)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_one_of_edist_eq_on_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_one_of_edist_eq_on_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_one_of_edist_eq_on_interval ``Submission.DifferentialGeometry.Geometry.Riemannian.inner_mfderiv_self_eq_one_of_edist_eq_on_interval

end DifferentialGeometry.Geometry.Riemannian
