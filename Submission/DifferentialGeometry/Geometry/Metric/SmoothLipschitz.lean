import Submission.DifferentialGeometry.Geometry.Metric.CompactDerivative
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Metric.LocalChartDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_radius_slack {B r rho a : ℝ} (hB : 0 ≤ B)
    (hrho : r < rho) (ha : B * r < a) :
    ∃ s : ℝ, r < s ∧ s < rho ∧ B * s ≤ a := by
  have hB1 : 0 < B + 1 := by linarith
  have hgap : 0 < (a - B * r) / (B + 1) := div_pos (by linarith) hB1
  obtain ⟨s, hrs, hs⟩ := exists_between
    (lt_min hrho (lt_add_of_pos_right r hgap))
  refine ⟨s, hrs, hs.trans_le (min_le_left _ _), ?_⟩
  have hdist : s - r < (a - B * r) / (B + 1) := by
    have hh := hs.trans_le (min_le_right _ _)
    linarith
  have hmul := (lt_div_iff₀ hB1).mp hdist
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.exists_radius_slack
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.exists_radius_slack target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_lintegral_of_metric_mfderiv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {f : M → F} {γ : ℝ → M} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (_root_.Set.Icc a b))
    (hf : ∀ t ∈ _root_.Set.Icc a b, ContMDiffAt I 𝓘(ℝ, F) 1 f (γ t))
    (hbound : ∀ t ∈ _root_.Set.Ioo a b, ∀ v : TangentSpace I (γ t),
      ‖(mfderiv I 𝓘(ℝ, F) f (γ t) v : F)‖ ≤ L * Real.sqrt (g.inner (γ t) v v)) :
    _root_.EDist.edist (f (γ a)) (f (γ b)) ≤ ENNReal.ofReal L *
      ∫⁻ t in _root_.Set.Ioo a b, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)))) := by
  have hcomp : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, F) 1 (f ∘ γ) (_root_.Set.Icc a b) := by
    intro t ht
    exact (hf t ht).comp_contMDiffWithinAt t (hγ t ht)
  have hη : ContDiffOn ℝ 1 (f ∘ γ) (_root_.Set.Icc a b) := contMDiffOn_iff_contDiffOn.mp hcomp
  have hh := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hη hab
  rw [← edist_eq_enorm_sub, _root_.PseudoEMetricSpace.edist_comm] at hh
  apply hh.trans
  rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  rw [← _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply _root_.MeasureTheory.lintegral_mono_ae
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  have hγt := (hγ t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hD := mfderiv_comp t ((hf t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt one_ne_zero)
    (hγt.mdifferentiableAt one_ne_zero)
  have hder : deriv (f ∘ γ) t =
      (mfderiv I 𝓘(ℝ, F) f (γ t)) (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv, hD]
    rfl
  rw [hder]
  have hb := ENNReal.ofReal_le_ofReal
    (hbound t ht (mfderiv 𝓘(ℝ) I γ t (1 : ℝ)))
  simpa only [ofReal_norm, ENNReal.ofReal_mul hL] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.edist_comp_le_lintegral_of_metric_mfderiv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.edist_comp_le_lintegral_of_metric_mfderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.edist_comp_le_lintegral_of_metric_mfderiv_bound ``Submission.DifferentialGeometry.Geometry.edist_comp_le_lintegral_of_metric_mfderiv_bound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem edist_comp_le_metric_path_length_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f U)
    (hbound : ∀ (x : M), x ∈ U → ∀ (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc 0 1))
    (hγU : _root_.Set.MapsTo γ (_root_.Set.Icc 0 1) U) :
    _root_.EDist.edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) *
      ∫⁻ t in _root_.Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
  have h := edist_comp_le_lintegral_of_metric_mfderiv_bound g (by norm_num : (0 : ℝ) ≤ 1)
    C.coe_nonneg hγ
    (fun t ht => (hf (γ t) (hγU ht)).contMDiffAt (hU.mem_nhds (hγU ht)))
    (fun t ht => hbound (γ t) (hγU ⟨ht.1.le, ht.2.le⟩))
  rw [_root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc, ENNReal.ofReal_coe_nnreal] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.edist_comp_le_metric_path_length_of_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.edist_comp_le_metric_path_length_of_contMDiffOn target :: scope.openDecls } }


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_metric_path_length
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc 0 1)) :
    _root_.EDist.edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) *
      ∫⁻ t in _root_.Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) := by
  exact edist_comp_le_metric_path_length_of_contMDiffOn g isOpen_univ hf.contMDiffOn
    (fun z _ v => hbound z v) hγ (_root_.Set.mapsTo_univ γ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.edist_comp_le_metric_path_length then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.edist_comp_le_metric_path_length"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.edist_comp_le_metric_path_length ``Submission.DifferentialGeometry.Geometry.edist_comp_le_metric_path_length

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_map_le_of_metric_mfderiv_bound
    (g : SmoothRiemannianMetric I M) {f : M → F} {C : ℝ≥0} (hC : 0 < C)
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ C * Real.sqrt (g.inner x v v)) (x y : M) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  change _root_.EDist.edist (f x) (f y) ≤ (C : ℝ≥0∞) * Manifold.riemannianEDist I x y
  rw [Manifold.riemannianEDist, ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro hγ
  rw [_root_.Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc, _root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hc := edist_comp_le_metric_path_length g hf hbound
    (hγ.comp_contMDiffOn contMDiffOn_projIcc)
  have hn (p : M) (v : TangentSpace I p) :
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp only [Function.comp_apply, _root_.Set.projIcc_left, _root_.Set.projIcc_right, hn] at hc
  change _root_.EDist.edist (f (γ 0)) (f (γ 1)) ≤ _ at hc
  simp only [γ.source, γ.target] at hc
  convert! hc using 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.edist_map_le_of_metric_mfderiv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.edist_map_le_of_metric_mfderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.edist_map_le_of_metric_mfderiv_bound ``Submission.DifferentialGeometry.Geometry.edist_map_le_of_metric_mfderiv_bound

theorem exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (hcompact : HasCompactSupport f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y,
      edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g hf hcompact
  have hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ (B + 1 : ℝ≥0) * Real.sqrt (g.inner x v v) := by
    intro x v
    exact (hB x v).trans
      (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))
  exact ⟨B + 1, by positivity,
    edist_map_le_of_metric_mfderiv_bound g (by positivity) hf hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport ``Submission.DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport

theorem exists_riemannian_lipschitz_of_contMDiff
    [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, _root_.EDist.edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDistOf g x y := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound g hf
  have hbound : ∀ (x : M) (v : TangentSpace I x),
      ‖(mfderiv I 𝓘(ℝ, F) f x v : F)‖ ≤ (B + 1 : ℝ≥0) * Real.sqrt (g.inner x v v) := by
    intro x v
    exact (hB x v).trans (mul_le_mul_of_nonneg_right (by simp) (Real.sqrt_nonneg _))
  exact ⟨B + 1, by positivity, edist_map_le_of_metric_mfderiv_bound g (by positivity) hf hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff ``Submission.DifferentialGeometry.Geometry.exists_riemannian_lipschitz_of_contMDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem norm_sub_le_mul_of_mfderiv_bound_on_ball
    (g : SmoothRiemannianMetric I M) {f : M → F} (x : M) {ρ B r : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, F) 1 f {z | riemannianEDistOf g x z < ENNReal.ofReal ρ})
    (hB : 0 ≤ B)
    (hbound : ∀ z, riemannianEDistOf g x z < ENNReal.ofReal ρ →
      ∀ v : TangentSpace I z,
        ‖(mfderiv I 𝓘(ℝ, F) f z v : F)‖ ≤ B * Real.sqrt (g.inner z v v))
    (hr : 0 ≤ r) (hrρ : r < ρ) {y : M}
    (hy : riemannianEDistOf g x y ≤ ENNReal.ofReal r) :
    ‖f y - f x‖ ≤ B * r := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hopen : IsOpen {z | riemannianEDistOf g x z < ENNReal.ofReal ρ} := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨δ, hδ, hzδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hz
    have hlocal := eventually_riemannianEDist_lt I z
      (c := (δ : ℝ≥0∞)) (by exact_mod_cast hδ)
    filter_upwards [hlocal] with w hw
    exact (riemannianEDistOf_triangle g x z w).trans_lt
      ((add_le_add_right hw.le _).trans_lt hzδ)
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  obtain ⟨s, hrs, hsρ, hBsa⟩ := exists_radius_slack hB hrρ ha
  have hs : 0 < s := hr.trans_lt hrs
  have hsmall : _root_.Manifold.riemannianEDist I x y < ENNReal.ofReal s :=
    hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hrs)
  obtain ⟨γ, hγx, hγy, hγ, hlen⟩ := _root_.Manifold.exists_lt_of_riemannianEDist_lt hsmall
  have hmaps : _root_.Set.MapsTo γ (_root_.Set.Icc 0 1)
      {z | riemannianEDistOf g x z < ENNReal.ofReal ρ} := by
    apply Metric.mapsTo_of_riemannianEDistOf_add_pathELength_lt g x _
      (ENNReal.ofReal ρ) (fun _ hz => hz) γ hγ
    rw [hγx, riemannianEDistOf_self, zero_add]
    exact hlen.trans ((ENNReal.ofReal_lt_ofReal_iff (hs.trans hsρ)).mpr hsρ)
  let C : ℝ≥0 := ⟨B, hB⟩
  have hpath := edist_comp_le_metric_path_length_of_contMDiffOn g
    (C := C) hopen hf hbound hγ hmaps
  have hn (z : M) (v : TangentSpace I z) :
      ENNReal.ofReal (Real.sqrt (g.inner z v v)) = ‖v‖ₑ := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp only [hγx, hγy, hn] at hpath
  rw [← _root_.Manifold.pathELength_eq_lintegral_mfderiv_Icc] at hpath
  have hle := hpath.trans (mul_le_mul_right hlen.le (C : ℝ≥0∞))
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal B := by
    rw [ENNReal.ofReal_eq_coe_nnreal hB]
    rfl
  rw [hC, ← ENNReal.ofReal_mul hB, _root_.PseudoEMetricSpace.edist_comm, edist_eq_enorm_sub, ← ofReal_norm] at hle
  exact ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hs.le)).mp hle).trans hBsa

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.norm_sub_le_mul_of_mfderiv_bound_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.norm_sub_le_mul_of_mfderiv_bound_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.norm_sub_le_mul_of_mfderiv_bound_on_ball ``Submission.DifferentialGeometry.Geometry.norm_sub_le_mul_of_mfderiv_bound_on_ball

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem abs_sub_le_mul_of_mfderiv_bound_on_ball
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (x : M) {ρ B r : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z, riemannianEDistOf g x z < ENNReal.ofReal ρ →
      ∀ v : TangentSpace I z,
        |(show ℝ from mfderiv I 𝓘(ℝ) f z v)| ≤ B * Real.sqrt (g.inner z v v))
    (hr : 0 ≤ r) (hrρ : r < ρ) {y : M}
    (hy : riemannianEDistOf g x y ≤ ENNReal.ofReal r) :
    |f y - f x| ≤ B * r := by
  exact norm_sub_le_mul_of_mfderiv_bound_on_ball g x hf.contMDiffOn hB hbound hr hrρ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.abs_sub_le_mul_of_mfderiv_bound_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.abs_sub_le_mul_of_mfderiv_bound_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.abs_sub_le_mul_of_mfderiv_bound_on_ball ``Submission.DifferentialGeometry.Geometry.abs_sub_le_mul_of_mfderiv_bound_on_ball

end DifferentialGeometry.Geometry
