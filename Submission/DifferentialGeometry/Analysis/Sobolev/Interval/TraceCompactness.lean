import Submission.DifferentialGeometry.Analysis.Integration.Measure.UniformLimit
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.Energy
import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
private theorem isOpenPosMeasure_comap_Icc {a b : ℝ} (hab : a < b) :
    Measure.IsOpenPosMeasure ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).comap (Subtype.val : _root_.Set.Icc a b → ℝ)) := by
  refine ⟨fun U hU hUne => ?_⟩
  rw [comap_subtype_coe_apply measurableSet_Icc]
  obtain ⟨W, hW, hWU⟩ := Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hU
  rw [hWU, Subtype.range_coe]
  obtain ⟨x, hx⟩ := hUne
  have hxW : (x : ℝ) ∈ W := by
    have himage : (x : ℝ) ∈ Subtype.val '' U := _root_.Set.mem_image_of_mem Subtype.val hx
    rw [hWU] at himage
    exact himage.1
  have hxcl : (x : ℝ) ∈ closure (_root_.Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact x.property
  have hnonempty : (W ∩ _root_.Set.Ioo a b).Nonempty := mem_closure_iff.mp hxcl W hW hxW
  have hpos : 0 < _root_.MeasureTheory.MeasureSpace.volume (W ∩ _root_.Set.Ioo a b) := (hW.inter isOpen_Ioo).measure_pos _root_.MeasureTheory.MeasureSpace.volume hnonempty
  exact ne_of_gt (hpos.trans_le (_root_.MeasureTheory.measure_mono (_root_.Set.inter_subset_inter_right W _root_.Set.Ioo_subset_Icc_self)))

run_cmd do
  let target := ``Submission.MeasureTheory.isOpenPosMeasure_comap_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.isOpenPosMeasure_comap_Icc target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound
    {X ι : Type*} [PseudoMetricSpace X] {l : Filter ι}
    {F : ι → ℝ → X} {f : ℝ → X} {a b B : ℝ} (hab : a < b)
    (hF : ∀ i, ∀ s ∈ _root_.Set.Icc a b, ∀ t ∈ _root_.Set.Icc a b,
      _root_.Dist.dist (F i s) (F i t) ≤ Real.sqrt (B * |s - t|))
    (hf : ContinuousOn f (_root_.Set.Icc a b))
    (hae : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), _root_.Filter.Tendsto (fun i => F i t) l (𝓝 (f t))) :
    TendstoUniformlyOn F f l (_root_.Set.Icc a b) := by
  let μ : _root_.MeasureTheory.Measure (_root_.Set.Icc a b) := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).comap Subtype.val
  let : Measure.IsOpenPosMeasure μ := isOpenPosMeasure_comap_Icc hab
  have hmod : _root_.Filter.Tendsto (fun t : ℝ => Real.sqrt (B * t)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (B * t)) :=
      Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
    simpa only [_root_.MulZeroClass.mul_zero, Real.sqrt_zero] using hc.tendsto (0 : ℝ)
  have heq : Equicontinuous (fun i (t : _root_.Set.Icc a b) => F i t) :=
    Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => Real.sqrt (B * t)) hmod
      (fun i (t : _root_.Set.Icc a b) => F i t) (fun s t i => by
        simpa only [Subtype.dist_eq, Real.dist_eq] using hF i s s.property t t.property)
  have hfc : Continuous (fun t : _root_.Set.Icc a b => f t) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  have hpae : ∀ᵐ t : _root_.Set.Icc a b ∂μ, _root_.Filter.Tendsto (fun i => F i t) l (𝓝 (f t)) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp hae
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (tendstoUniformly_of_ae_tendsto_of_equicontinuous heq hfc hpae)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound ``Submission.MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound

end MeasureTheory

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) {a b C : ℝ}
    (hC : (∫ t in _root_.Set.Icc a b, ‖deriv f t‖ ^ 2) ≤ C)
    {x y : ℝ} (hx : x ∈ _root_.Set.Icc a b) (hy : y ∈ _root_.Set.Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ C * |x - y| := by
  have hderiv : _root_.MeasureTheory.MemLp (deriv f) 2 (volume.restrict (_root_.Set.Icc a b)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) K
      (Eventually.of_forall fun t => norm_deriv_le_of_lipschitz hf)
  have hi := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hderiv.aestronglyMeasurable).mp hderiv
  have hord {s t : ℝ} (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (hst : s ≤ t) :
      ‖f t - f s‖ ^ 2 ≤ C * (t - s) := by
    have hsub : _root_.Set.Icc s t ⊆ _root_.Set.Icc a b := _root_.Set.Icc_subset_Icc hs.1 ht.2
    have hac : AbsolutelyContinuousOnInterval f s t :=
      hf.lipschitzOnWith.absolutelyContinuousOnInterval
    have he := norm_sub_sq_le_mul_integral_norm_deriv_sq_of_absolutelyContinuousOnInterval
      hac (hderiv.mono_measure (Measure.restrict_mono hsub le_rfl))
      (show t ∈ _root_.Set.Icc s t from ⟨hst, le_rfl⟩)
      (show s ∈ _root_.Set.Icc s t from ⟨le_rfl, hst⟩)
    rw [intervalIntegral.integral_of_le hst, ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc] at he
    have hsmall : (∫ z in _root_.Set.Icc s t, ‖deriv f z‖ ^ 2) ≤ C :=
      (_root_.MeasureTheory.setIntegral_mono_set hi (Eventually.of_forall fun z => sq_nonneg ‖deriv f z‖)
        hsub.eventuallyLE).trans hC
    exact he.trans ((mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hst)).trans_eq
      (mul_comm _ _))
  rcases le_total x y with hxy | hyx
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact hord hx hy hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hord hy hx hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le

theorem exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n)) {C : ℝ}
    (hC : ∀ n, (∫ t in _root_.Set.Icc a b, ‖deriv (f n) t‖ ^ 2) ≤ C)
    (ha : Bornology.IsBounded (_root_.Set.range fun n => f n a)) :
    ∃ (φ : ℕ → ℕ) (g : C(_root_.Set.Icc a b, F)), StrictMono φ ∧
      TendstoUniformly (fun n (x : _root_.Set.Icc a b) => f (φ n) x) g _root_.Filter.atTop ∧
      ∀ s t : _root_.Set.Icc a b, ‖g s - g t‖ ^ 2 ≤ C * |(s : ℝ) - t| := by
  let fc (n : ℕ) : C(_root_.Set.Icc a b, F) := ⟨fun x => f n x, (hf n).continuous.comp continuous_subtype_val⟩
  have hdisp (n : ℕ) (x y : _root_.Set.Icc a b) :
      ‖fc n x - fc n y‖ ^ 2 ≤ C * |(x : ℝ) - y| :=
    norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le (hf n) (hC n) x.property y.property
  have hequi : Equicontinuous (fun n => (fc n : _root_.Set.Icc a b → F)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun s : ℝ => Real.sqrt (C * s))
    · have hc : Continuous (fun s : ℝ => Real.sqrt (C * s)) :=
        Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
      simpa only [_root_.MulZeroClass.mul_zero, Real.sqrt_zero] using hc.tendsto (0 : ℝ)
    · intro x y n
      simpa only [dist_eq_norm, Real.norm_eq_abs, Subtype.dist_eq, Real.dist_eq] using
        Real.le_sqrt_of_sq_le (hdisp n x y)
  obtain ⟨R, hR⟩ := ha.exists_norm_le
  have hC0 : 0 ≤ C := (_root_.MeasureTheory.integral_nonneg fun t => sq_nonneg ‖deriv (f 0) t‖).trans (hC 0)
  have hval (n : ℕ) (x : _root_.Set.Icc a b) :
      fc n x ∈ Metric.closedBall (0 : F) (R + Real.sqrt (C * (b - a))) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hd := hdisp n x ⟨a, le_rfl, hab.le⟩
    have hxa : |(x : ℝ) - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr x.property.1)]
      exact sub_le_sub_right x.property.2 a
    have hbnd : ‖fc n x - f n a‖ ≤ Real.sqrt (C * (b - a)) :=
      Real.le_sqrt_of_sq_le (hd.trans (mul_le_mul_of_nonneg_left hxa hC0))
    exact (norm_le_norm_sub_add (fc n x) (f n a)).trans
      (by linarith [hR (f n a) (_root_.Set.mem_range_self n)])
  obtain ⟨φ, g, hφ, hg⟩ := arzela_subseq_compact
    (Metric.closedBall (0 : F) (R + Real.sqrt (C * (b - a))))
    (_root_.ProperSpace.isCompact_closedBall _ _) fc hval hequi
  refine ⟨φ, g, hφ, hg, ?_⟩
  intro s t
  have ht := (((hg.tendsto_at s).sub (hg.tendsto_at t)).norm).pow 2
  exact le_of_tendsto ht (Eventually.of_forall fun n => hdisp (φ n) s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le

theorem exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n)) {C : ℝ}
    (hC : ∀ n, (∫ t in _root_.Set.Icc a b, ‖deriv (f n) t‖ ^ 2) ≤ C)
    {p : F} (ha : _root_.Filter.Tendsto (fun n => f n a) _root_.Filter.atTop (𝓝 p))
    (v : ℝ → F) (hv : ContinuousOn v (_root_.Set.Ioo a b))
    (hfv : ∀ᵐ x ∂volume.restrict (_root_.Set.Ioo a b), _root_.Filter.Tendsto (fun n => f n x) _root_.Filter.atTop (𝓝 (v x))) :
    ∃ g : C(_root_.Set.Icc a b, F),
      TendstoUniformlyOn f (Set.IccExtend hab.le g) _root_.Filter.atTop (_root_.Set.Icc a b) ∧
      _root_.Set.EqOn (Set.IccExtend hab.le g) v (_root_.Set.Ioo a b) ∧
      g ⟨a, le_rfl, hab.le⟩ = p ∧
      ∀ s t : _root_.Set.Icc a b, ‖g s - g t‖ ^ 2 ≤ C * |(s : ℝ) - t| := by
  obtain ⟨φ, g, hφ, hg, hmod⟩ := exists_subseq_tendstoUniformly_Icc_of_integral_deriv_sq_le
    hab f K hf hC (Metric.isBounded_range_of_tendsto _ ha)
  have heq : Set.IccExtend hab.le g =ᵐ[volume.restrict (_root_.Set.Ioo a b)] v := by
    filter_upwards [hfv, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx hxin
    have hpoint := hg.tendsto_at ⟨x, _root_.Set.Ioo_subset_Icc_self hxin⟩
    rw [Set.IccExtend_of_mem hab.le g (_root_.Set.Ioo_subset_Icc_self hxin)]
    exact tendsto_nhds_unique hpoint (hx.comp hφ.tendsto_atTop)
  have hgc : Continuous (Set.IccExtend hab.le g) :=
    g.continuous.comp continuous_projIcc
  have hwholeae : ∀ᵐ x ∂volume.restrict (_root_.Set.Icc a b),
      Tendsto (fun n => f n x) _root_.Filter.atTop (𝓝 (Set.IccExtend hab.le g x)) := by
    rw [← Measure.restrict_congr_set (_root_.MeasureTheory.Ioo_ae_eq_Icc (μ := _root_.MeasureTheory.MeasureSpace.volume))]
    filter_upwards [hfv, heq] with x hx heqx
    rw [heqx]
    exact hx
  have hwhole : TendstoUniformlyOn f (Set.IccExtend hab.le g) _root_.Filter.atTop (_root_.Set.Icc a b) := by
    apply tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound (B := C)
      hab _ hgc.continuousOn hwholeae
    intro n s hs t ht
    rw [dist_eq_norm]
    exact Real.le_sqrt_of_sq_le
      (norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le (hf n) (hC n) hs ht)
  refine ⟨g, hwhole, Measure.eqOn_Ioo_of_ae_eq _root_.MeasureTheory.MeasureSpace.volume heq hgc.continuousOn hv, ?_, hmod⟩
  exact tendsto_nhds_unique (hg.tendsto_at ⟨a, le_rfl, hab.le⟩) (ha.comp hφ.tendsto_atTop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le

theorem exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → F) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n)) {C : ℝ}
    (hC : ∀ n, (∫ t in _root_.Set.Icc a b, ‖deriv (f n) t‖ ^ 2) ≤ C)
    {p q : F} (ha : _root_.Filter.Tendsto (fun n => f n a) _root_.Filter.atTop (𝓝 p))
    (hb : _root_.Filter.Tendsto (fun n => f n b) _root_.Filter.atTop (𝓝 q))
    (v : ℝ → F) (hv : ContinuousOn v (_root_.Set.Ioo a b))
    (hfv : ∀ᵐ x ∂volume.restrict (_root_.Set.Ioo a b), _root_.Filter.Tendsto (fun n => f n x) _root_.Filter.atTop (𝓝 (v x))) :
    ∃ g : C(_root_.Set.Icc a b, F),
      TendstoUniformlyOn f (Set.IccExtend hab.le g) _root_.Filter.atTop (_root_.Set.Icc a b) ∧
      _root_.Set.EqOn (Set.IccExtend hab.le g) v (_root_.Set.Ioo a b) ∧
      g ⟨a, le_rfl, hab.le⟩ = p ∧ g ⟨b, hab.le, le_rfl⟩ = q ∧
      ∀ s t : _root_.Set.Icc a b, ‖g s - g t‖ ^ 2 ≤ C * |(s : ℝ) - t| := by
  obtain ⟨g, hg, hgv, hga, hmod⟩ :=
    exists_continuous_Icc_extension_of_ae_tendsto_of_integral_deriv_sq_le
      hab f K hf hC ha v hv hfv
  refine ⟨g, hg, hgv, hga, ?_, hmod⟩
  have hright := hg.tendsto_at (show b ∈ _root_.Set.Icc a b from ⟨hab.le, le_rfl⟩)
  rw [Set.IccExtend_of_mem hab.le g ⟨hab.le, le_rfl⟩] at hright
  exact tendsto_nhds_unique hright hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto

end DifferentialGeometry.Analysis.Sobolev

end
