import Submission.DifferentialGeometry.Geometry.Measure.Energy.ScalarComposition
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ProbeLowerSemicontinuity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {P : M → ℝ} {L K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (hP : ∀ p q, _root_.EDist.edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q)
    (b : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    (∫ x in _root_.Metric.ball b R, ‖fderiv ℝ (fun y => P (diskExtension u (e y))) x‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 * ∫ z in _root_.Metric.ball (e b) R, diskMapEnergyDensity g (diskExtension u) z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let f : ℂ → ℝ := P ∘ diskExtension u
  have hU := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzWith (K * L) f := by
    intro z w
    exact (hP _ _).trans ((mul_le_mul_right (hU z w) (K : ℝ≥0∞)).trans_eq (by
      rw [ENNReal.coe_mul, mul_assoc]))
  have hfm (ξ : ℂ) : _root_.MeasureTheory.MemLp (fderiv ℝ f) 2 (volume.restrict (_root_.Metric.ball ξ R)) := by
    let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Metric.ball ξ R)) :=
      isFiniteMeasure_restrict.mpr _root_.MeasureTheory.measure_ball_ne_top
    exact MemLp.of_bound (measurable_fderiv ℝ f).aestronglyMeasurable (K * L : ℝ≥0)
      (Eventually.of_forall fun z => norm_fderiv_le_of_lipschitz ℝ hf)
  have hintr : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (_root_.Metric.ball (e b) R) := by
    let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Metric.ball (e b) R)) :=
      isFiniteMeasure_restrict.mpr _root_.MeasureTheory.measure_ball_ne_top
    exact integrableOn_diskMapEnergyDensity_of_lipschitz g hU _
  have hae := ae_fderiv_partials_sq_le_mul_diskMapEnergyDensity g hU (fun z w => hP _ _)
  have hnorm (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
    change ‖fderiv ℝ (f ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ f (e x)).opNorm_comp_linearIsometryEquiv e
  have hpre : e ⁻¹' _root_.Metric.ball (e b) R = _root_.Metric.ball b R := by
    ext x
    simp only [_root_.Set.mem_preimage, _root_.Metric.mem_ball, e.isometry.dist_eq]
  have hchange := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (fun z => ‖fderiv ℝ f z‖ ^ 2) (_root_.Metric.ball (e b) R)
  rw [hpre] at hchange
  change (∫ x in _root_.Metric.ball b R, ‖fderiv ℝ (f ∘ e) x‖ ^ 2) ≤ _
  simp_rw [hnorm]
  rw [hchange, ← _root_.MeasureTheory.integral_const_mul]
  apply _root_.MeasureTheory.integral_mono_ae (hfm (e b)).norm.integrable_sq (hintr.const_mul (2 * (K : ℝ) ^ 2))
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (s := _root_.Metric.ball (e b) R) hae] with z hz
  have hnormsq : ‖fderiv ℝ f z‖ ^ 2 =
      (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
    simpa [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two] using
      Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ f z)
  rwa [hnormsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball ``Submission.DifferentialGeometry.Geometry.integral_norm_fderiv_sq_comp_plane_le_mul_disk_energy_on_ball

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integral_fderiv_probe_sq_le_disk_energy_on_subset
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {P : M → ℝ} {L K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (hP : ∀ p q, _root_.EDist.edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : S ⊆ _root_.Metric.ball 0 1) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    (∫ x in S, ‖fderiv ℝ (fun y => P (diskExtension u (e y))) x‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 * ∫ z in e '' S, diskMapEnergyDensity g (diskExtension u) z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let f : ℂ → ℝ := P ∘ diskExtension u
  have hU := diskExtension_riemannian_lipschitz g hu
  have hf : LipschitzWith (K * L) f := by
    intro z w
    apply (hP _ _).trans
    rw [ENNReal.coe_mul, mul_assoc]
    exact mul_le_mul' le_rfl (hU z w)
  have hsub : e '' S ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hS hx
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, e.norm_map] using (mem_ball_zero_iff.mp hh).le
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (e '' S)) := isFiniteMeasure_restrict.mpr
    ((_root_.MeasureTheory.measure_mono hsub).trans_lt (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_lt_top).ne
  have hfm : _root_.MeasureTheory.MemLp (fderiv ℝ f) 2 (volume.restrict (e '' S)) :=
    MemLp.of_bound (measurable_fderiv ℝ f).aestronglyMeasurable (K * L : ℝ≥0)
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hf)
  have hintr := (integrable_diskMapEnergyDensity g hu).mono_set hsub
  have hae := ae_fderiv_partials_sq_le_mul_diskMapEnergyDensity g hU (fun z w => hP _ _)
  have hnorm (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
    change ‖fderiv ℝ (f ∘ (e.toContinuousLinearEquiv : _ → _)) x‖ = _
    rw [e.toContinuousLinearEquiv.comp_right_fderiv]
    exact (fderiv ℝ f (e x)).opNorm_comp_linearIsometryEquiv e
  have hpre : e ⁻¹' (e '' S) = S := _root_.Set.preimage_image_eq _ e.injective
  have hchange := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (fun z => ‖fderiv ℝ f z‖ ^ 2) (e '' S)
  rw [hpre] at hchange
  change (∫ x in S, ‖fderiv ℝ (f ∘ e) x‖ ^ 2) ≤ _
  simp_rw [hnorm]
  rw [hchange, ← _root_.MeasureTheory.integral_const_mul]
  apply _root_.MeasureTheory.integral_mono_ae hfm.norm.integrable_sq (hintr.const_mul (2 * (K : ℝ) ^ 2))
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (s := e '' S) hae] with z hz
  have hnormsq : ‖fderiv ℝ f z‖ ^ 2 =
      (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
    simpa [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two] using
      Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ f z)
  rwa [hnormsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_fderiv_probe_sq_le_disk_energy_on_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_fderiv_probe_sq_le_disk_energy_on_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_fderiv_probe_sq_le_disk_energy_on_subset ``Submission.DifferentialGeometry.Geometry.integral_fderiv_probe_sq_le_disk_energy_on_subset

theorem integral_weakGrad_probe_sq_le_limsup_energy_on_subset
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {P : M → ℝ}
    (hP : Continuous P) {D : ℝ} (hD : ∀ p, ‖P p‖ ≤ D) {K : ℝ≥0}
    (hPLip : ∀ p q, _root_.EDist.edist (P p) (P q) ≤ (K : ℝ≥0∞) * riemannianEDistOf g p q)
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {B : ℝ}
    (hLip : ∀ n, ∃ L : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (_root_.Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => diskExtension (u n) z) _root_.Filter.atTop (𝓝 (v z)))
    (henergy : ∀ n, riemannianDiskEnergy g (u n) ≤ B)
    (hw : DeGiorgi.MemW1pWitness 2
      (fun x => P (v (Complex.orthonormalBasisOneI.repr.symm x))) (_root_.Metric.ball 0 1))
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hSo : IsOpen S) (hS : S ⊆ _root_.Metric.ball 0 1) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    (∫ x in S, ‖hw.weakGrad x‖ ^ 2) ≤
      2 * (K : ℝ) ^ 2 * _root_.Filter.limsup (fun n => ∫ z in e '' S,
        diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun n x => P (diskExtension (u n) (e x))
  let q : ℕ → ℝ := fun n => ∫ x in S, ‖fderiv ℝ (f n) x‖ ^ 2
  let a : ℕ → ℝ := fun n => ∫ z in e '' S, diskMapEnergyDensity g (diskExtension (u n)) z
  let C : ℝ := 2 * (K : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLipe (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (f n) := by
    obtain ⟨L, hL⟩ := hLip n
    refine ⟨K * L, ?_⟩
    intro x y
    apply (hPLip _ _).trans
    have hh := diskExtension_riemannian_lipschitz g hL (e x) (e y)
    rw [e.isometry.edist_eq] at hh
    simpa only [ENNReal.coe_mul, mul_assoc] using mul_le_mul' (le_refl (K : ℝ≥0∞)) hh
  have hpre : e ⁻¹' _root_.Metric.ball (0 : ℂ) 1 = _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [_root_.Set.mem_preimage, mem_ball_zero_iff, e.norm_map]
  have he := e.measurePreserving.restrict_preimage (s := _root_.Metric.ball (0 : ℂ) 1) measurableSet_ball
  rw [hpre] at he
  have haee := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hS (he.quasiMeasurePreserving.ae hae)
  have hsub : e '' S ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, e.norm_map] using (mem_ball_zero_iff.mp (hS hx)).le
  have ha0 (n : ℕ) : 0 ≤ a n := _root_.MeasureTheory.integral_nonneg fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have haB (n : ℕ) : a n ≤ B := by
    obtain ⟨L, hL⟩ := hLip n
    exact (_root_.MeasureTheory.setIntegral_mono_set (integrable_diskMapEnergyDensity g hL)
      (Eventually.of_forall fun z => div_nonneg
        (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
          (by norm_num)) (Eventually.of_forall hsub)).trans (henergy n)
  have hlocal (n : ℕ) : q n ≤ C * a n := by
    obtain ⟨L, hL⟩ := hLip n
    exact integral_fderiv_probe_sq_le_disk_energy_on_subset g (u n) hL hPLip hS
  have hqB (n : ℕ) : q n ≤ C * B :=
    (hlocal n).trans (mul_le_mul_of_nonneg_left (haB n) hC)
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    ((_root_.MeasureTheory.measure_mono (hS.trans _root_.Metric.ball_subset_closedBall)).trans_lt
      (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).measure_lt_top).ne
  have hls := Analysis.Sobolev.Euclidean.integral_weakGrad_sq_le_liminf_comp_fderiv_on_subset
    hSo hS hP hD (fun n x => diskExtension (u n) (e x)) (fun x => v (e x))
    hLipe haee hqB hw
  have hq0 (n : ℕ) : 0 ≤ q n := _root_.MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hqlo : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop q :=
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall hq0)
  have hqhi : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop q :=
    _root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall hqB)
  have hahi : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop a :=
    _root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall haB)
  have hcahi : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (fun n => C * a n) :=
    _root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      mul_le_mul_of_nonneg_left (haB n) hC)
  have hmul := limsup_mul_le
    ((Eventually.of_forall fun _ : ℕ => hC).frequently)
    (show _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (fun _ : ℕ => C) from
      (tendsto_const_nhds (x := C)).isBoundedUnder_le)
    (Eventually.of_forall ha0) hahi
  have hcle : _root_.Filter.limsup (fun n => C * a n) _root_.Filter.atTop ≤ C * _root_.Filter.limsup a atTop := by
    simpa only [Pi.mul_def, _root_.Filter.limsup_const] using hmul
  exact hls.trans ((_root_.Filter.liminf_le_limsup hqhi hqlo).trans
    ((_root_.Filter.limsup_le_limsup (Eventually.of_forall hlocal) hqlo.isCoboundedUnder_le hcahi).trans hcle))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_weakGrad_probe_sq_le_limsup_energy_on_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_weakGrad_probe_sq_le_limsup_energy_on_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_weakGrad_probe_sq_le_limsup_energy_on_subset ``Submission.DifferentialGeometry.Geometry.integral_weakGrad_probe_sq_le_limsup_energy_on_subset

end DifferentialGeometry.Geometry

end

end
