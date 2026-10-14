import Submission.DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Interpolation.AnnulusEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℝ F]

theorem attachThinAnnulus_mapsTo_closedBall_of_convex
    {K : Set F} (hK : Convex ℝ K) {u v : ℂ → F} {R h : ℝ}
    (hh : 0 < h) (hhR : h < R)
    (hu : _root_.Set.MapsTo u (_root_.Metric.sphere (0 : ℂ) R) K)
    (hv : _root_.Set.MapsTo v (_root_.Metric.closedBall (0 : ℂ) R) K) :
    MapsTo (attachThinAnnulus u v id R h) (_root_.Metric.closedBall (0 : ℂ) R) K := by
  intro z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  by_cases hi : ‖z‖ ≤ R - h
  · rw [attachThinAnnulus_inner u v id R h hi]
    apply hv
    have ha := sub_pos.mpr hhR
    have hR := hh.trans hhR
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR ha)]
    exact (mul_le_mul_of_nonneg_left hi (div_nonneg hR.le ha.le)).trans_eq
      (div_mul_cancel₀ R ha.ne')
  · have hshell : R - h ≤ ‖z‖ ∧ ‖z‖ ≤ R := ⟨(lt_of_not_ge hi).le, hzR⟩
    rw [attachThinAnnulus_shell u v id hh hhR (fun _ _ => rfl) (fun _ _ => rfl) hshell]
    have hp : thinAnnulusProjection R z ∈ _root_.Metric.sphere (0 : ℂ) R := by
      simpa only [_root_.Metric.mem_sphere, dist_zero_right] using
        thinAnnulusProjection_norm (hh.trans hhR).le z
    have hθ := thinAnnulusParameter_mem_Icc hh hshell
    exact hK (hv (_root_.Metric.sphere_subset_closedBall hp)) (hu hp)
      (sub_nonneg.mpr hθ.2) hθ.1 (sub_add_cancel 1 _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.attachThinAnnulus_mapsTo_closedBall_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.attachThinAnnulus_mapsTo_closedBall_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.attachThinAnnulus_mapsTo_closedBall_of_convex ``Submission.DifferentialGeometry.Analysis.attachThinAnnulus_mapsTo_closedBall_of_convex

theorem integrableOn_quadratic_fderiv_of_lipschitz [FiniteDimensional ℝ F]
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f)
    {S : Set ℂ} (hS : IsCompact S) {K : Set F} (hK : IsCompact K)
    (hfK : _root_.Set.MapsTo f S K) (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    _root_.MeasureTheory.IntegrableOn (fun z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2) S := by
  borelize F
  let μ : _root_.MeasureTheory.Measure ℂ := volume.restrict S
  let : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  have hm (w : ℂ) : _root_.MeasureTheory.MemLp (fun z => fderiv ℝ f z w) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f w).aestronglyMeasurable
      ((L : ℝ) * ‖w‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ f z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg w))
  have hAc : ContinuousOn (fun z => A (f z)) S := hA.comp hf.continuous.continuousOn hfK
  have hAm (v w : F) : _root_.MeasureTheory.AEStronglyMeasurable (fun z => A (f z) v w) μ :=
    ((hAc.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hS.measurableSet
  have hnorm : ContinuousOn (fun x => ‖A x‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  have hAb : ∀ᵐ z ∂μ, ‖A (f z)‖ ≤ C := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hS.measurableSet] with z hz
    exact hC (_root_.Set.mem_image_of_mem (fun x => ‖A x‖) (hfK hz))
  exact ((integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
    hAm hAb (hm 1) (hm 1)).add
    (integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
      hAm hAb (hm Complex.I) (hm Complex.I))).div_const 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrableOn_quadratic_fderiv_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrableOn_quadratic_fderiv_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrableOn_quadratic_fderiv_of_lipschitz ``Submission.DifferentialGeometry.Analysis.integrableOn_quadratic_fderiv_of_lipschitz

end Normed

variable [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_convex_thin_annulus_tendsto_quadratic_energy
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {R : ℝ} (hR : 0 < R)
    (hgap : _root_.Filter.Tendsto (fun n => ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖v n (circleMap 0 R (2 * Real.pi * t - Real.pi)) -
        u n (circleMap 0 R (2 * Real.pi * t - Real.pi))‖ ^ 2) _root_.Filter.atTop (𝓝 0))
    {D : ℝ} (hder : ∀ n, (∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun t => v n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
        ‖deriv (fun t => u n (circleMap 0 R (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤ D)
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (huK : ∀ᶠ n in _root_.Filter.atTop, _root_.Set.MapsTo (u n) (_root_.Metric.sphere (0 : ℂ) R) K)
    (hvK : ∀ n, _root_.Set.MapsTo (v n) (_root_.Metric.closedBall (0 : ℂ) R) K) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0) ∧
      (∀ᶠ n in _root_.Filter.atTop, h n < R / 2 ∧
        (∃ C : ℝ≥0, LipschitzWith C (attachThinAnnulus (u n) (v n) id R (h n))) ∧
        _root_.Set.MapsTo (attachThinAnnulus (u n) (v n) id R (h n)) (_root_.Metric.closedBall (0 : ℂ) R) K) ∧
      (∀ n z, R ≤ ‖z‖ → attachThinAnnulus (u n) (v n) id R (h n) z = u n z) ∧
      ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
        _root_.Filter.Tendsto (fun n =>
          (∫ z in _root_.Metric.closedBall (0 : ℂ) R,
            (A (attachThinAnnulus (u n) (v n) id R (h n) z)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z 1)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z 1) +
              A (attachThinAnnulus (u n) (v n) id R (h n) z)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z Complex.I)
                (fderiv ℝ (attachThinAnnulus (u n) (v n) id R (h n)) z Complex.I)) / 2) -
          (∫ z in _root_.Metric.closedBall (0 : ℂ) R,
            (A (v n z) (fderiv ℝ (v n) z 1) (fderiv ℝ (v n) z 1) +
              A (v n z) (fderiv ℝ (v n) z Complex.I) (fderiv ℝ (v n) z Complex.I)) / 2))
          atTop (𝓝 0) := by
  obtain ⟨h, hh, hh0, hgood, houter, hnorm⟩ :=
    exists_width_tendsto_annulus_energy_attachThinAnnulus_zero u v Ku Kv hu hv
      (fun _ => R) hR (fun _ => ⟨le_rfl, le_rfl⟩) hgap hder id differentiable_id
      (L := 1) (by
        intro x
        rw [fderiv_id]
        exact ContinuousLinearMap.norm_id_le) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hmaps : ∀ᶠ n in _root_.Filter.atTop,
      MapsTo (attachThinAnnulus (u n) (v n) id R (h n)) (_root_.Metric.closedBall (0 : ℂ) R) K := by
    filter_upwards [hgood, huK] with n hn huKn
    exact attachThinAnnulus_mapsTo_closedBall_of_convex hKconv (hh n)
      (by linarith [hn.1]) huKn (hvK n)
  refine ⟨h, hh, hh0, hgood.and hmaps |>.mono (fun n hn =>
    ⟨hn.1.1, hn.1.2, hn.2⟩), houter, ?_⟩
  intro A hA
  let f (n : ℕ) := attachThinAnnulus (u n) (v n) id R (h n)
  let S (n : ℕ) := {z : ℂ | ‖z‖ ∈ _root_.Set.Icc (R - h n) R}
  let energy (w : ℂ → F) (z : ℂ) :=
    (A (w z) (fderiv ℝ w z 1) (fderiv ℝ w z 1) +
      A (w z) (fderiv ℝ w z Complex.I) (fderiv ℝ w z Complex.I)) / 2
  have hsub (n : ℕ) : S n ⊆ _root_.Metric.closedBall (0 : ℂ) R := fun z hz =>
    mem_closedBall_zero_iff.mpr hz.2
  have hcompact (n : ℕ) : IsCompact (S n) :=
    (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      (isClosed_Icc.preimage continuous_norm) (hsub n)
  have hquad : _root_.Filter.Tendsto (fun n => ∫ z in S n, energy (f n) z) _root_.Filter.atTop (𝓝 0) :=
    tendsto_integral_quadratic_fderiv_of_eventually_lipschitz f S hcompact hK A hA
      (by
        filter_upwards [hgood, hmaps] with n hn hnK
        exact ⟨hn.2, hnK.mono_left (hsub n)⟩) hnorm
  apply hquad.congr'
  filter_upwards [hgood, hmaps] with n hn hnK
  obtain ⟨C, hC⟩ := hn.2
  have hhR : h n < R := by linarith [hn.1]
  have hint := integrableOn_quadratic_fderiv_of_lipschitz hC
    (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) R) hK hnK A hA
  have heq := integral_quadratic_fderiv_attachThinAnnulus_closedBall
    A (u n) (v n) id (hh n) hhR (le_refl R) hint
  change (∫ z in _root_.Metric.closedBall (0 : ℂ) R, energy (f n) z) =
    (∫ z in _root_.Metric.closedBall (0 : ℂ) R, energy (v n) z) +
      (∫ z in _root_.Metric.closedBall (0 : ℂ) R \ _root_.Metric.closedBall (0 : ℂ) (R - h n), energy (f n) z) +
      ∫ z in _root_.Metric.closedBall (0 : ℂ) R \ _root_.Metric.closedBall (0 : ℂ) R, energy (u n) z at heq
  simp only [Set.sdiff_self, _root_.MeasureTheory.setIntegral_empty, add_zero] at heq
  have hsets : _root_.Metric.closedBall (0 : ℂ) R \ _root_.Metric.closedBall (0 : ℂ) (R - h n) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] S n := by
    have hnull : ∀ᵐ z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ), z ∉ _root_.Metric.sphere (0 : ℂ) (R - h n) := by
      rw [_root_.MeasureTheory.ae_iff]
      simpa only [_root_.Classical.not_not, Set.ofPred_mem_eq] using
        Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) (R - h n)
    filter_upwards [hnull] with z hz
    apply propext
    have hne : ‖z‖ ≠ R - h n := by simpa only [_root_.Metric.mem_sphere, dist_zero_right] using hz
    change (z ∈ _root_.Metric.closedBall (0 : ℂ) R ∧ z ∉ _root_.Metric.closedBall (0 : ℂ) (R - h n)) ↔
      (R - h n ≤ ‖z‖ ∧ ‖z‖ ≤ R)
    simp only [_root_.Metric.mem_closedBall, dist_zero_right, not_le]
    exact ⟨fun hz => ⟨hz.2.le, hz.1⟩,
      fun hz => ⟨hz.2, lt_of_le_of_ne hz.1 hne.symm⟩⟩
  have hshell : (∫ z in _root_.Metric.closedBall (0 : ℂ) R \ _root_.Metric.closedBall (0 : ℂ) (R - h n),
      energy (f n) z) = ∫ z in S n, energy (f n) z := _root_.MeasureTheory.setIntegral_congr_set hsets
  change (∫ z in S n, energy (f n) z) =
    (∫ z in _root_.Metric.closedBall (0 : ℂ) R, energy (f n) z) -
      ∫ z in _root_.Metric.closedBall (0 : ℂ) R, energy (v n) z
  rw [heq, hshell]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_convex_thin_annulus_tendsto_quadratic_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_convex_thin_annulus_tendsto_quadratic_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_convex_thin_annulus_tendsto_quadratic_energy ``Submission.DifferentialGeometry.Analysis.exists_convex_thin_annulus_tendsto_quadratic_energy

end DifferentialGeometry.Analysis

end

end
