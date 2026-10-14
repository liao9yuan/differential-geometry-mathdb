import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Composition
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Retraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Metric _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

section Retraction

variable [T3Space M]

theorem diskMapEnergyDensity_ae_eq_pullback_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y) :
    diskMapEnergyDensity g u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun z =>
      (pullbackMetricCoefficients g r (Φ (u z))
          (fderiv ℝ (Φ ∘ u) z 1) (fderiv ℝ (Φ ∘ u) z 1) +
        pullbackMetricCoefficients g r (Φ (u z))
          (fderiv ℝ (Φ ∘ u) z Complex.I) (fderiv ℝ (Φ ∘ u) z Complex.I)) / 2 := by
  filter_upwards [ae_mdifferentiableAt_of_riemannian_lipschitz g hu] with z hz
  have hΦz : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) Φ (u z) :=
    hΦ.mdifferentiableAt one_ne_zero
  have hrz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) r (Φ (u z)) :=
    ((hr (Φ (u z)) (hΦN (_root_.Set.mem_range_self (u z)))).contMDiffAt
      (hN.mem_nhds (hΦN (_root_.Set.mem_range_self (u z))))).mdifferentiableAt one_ne_zero
  rw [pullbackMetricCoefficients_comp_fderiv_of_leftInverse g hΦz hrz hleft hz,
    pullbackMetricCoefficients_comp_fderiv_of_leftInverse g hΦz hrz hleft hz]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapEnergyDensity_ae_eq_pullback_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapEnergyDensity_ae_eq_pullback_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapEnergyDensity_ae_eq_pullback_of_lipschitz ``Submission.DifferentialGeometry.Geometry.diskMapEnergyDensity_ae_eq_pullback_of_lipschitz

end Retraction

variable [T2Space M] [CompactSpace M] [CompleteSpace F]

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
      ∀ (S : Set ℂ), S ⊆ _root_.Metric.closedBall (0 : ℂ) 1 →
        _root_.MeasureTheory.IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S ∧
        _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) S ∧
        (∫ z in S, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 * ∫ z in S, diskMapEnergyDensity g (diskExtension u) z := by
  obtain ⟨C, hC, hpoint⟩ := exists_lipschitzWith_comp_and_ae_norm_fderiv_sq_le g hΦ
  refine ⟨C, hC, fun u K hu => ?_⟩
  obtain ⟨hLip, hpointu⟩ := hpoint (diskExtension u) K (diskExtension_riemannian_lipschitz g hu)
  refine ⟨hLip, fun S hSD => ?_⟩
  have he : _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) S :=
    (integrable_diskMapEnergyDensity g hu).mono_set hSD
  have hi : _root_.MeasureTheory.IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S := by
    apply (he.const_mul (4 * (C : ℝ) ^ 2)).mono'
      ((measurable_fderiv ℝ (Φ ∘ diskExtension u)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (s := S) hpointu] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hi, he, ?_⟩
  simpa only [_root_.MeasureTheory.integral_const_mul] using
    _root_.MeasureTheory.integral_mono_ae hi (he.const_mul (4 * (C : ℝ) ^ 2)) (_root_.MeasureTheory.ae_restrict_of_ae hpointu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets ``Submission.DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets

theorem exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) 1 r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : closedDisk → M) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * _root_.EDist.edist x y) →
      LipschitzWith (C * K) (Φ ∘ diskExtension u) ∧
      ∀ (S : Set ℂ), S ⊆ _root_.Metric.closedBall (0 : ℂ) 1 →
        let e : ℂ → ℝ := fun z =>
          (pullbackMetricCoefficients g r (Φ (diskExtension u z))
              (fderiv ℝ (Φ ∘ diskExtension u) z 1) (fderiv ℝ (Φ ∘ diskExtension u) z 1) +
            pullbackMetricCoefficients g r (Φ (diskExtension u z))
              (fderiv ℝ (Φ ∘ diskExtension u) z Complex.I)
              (fderiv ℝ (Φ ∘ diskExtension u) z Complex.I)) / 2
        _root_.MeasureTheory.IntegrableOn (fun z => ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) S ∧
        _root_.MeasureTheory.IntegrableOn e S ∧
        (∫ z in S, diskMapEnergyDensity g (diskExtension u) z) = (∫ z in S, e z) ∧
        (∫ z in S, ‖fderiv ℝ (Φ ∘ diskExtension u) z‖ ^ 2) ≤
          4 * (C : ℝ) ^ 2 * ∫ z in S, e z := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets g hΦ
  refine ⟨C, hC, fun u K hu => ⟨(hbound u K hu).1, fun S hSD => ?_⟩⟩
  obtain ⟨hi, he, hle⟩ := (hbound u K hu).2 S hSD
  have heq := _root_.MeasureTheory.ae_restrict_of_ae (s := S)
    (diskMapEnergyDensity_ae_eq_pullback_of_lipschitz g hΦ hN hr hΦN hleft
      (diskExtension_riemannian_lipschitz g hu))
  have hint := _root_.MeasureTheory.integral_congr_ae heq
  exact ⟨hi, he.congr heq, hint, hle.trans_eq (congrArg (fun x => 4 * (C : ℝ) ^ 2 * x) hint)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets ``Submission.DifferentialGeometry.Geometry.exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets

end DifferentialGeometry.Geometry

end
