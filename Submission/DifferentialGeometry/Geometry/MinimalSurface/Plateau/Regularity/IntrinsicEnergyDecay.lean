import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Nonconcentration
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalDefect
import Submission.DifferentialGeometry.Analysis.Asymptotics.AffineContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_eventually_dyadic_energy_bound_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)))) :
    ∃ (N : ℕ) (B θ : ℝ), 0 < N ∧ 0 < B ∧ 0 < θ ∧ θ < 1 ∧
      ∀ᶠ n in _root_.Filter.atTop, ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
        (∫ z in _root_.Metric.closedBall b (R / 2 ^ (N + k)),
          diskMapEnergyDensity g (diskExtension (u n)) z) ≤
          θ ^ k * B + (1 - θ ^ k) *
            (riemannianDiskEnergy g (u n) -
              _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
                weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε, θ, hε, hθ, hθ1, hcontract⟩ :=
    exists_local_energy_contraction_with_minimizing_defect g hregular
  obtain ⟨N, hN, hevent⟩ := exists_eventually_uniform_small_ball_energy_of_minimizing_sequence
    g hregular γ u hu hmin (half_pos hε)
  refine ⟨N, ε / 2, θ, hN, half_pos hε, hθ, hθ1, ?_⟩
  filter_upwards [hevent] with n hn
  intro b R hR hbr k
  let r : ℝ := R / 2 ^ N
  let e : ℕ → ℝ := fun j => ∫ z in _root_.Metric.closedBall b (r / 2 ^ j),
    diskMapEnergyDensity g (diskExtension (u n)) z
  let δ : ℝ := riemannianDiskEnergy g (u n) -
    _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
  have hr : 0 < r := div_pos hR (by positivity)
  have hrR : r ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hball : _root_.Metric.closedBall b r ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ _root_.Dist.dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    have hd := mem_closedBall.mp hz
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have hi := (weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)).mono_set hball
  have hnonneg (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension (u n)) z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have he0 : e 0 ≤ ε / 2 := by simpa only [e, pow_zero, div_one] using hn b R hR hbr
  have hjr (j : ℕ) : r / 2 ^ j ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
  have hstep (j : ℕ) : e (j + 1) ≤ θ * e j + (1 - θ) * δ := by
    have hjpos : 0 < r / 2 ^ j := div_pos hr (by positivity)
    have hjle := hjr j
    have hsmall : e j < ε := by
      have hmono : e j ≤ e 0 := by
        dsimp only [e]
        rw [pow_zero, div_one]
        exact _root_.MeasureTheory.setIntegral_mono_set hi (Eventually.of_forall hnonneg)
          (Eventually.of_forall (_root_.Metric.closedBall_subset_closedBall hjle))
      exact hmono.trans_lt (he0.trans_lt (half_lt_self hε))
    have h := hcontract γ (u n) (hu n) b (r / 2 ^ j) hjpos (by linarith) hsmall
    simpa only [e, pow_succ, div_mul_eq_div_div] using h
  have h := Analysis.le_pow_mul_add_defect_of_affine_contraction hθ.le hstep k
  have heq : r / 2 ^ k = R / 2 ^ (N + k) := by
    rw [pow_add, div_mul_eq_div_div]
  rw [← heq]
  change e k ≤ _
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_left he0 (pow_nonneg hθ.le k)) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_eventually_dyadic_energy_bound_of_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_eventually_dyadic_energy_bound_of_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_eventually_dyadic_energy_bound_of_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_eventually_dyadic_energy_bound_of_minimizing_sequence

end DifferentialGeometry.Geometry

end

end
