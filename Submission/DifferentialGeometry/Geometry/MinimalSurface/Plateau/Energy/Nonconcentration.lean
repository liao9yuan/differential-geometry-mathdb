import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalDefect
import Submission.DifferentialGeometry.Analysis.Asymptotics.SmallDrop

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

private theorem integral_annulus_eq_sub_closedBall
    {f : ℂ → ℝ} {b : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (hf : _root_.MeasureTheory.IntegrableOn f (_root_.Metric.closedBall b R)) :
    (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc r R}, f z) =
      (∫ z in _root_.Metric.closedBall b R, f z) - ∫ z in _root_.Metric.closedBall b r, f z := by
  have heq : {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc r R} =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      closedBall b R \ _root_.Metric.closedBall b r := by
    filter_upwards [(_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume b r)]
      with z hz
    have hne : _root_.Dist.dist z b ≠ r := by simpa only [_root_.Metric.mem_sphere] using hz
    apply propext
    change (r ≤ _root_.Dist.dist z b ∧ _root_.Dist.dist z b ≤ R) ↔ (_root_.Dist.dist z b ≤ R ∧ ¬ _root_.Dist.dist z b ≤ r)
    constructor
    · rintro ⟨hr, hR⟩
      exact ⟨hR, not_le.mpr (lt_of_le_of_ne hr (Ne.symm hne))⟩
    · rintro ⟨hR, hr⟩
      exact ⟨(lt_of_not_ge hr).le, hR⟩
  rw [_root_.MeasureTheory.setIntegral_congr_set heq]
  exact _root_.MeasureTheory.setIntegral_sdiff measurableSet_closedBall hf (_root_.Metric.closedBall_subset_closedBall hrR)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_annulus_eq_sub_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_annulus_eq_sub_closedBall target :: scope.openDecls } }

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_dyadic_radius_energy_le_add_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (γ : freeLoop M) (u : C(closedDisk, M)), u ∈ weaklyMonotoneDiskCompetitors g γ →
        riemannianDiskEnergy g u ≤ B →
        ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 →
        (∫ z in _root_.Metric.closedBall b (R / 2 ^ N), diskMapEnergyDensity g (diskExtension u) z) ≤
          η + (riemannianDiskEnergy g u -
            _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
              weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ :=
    exists_local_energy_bound_by_annulus_add_minimizing_defect g hregular
  obtain ⟨N, hN, hcontrol⟩ := Analysis.exists_uniform_index_energy_le_of_small_drop
    (ε := ε / (8 * Real.pi)) (C := C * (8 * Real.pi))
    (by positivity) (by positivity) hB hη
  refine ⟨N, hN, ?_⟩
  intro γ u hu htotal b R hR hbr
  let rad : ℕ → ℝ := fun k => R / 2 ^ k
  let e : ℕ → ℝ := fun k => ∫ z in _root_.Metric.closedBall b (rad k),
    diskMapEnergyDensity g (diskExtension u) z
  let δ := riemannianDiskEnergy g u -
    _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
  have hradpos (k : ℕ) : 0 < rad k := div_pos hR (by positivity)
  have hradstep (k : ℕ) : rad (k + 1) = rad k / 2 := by
    simp only [rad, pow_succ, div_mul_eq_div_div]
  have hradanti : Antitone rad := by
    intro i j hij
    exact div_le_div_of_nonneg_left hR.le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)
  have hradle (k : ℕ) : rad k ≤ R := by
    simpa only [rad, pow_zero, div_one] using hradanti (Nat.zero_le k)
  have hball (k : ℕ) : _root_.Metric.closedBall b (rad k) ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ _root_.Dist.dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    have hd := mem_closedBall.mp hz
    have hk := hradle k
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have hi (k : ℕ) := (weaklyMonotoneDiskCompetitor_integrable_energy g hu).mono_set (hball k)
  have hn (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have he0 (k : ℕ) : 0 ≤ e k := _root_.MeasureTheory.integral_nonneg hn
  have heanti : Antitone e := by
    intro i j hij
    exact _root_.MeasureTheory.setIntegral_mono_set (hi i) (Eventually.of_forall hn)
      (Eventually.of_forall (_root_.Metric.closedBall_subset_closedBall (hradanti hij)))
  have hetotal : e 0 ≤ B := by
    exact (_root_.MeasureTheory.setIntegral_mono_set (weaklyMonotoneDiskCompetitor_integrable_energy g hu)
      (Eventually.of_forall hn) (Eventually.of_forall (hball 0))).trans htotal
  have hsmall (j : ℕ) (hj : e j - e (j + 1) < ε / (8 * Real.pi)) :
      e (j + 1) ≤ C * (8 * Real.pi) * (e j - e (j + 1)) + δ := by
    have hjpos := hradpos j
    have hjR := hradle j
    have hradlt : rad (j + 1) < rad j := by rw [hradstep]; linarith
    have hfactor : 4 * Real.pi * rad j / (rad j - rad (j + 1)) = 8 * Real.pi := by
      rw [hradstep]
      field_simp
      ring
    have hann : (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc (rad (j + 1)) (rad j)},
        diskMapEnergyDensity g (diskExtension u) z) = e j - e (j + 1) :=
      integral_annulus_eq_sub_closedBall hradlt.le (hi j)
    have h := hbound γ u hu b (rad (j + 1)) (rad j) (hradpos _) hradlt
      (by linarith) (by
        rw [hfactor, hann]
        exact (by simpa only [mul_comm] using
          (lt_div_iff₀ (by positivity : 0 < 8 * Real.pi)).mp hj))
    rw [hfactor, hann] at h
    exact h
  exact hcontrol e δ heanti he0 hetotal hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_dyadic_radius_energy_le_add_minimizing_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_dyadic_radius_energy_le_add_minimizing_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_dyadic_radius_energy_le_add_minimizing_defect ``Submission.DifferentialGeometry.Geometry.exists_dyadic_radius_energy_le_add_minimizing_defect

end DifferentialGeometry.Geometry

end

end

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

theorem exists_eventually_uniform_small_ball_energy_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ)))) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ n in _root_.Filter.atTop,
      ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 →
        (∫ z in _root_.Metric.closedBall b (R / 2 ^ N), diskMapEnergyDensity g (diskExtension (u n)) z) ≤ η := by
  obtain ⟨B, hB⟩ := hmin.isBoundedUnder_le.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (_root_.Set.mem_range_self n)
  have hB0 : 0 ≤ B := (riemannianDiskEnergy_nonneg g (u 0)).trans (htotal 0)
  obtain ⟨N, hN, hsmall⟩ := exists_dyadic_radius_energy_le_add_minimizing_defect
    g hregular hB0 (half_pos hη)
  let infimum := _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
    weaklyMonotoneDiskCompetitors g γ)
  have hδ : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n) - infimum) _root_.Filter.atTop (𝓝 0) := by
    simpa only [infimum, sub_self] using hmin.sub_const infimum
  refine ⟨N, hN, ?_⟩
  filter_upwards [hδ.eventually_le_const (half_pos hη)] with n hn
  intro b R hR hbr
  have h := hsmall γ (u n) (hu n) (htotal n) b R hR hbr
  exact h.trans (by dsimp only [infimum] at hn; linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_eventually_uniform_small_ball_energy_of_minimizing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_eventually_uniform_small_ball_energy_of_minimizing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_eventually_uniform_small_ball_energy_of_minimizing_sequence ``Submission.DifferentialGeometry.Geometry.exists_eventually_uniform_small_ball_energy_of_minimizing_sequence

end DifferentialGeometry.Geometry

end

end
