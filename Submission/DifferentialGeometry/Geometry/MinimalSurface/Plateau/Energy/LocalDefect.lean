import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicReplacement
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicPolar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_local_replacement_energy_comparison
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (γ : freeLoop M) (u : C(closedDisk, M)), u ∈ weaklyMonotoneDiskCompetitors g γ →
        ∀ (b : ℂ) (r : ℝ), 0 < r → ‖b‖ + r < 1 →
        let β : ℝ → M := fun s => diskExtension u
          (b + r • circleMap 0 1 (2 * Real.pi * s - Real.pi))
        _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g β t) ^ 2) (_root_.Set.Icc 0 1) →
        (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g β t) ^ 2) < ε →
        ∃ v : C(closedDisk, M), v ∈ weaklyMonotoneDiskCompetitors g γ ∧
          diskTrace v = diskTrace u ∧
          (∀ z : closedDisk, r ≤ _root_.Dist.dist (z : ℂ) b → v z = u z) ∧
          (∀ z : closedDisk, _root_.Dist.dist (z : ℂ) b ≤ r / 2 →
            v z = diskExtension u (b + r • circleMap 0 1 (-Real.pi))) ∧
          riemannianDiskEnergy g v ≤ riemannianDiskEnergy g u -
            (∫ z in _root_.Metric.closedBall b r, diskMapEnergyDensity g (diskExtension u) z) +
              C * ∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g β t) ^ 2 := by
  obtain ⟨ε, C, hε, hC, hfill⟩ :=
    exists_uniform_disk_filling_of_intrinsic_boundary_energy_lt g hregular
  refine ⟨ε, C, hε, hC, ?_⟩
  intro γ u hu b r hr hbr β henergy hsmall
  obtain ⟨K, hK⟩ := hu.2
  let U : ℂ → M := fun z => diskExtension u (b + r • z)
  have ha : LipschitzWith (Real.nnabs r) (fun z : ℂ => b + r • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_eq_abs, Real.coe_nnabs, le_refl]
  have hU : ∀ z z', riemannianEDistOf g (U z) (U z') ≤
      ((K * Real.nnabs r : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist z z' := by
    intro z z'
    exact (diskExtension_riemannian_lipschitz g hK (b + r • z) (b + r • z')).trans
      ((mul_le_mul_right (ha z z') (K : ℝ≥0∞)).trans_eq (by rw [ENNReal.coe_mul, mul_assoc]))
  obtain ⟨w, ⟨L, hw⟩, htrace, hinner, _, _, _, hbound⟩ :=
    hfill U (K * Real.nnabs r) hU henergy hsmall
  obtain ⟨v, hv, hvt, hvo, hvi, he⟩ :=
    exists_disk_replacement_from_unit_filling g hu w hw hr hbr htrace
  refine ⟨v, hv, hvt, hvo, ?_, ?_⟩
  · intro z hz
    have hzr : _root_.Dist.dist (z : ℂ) b ≤ r := hz.trans (by linarith)
    rw [hvi z hzr]
    have hnorm : ‖r⁻¹ • ((z : ℂ) - b)‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm]
      have h := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hr.le)
      simpa only [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] using h
    let q : closedDisk := ⟨r⁻¹ • ((z : ℂ) - b),
      mem_closedBall.mpr (by simpa only [dist_zero_right] using hnorm.trans (by norm_num))⟩
    exact (diskExtension_coe w q).trans (hinner q hnorm)
  · rw [he]
    exact add_le_add_right hbound _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_local_replacement_energy_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_local_replacement_energy_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_local_replacement_energy_comparison ``Submission.DifferentialGeometry.Geometry.exists_uniform_local_replacement_energy_comparison

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_local_energy_bound_with_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (γ : freeLoop M) (u : C(closedDisk, M)), u ∈ weaklyMonotoneDiskCompetitors g γ →
        ∀ (b : ℂ) (r : ℝ), 0 < r → ‖b‖ + r < 1 →
        let β : ℝ → M := fun s => diskExtension u
          (b + r • circleMap 0 1 (2 * Real.pi * s - Real.pi))
        _root_.MeasureTheory.IntegrableOn (fun t => (riemannianCurveSpeed g β t) ^ 2) (_root_.Set.Icc 0 1) →
        (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g β t) ^ 2) < ε →
        (∫ z in _root_.Metric.closedBall b r, diskMapEnergyDensity g (diskExtension u) z) ≤
          C * (∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g β t) ^ 2) +
            (riemannianDiskEnergy g u -
              _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
                weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε, C, hε, hC, hreplace⟩ := exists_uniform_local_replacement_energy_comparison g hregular
  refine ⟨ε, C, hε, hC, ?_⟩
  intro γ u hu b r hr hbr β henergy hsmall
  obtain ⟨v, hv, _, _, _, hbound⟩ := hreplace γ u hu b r hr hbr henergy hsmall
  have hbounded : BddBelow ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro e ⟨w, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g w
  have hle := csInf_le hbounded (_root_.Set.mem_image_of_mem (fun w : C(closedDisk, M) =>
    riemannianDiskEnergy g w) hv)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_local_energy_bound_with_minimizing_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_local_energy_bound_with_minimizing_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_local_energy_bound_with_minimizing_defect ``Submission.DifferentialGeometry.Geometry.exists_uniform_local_energy_bound_with_minimizing_defect

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_local_energy_bound_by_annulus_add_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (γ : freeLoop M) (u : C(closedDisk, M)), u ∈ weaklyMonotoneDiskCompetitors g γ →
        ∀ (b : ℂ) (r R : ℝ), 0 < r → r < R → ‖b‖ + R < 1 →
        (4 * Real.pi * R / (R - r)) *
          (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc r R}, diskMapEnergyDensity g (diskExtension u) z) < ε →
        (∫ z in _root_.Metric.closedBall b r, diskMapEnergyDensity g (diskExtension u) z) ≤
          C * (4 * Real.pi * R / (R - r)) *
            (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc r R}, diskMapEnergyDensity g (diskExtension u) z) +
              (riemannianDiskEnergy g u -
                _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
                  weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε, C, hε, hC, hlocal⟩ :=
    exists_uniform_local_energy_bound_with_minimizing_defect g hregular
  refine ⟨ε, C, hε, hC, ?_⟩
  intro γ u hu b r R hr hrR hbr hsmall
  obtain ⟨K, hK⟩ := hu.2
  obtain ⟨ρ, hρ, hint, hD⟩ := exists_radius_circle_energy_le_annular_disk_energy_at
    g (diskExtension_riemannian_lipschitz g hK) b hr hrR
  have hlocalρ := hlocal γ u hu b ρ (hr.trans_le hρ.1) (by linarith [hρ.2]) hint
    (hD.trans_lt hsmall)
  have hball : _root_.Metric.closedBall b R ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ _root_.Dist.dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    have hd := mem_closedBall.mp hz
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have hi := (weaklyMonotoneDiskCompetitor_integrable_energy g hu).mono_set
    ((_root_.Metric.closedBall_subset_closedBall hρ.2).trans hball)
  have hnonneg (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have hle := _root_.MeasureTheory.setIntegral_mono_set hi (Eventually.of_forall hnonneg)
    (Eventually.of_forall (_root_.Metric.closedBall_subset_closedBall hρ.1))
  apply hle.trans (hlocalρ.trans ?_)
  simpa only [mul_assoc] using add_le_add_left (mul_le_mul_of_nonneg_left hD hC.le)
    (riemannianDiskEnergy g u - _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w)
      '' weaklyMonotoneDiskCompetitors g γ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_local_energy_bound_by_annulus_add_minimizing_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_local_energy_bound_by_annulus_add_minimizing_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_local_energy_bound_by_annulus_add_minimizing_defect ``Submission.DifferentialGeometry.Geometry.exists_local_energy_bound_by_annulus_add_minimizing_defect

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

private theorem integral_annular_energy_eq_sub
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
  let target := ``Submission.DifferentialGeometry.Geometry.integral_annular_energy_eq_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_annular_energy_eq_sub target :: scope.openDecls } }

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_local_energy_contraction_with_minimizing_defect
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g) :
    ∃ ε θ : ℝ, 0 < ε ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (γ : freeLoop M) (u : C(closedDisk, M)), u ∈ weaklyMonotoneDiskCompetitors g γ →
        ∀ (b : ℂ) (R : ℝ), 0 < R → ‖b‖ + R < 1 →
        (∫ z in _root_.Metric.closedBall b R, diskMapEnergyDensity g (diskExtension u) z) < ε →
        (∫ z in _root_.Metric.closedBall b (R / 2), diskMapEnergyDensity g (diskExtension u) z) ≤
          θ * (∫ z in _root_.Metric.closedBall b R, diskMapEnergyDensity g (diskExtension u) z) +
            (1 - θ) * (riemannianDiskEnergy g u -
              _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
                weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε₀, C, hε₀, hC, hbound⟩ :=
    exists_local_energy_bound_by_annulus_add_minimizing_defect g hregular
  let k : ℝ := C * (8 * Real.pi)
  have hk : 0 < k := mul_pos hC (by positivity)
  let θ : ℝ := k / (1 + k)
  have hden : 0 < 1 + k := by linarith
  have hθ : 0 < θ := div_pos hk hden
  have hθ1 : θ < 1 := (div_lt_one hden).mpr (by linarith)
  refine ⟨ε₀ / (8 * Real.pi), θ, div_pos hε₀ (by positivity), hθ, hθ1, ?_⟩
  intro γ u hu b R hR hbr hsmall
  have hball : _root_.Metric.closedBall b R ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ _root_.Dist.dist z b + ‖b‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - b) b
    have hd := mem_closedBall.mp hz
    exact mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  have hi := (weaklyMonotoneDiskCompetitor_integrable_energy g hu).mono_set hball
  have hhalf : R / 2 ≤ R := by linarith
  have hfactor : 4 * Real.pi * R / (R - R / 2) = 8 * Real.pi := by
    field_simp
    ring
  have hnonneg (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have hannle : (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc (R / 2) R},
      diskMapEnergyDensity g (diskExtension u) z) ≤
        ∫ z in _root_.Metric.closedBall b R, diskMapEnergyDensity g (diskExtension u) z :=
    _root_.MeasureTheory.setIntegral_mono_set hi (Eventually.of_forall hnonneg)
      (Eventually.of_forall fun z hz => hz.2)
  have hsmallann : (4 * Real.pi * R / (R - R / 2)) *
      (∫ z in {z : ℂ | _root_.Dist.dist z b ∈ _root_.Set.Icc (R / 2) R},
        diskMapEnergyDensity g (diskExtension u) z) < ε₀ := by
    rw [hfactor]
    exact (mul_le_mul_of_nonneg_left hannle (by positivity)).trans_lt
      (by simpa only [mul_comm] using
        (lt_div_iff₀ (by positivity : 0 < 8 * Real.pi)).mp hsmall)
  have hle := hbound γ u hu b (R / 2) R (by positivity) (by linarith) hbr hsmallann
  rw [hfactor, integral_annular_energy_eq_sub hhalf hi] at hle
  have hscaled := (le_div_iff₀ hden).mpr (show
      (∫ z in _root_.Metric.closedBall b (R / 2), diskMapEnergyDensity g (diskExtension u) z) * (1 + k) ≤
        k * (∫ z in _root_.Metric.closedBall b R, diskMapEnergyDensity g (diskExtension u) z) +
          (riemannianDiskEnergy g u - _root_.InfSet.sInf
            ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) from by dsimp only [k]; nlinarith [hle])
  apply hscaled.trans_eq
  dsimp only [θ]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_local_energy_contraction_with_minimizing_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_local_energy_contraction_with_minimizing_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_local_energy_contraction_with_minimizing_defect ``Submission.DifferentialGeometry.Geometry.exists_local_energy_contraction_with_minimizing_defect

end DifferentialGeometry.Geometry

end

end
