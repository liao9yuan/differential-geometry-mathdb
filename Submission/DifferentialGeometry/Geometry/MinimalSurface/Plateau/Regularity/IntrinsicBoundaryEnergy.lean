import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicBoundaryCap
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicCrosscut

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {B ε R₀ : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hR₀ : 0 < R₀) :
    ∃ a ∈ _root_.Set.Ioo (0 : ℝ) (_root_.Min.min R₀ 1),
      ∀ (u : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * _root_.EDist.edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ψ (1 - Real.arccos (ρ / 2) / Real.pi) - ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      riemannianDiskEnergy g u ≤ B →
      (∫ z in boundaryLens a, diskMapEnergyDensity g (diskExtension u) z) ≤ ε +
        (riemannianDiskEnergy g u -
          _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε₀, C, hε₀, hC, hcap⟩ := exists_uniform_intrinsic_boundary_cap_energy_bound g γ hγ
  let κ := _root_.Min.min ε₀ (ε / (C + 1))
  have hκ : 0 < κ := lt_min hε₀ (by positivity)
  let b := _root_.Min.min R₀ 1 / 2
  have hb : 0 < b := half_pos (lt_min hR₀ zero_lt_one)
  have hb1 : b < 1 := by dsimp [b]; linarith [min_le_right R₀ (1 : ℝ)]
  have hbR : b < _root_.Min.min R₀ 1 := half_lt_self (lt_min hR₀ zero_lt_one)
  let H := 2 * Real.pi * B / κ + 1
  have hH : 0 < H := by dsimp [H]; positivity
  let a := b / Real.exp H
  have ha : 0 < a := div_pos hb (Real.exp_pos _)
  have hab : a < b := div_lt_self hb (Real.one_lt_exp_iff.mpr hH)
  have hlog : Real.log (b / a) = H := by
    have heq : b / a = Real.exp H := by dsimp [a]; field_simp
    rw [heq, Real.log_exp]
  have hratio : 2 * Real.pi * B / Real.log (b / a) < κ := by
    rw [hlog]
    apply (div_lt_iff₀ hH).mpr
    dsimp [H]
    field_simp
    nlinarith
  have hratio0 : 0 ≤ 2 * Real.pi * B / Real.log (b / a) := by rw [hlog]; positivity
  have hCratio : C * (2 * Real.pi * B / Real.log (b / a)) < ε := by
    have h₁ := mul_le_mul_of_nonneg_right (show C ≤ C + 1 by linarith) hratio0
    have h₂ := mul_lt_mul_of_pos_left hratio (show 0 < C + 1 by linarith)
    have h₃ : (C + 1) * κ ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (min_le_right ε₀ (ε / (C + 1)))
        (show 0 ≤ C + 1 by linarith)
      exact h.trans_eq (mul_div_cancel₀ ε (by positivity))
    exact h₁.trans_lt (h₂.trans_le h₃)
  refine ⟨a, ⟨ha, hab.trans hbR⟩, ?_⟩
  intro u L hu ψ hψ htrace hshort henergy
  have hU := diskExtension_riemannian_lipschitz g hu
  have hI := integrable_diskMapEnergyDensity g hu
  have hnonneg (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z := by
    unfold diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hmasked : (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc a b} ∩ _root_.Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension u) z) ≤ B :=
    (_root_.MeasureTheory.setIntegral_mono_set hI (Eventually.of_forall hnonneg)
      (Eventually.of_forall _root_.Set.inter_subset_right)).trans henergy
  obtain ⟨ρ, hρ, hρI, hρE⟩ := exists_radius_normalized_crosscut_riemannian_energy_le
    g hU ha hab (hb1.trans (by norm_num)) hmasked
  have hρ0 := ha.trans hρ.1
  have hρ1 := hρ.2.trans hb1
  have hestimate := hcap u L hu ψ hψ htrace ρ hρ0 hρ1 (hshort ρ hρ0 hρ1) hρI
    (hρE.trans (hratio.le.trans (min_le_left _ _)))
  have hsub : boundaryLens a ⊆ boundaryLens ρ := by
    intro z hz
    exact ⟨(_root_.Metric.closedBall_subset_closedBall hρ.1.le) hz.1, hz.2⟩
  have hmono : (∫ z in boundaryLens a, diskMapEnergyDensity g (diskExtension u) z) ≤
      ∫ z in boundaryLens ρ, diskMapEnergyDensity g (diskExtension u) z :=
    _root_.MeasureTheory.setIntegral_mono_set (hI.mono_set _root_.Set.inter_subset_right) (Eventually.of_forall hnonneg)
      (Eventually.of_forall hsub)
  have hEsmall := (mul_le_mul_of_nonneg_left hρE hC).trans_lt hCratio
  exact hmono.trans (hestimate.trans (add_le_add hEsmall.le le_rfl))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound ``Submission.DifferentialGeometry.Geometry.exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

private theorem integral_annulus_closedDisk_eq_boundaryLens_sdiff (f : ℂ → ℝ) (a b : ℝ) :
    (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc a b} ∩ _root_.Metric.closedBall (0 : ℂ) 1, f z) =
      ∫ z in boundaryLens b \ boundaryLens a, f z := by
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∉ _root_.Metric.sphere (-1 : ℂ) a := by
    rw [_root_.MeasureTheory.ae_iff]
    convert Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (-1 : ℂ) a using 1
    congr 1
    ext z
    simp only [_root_.Set.mem_ofPred_eq, _root_.Classical.not_not]
  apply _root_.MeasureTheory.setIntegral_congr_set
  filter_upwards [hzero] with z hz
  have hne : _root_.Dist.dist z (-1) ≠ a := hz
  apply propext
  change ((a ≤ _root_.Dist.dist z (-1) ∧ _root_.Dist.dist z (-1) ≤ b) ∧ _root_.Dist.dist z 0 ≤ 1) ↔
    ((_root_.Dist.dist z (-1) ≤ b ∧ _root_.Dist.dist z 0 ≤ 1) ∧ ¬ (_root_.Dist.dist z (-1) ≤ a ∧ _root_.Dist.dist z 0 ≤ 1))
  constructor
  · rintro ⟨⟨ha, hb⟩, hD⟩
    refine ⟨⟨hb, hD⟩, ?_⟩
    intro h
    exact hne (le_antisymm h.1 ha)
  · rintro ⟨⟨hb, hD⟩, hn⟩
    exact ⟨⟨le_of_not_ge (fun h => hn ⟨h, hD⟩), hb⟩, hD⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_annulus_closedDisk_eq_boundaryLens_sdiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_annulus_closedDisk_eq_boundaryLens_sdiff target :: scope.openDecls } }

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_boundary_energy_contraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ C / (1 + C) < 1 ∧
      ∀ (u : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤
        (L : ℝ≥0∞) * _root_.EDist.edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      ∀ s : ℝ, 0 < s → s < 1 / 4 →
      (∀ ρ ∈ _root_.Set.Ioo s (2 * s), ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      (∫ z in boundaryLens (2 * s), diskMapEnergyDensity g (diskExtension u) z) ≤ ε₀ →
      (∫ z in boundaryLens s, diskMapEnergyDensity g (diskExtension u) z) ≤
        (C / (1 + C)) *
          (∫ z in boundaryLens (2 * s), diskMapEnergyDensity g (diskExtension u) z) +
          (riemannianDiskEnergy g u -
            _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
              weaklyMonotoneDiskCompetitors g γ)) / (1 + C) := by
  obtain ⟨ε, Ccap, hε, hCcap, hcap⟩ := exists_uniform_intrinsic_boundary_cap_energy_bound g γ hγ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwoπ : 0 < 2 * Real.pi := by positivity
  let ε₀ := ε * Real.log 2 / (2 * Real.pi)
  let C := Ccap * (2 * Real.pi) / Real.log 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hCcap htwoπ.le) hlog.le
  have hden : 0 < 1 + C := by linarith
  refine ⟨ε₀, C, div_pos (mul_pos hε hlog) htwoπ, hC,
    (div_lt_one hden).mpr (by linarith), ?_⟩
  intro u L hu ψ hψ htrace s hs hsquarter hshort hsmall
  let d : ℂ → ℝ := diskMapEnergyDensity g (diskExtension u)
  let S := {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc s (2 * s)} ∩ _root_.Metric.closedBall (0 : ℂ) 1
  let B := ∫ z in S, d z
  have hdi : _root_.MeasureTheory.IntegrableOn d (_root_.Metric.closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g hu
  have hd0 (z : ℂ) : 0 ≤ d z :=
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hScap : S ⊆ boundaryLens (2 * s) := fun z hz => ⟨hz.1.2, hz.2⟩
  have hBcap : B ≤ ∫ z in boundaryLens (2 * s), d z :=
    _root_.MeasureTheory.setIntegral_mono_set (hdi.mono_set _root_.Set.inter_subset_right) (Eventually.of_forall hd0)
      (Eventually.of_forall hScap)
  obtain ⟨ρ, hρ, hαI, hαE⟩ := exists_radius_normalized_crosscut_riemannian_energy_le g
    (diskExtension_riemannian_lipschitz g hu) hs (by linarith : s < 2 * s)
    (by linarith : 2 * s < 2) (le_refl B)
  let α : ℝ → M := fun t => diskExtension u
    (circleMap (-1) ρ (-Real.arccos (ρ / 2) + 2 * Real.arccos (ρ / 2) * t))
  let Ea := ∫ t in _root_.Set.Icc (0 : ℝ) 1, (riemannianCurveSpeed g α t) ^ 2
  have hratio : (2 * s) / s = 2 := by field_simp [hs.ne']
  have hEa : Ea ≤ 2 * Real.pi * B / Real.log 2 := by
    simpa only [hratio] using hαE
  have hEasmall : Ea ≤ ε := by
    apply hEa.trans
    apply (div_le_iff₀ hlog).mpr
    have hBsmall : B ≤ ε₀ := hBcap.trans hsmall
    have h := mul_le_mul_of_nonneg_left hBsmall htwoπ.le
    have heq : (2 * Real.pi) * ε₀ = ε * Real.log 2 := by
      dsimp only [ε₀]
      field_simp
    exact h.trans_eq heq
  have hlocal := hcap u L hu ψ hψ htrace ρ (hs.trans hρ.1)
    (by linarith [hρ.2] : ρ < 1) (hshort ρ hρ) hαI hEasmall
  have hsmallρ : boundaryLens s ⊆ boundaryLens ρ := fun z hz =>
    ⟨closedBall_subset_closedBall hρ.1.le hz.1, hz.2⟩
  have hmono : (∫ z in boundaryLens s, d z) ≤ ∫ z in boundaryLens ρ, d z :=
    _root_.MeasureTheory.setIntegral_mono_set (hdi.mono_set _root_.Set.inter_subset_right) (Eventually.of_forall hd0)
      (Eventually.of_forall hsmallρ)
  have hcoeff : Ccap * (2 * Real.pi * B / Real.log 2) = C * B := by
    dsimp only [C]
    ring
  have hestimate : (∫ z in boundaryLens s, d z) ≤ C * B +
      (riemannianDiskEnergy g u -
        _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
          weaklyMonotoneDiskCompetitors g γ)) := by
    have hb := mul_le_mul_of_nonneg_left hEa hCcap
    rw [hcoeff] at hb
    exact hmono.trans (hlocal.trans (add_le_add hb le_rfl))
  have hsub : boundaryLens s ⊆ boundaryLens (2 * s) := fun z hz =>
    ⟨closedBall_subset_closedBall (by linarith : s ≤ 2 * s) hz.1, hz.2⟩
  have hAnn : B = (∫ z in boundaryLens (2 * s), d z) - ∫ z in boundaryLens s, d z := by
    rw [show B = ∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc s (2 * s)} ∩
      _root_.Metric.closedBall (0 : ℂ) 1, d z from rfl,
      integral_annulus_closedDisk_eq_boundaryLens_sdiff]
    exact _root_.MeasureTheory.setIntegral_sdiff (isClosed_closedBall.inter _root_.Metric.isClosed_closedBall).measurableSet
      (hdi.mono_set _root_.Set.inter_subset_right) hsub
  rw [hAnn] at hestimate
  change (∫ z in boundaryLens s, d z) ≤
    (C / (1 + C)) * (∫ z in boundaryLens (2 * s), d z) +
      (riemannianDiskEnergy g u - _) / (1 + C)
  rw [div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hestimate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_energy_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_energy_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_energy_contraction ``Submission.DifferentialGeometry.Geometry.exists_uniform_intrinsic_boundary_energy_contraction

end DifferentialGeometry.Geometry

end

end
