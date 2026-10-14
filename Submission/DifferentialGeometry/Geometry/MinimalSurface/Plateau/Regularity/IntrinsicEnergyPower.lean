import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalDefect
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Nonconcentration
import Submission.DifferentialGeometry.Analysis.Asymptotics.LimsupDecay
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.IntrinsicBoundaryPower
import Submission.DifferentialGeometry.Analysis.Asymptotics.TruncatedBallPower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem disk_energy_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z :=
  div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
    (metric_inner_self_nonneg g _ _)) (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.disk_energy_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.disk_energy_nonneg target :: scope.openDecls } }

private theorem integral_disk_energy_le_total
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ) {S : Set ℂ}
    (hS : S ⊆ _root_.Metric.closedBall (0 : ℂ) 1) :
    (∫ z in S, diskMapEnergyDensity g (diskExtension u) z) ≤ riemannianDiskEnergy g u :=
  _root_.MeasureTheory.setIntegral_mono_set (weaklyMonotoneDiskCompetitor_integrable_energy g hu)
    (Eventually.of_forall (disk_energy_nonneg g u)) (Eventually.of_forall hS)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_disk_energy_le_total
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_disk_energy_le_total target :: scope.openDecls } }

private theorem limsup_disk_energy_mono
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    {B : ℝ} (hB : ∀ n, riemannianDiskEnergy g (u n) ≤ B)
    {S T : Set ℂ} (hST : S ⊆ T) (hT : T ⊆ _root_.Metric.closedBall (0 : ℂ) 1) :
    _root_.Filter.limsup (fun n => ∫ z in S, diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤
      limsup (fun n => ∫ z in T, diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  apply _root_.Filter.limsup_le_limsup
    (Eventually.of_forall fun n => _root_.MeasureTheory.setIntegral_mono_set
      ((weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)).mono_set hT)
      (Eventually.of_forall (disk_energy_nonneg g (u n))) (Eventually.of_forall hST))
    (_root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      _root_.MeasureTheory.integral_nonneg (disk_energy_nonneg g (u n)))).isCoboundedUnder_le
    (_root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (integral_disk_energy_le_total g (hu n) hT).trans (hB n)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.limsup_disk_energy_mono
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.limsup_disk_energy_mono target :: scope.openDecls } }

private theorem dist_normalize_of_norm_le_one {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    dist x (NormedSpace.normalize x) = 1 - ‖x‖ := by
  have he : x - NormedSpace.normalize x = (‖x‖ - 1) • NormedSpace.normalize x := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx,
    mul_one, abs_of_nonpos (by linarith)]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.dist_normalize_of_norm_le_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.dist_normalize_of_norm_le_one target :: scope.openDecls } }

theorem exists_uniform_small_limsup_disk_energy_of_boundary_power
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    {β Kb δb : ℝ} (hβ : 0 < β) (hδb : 0 < δb)
    (hboundary : ∀ c ∈ _root_.Metric.sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δb →
      _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s,
        diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤ Kb * s ^ β)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∀ x ∈ _root_.Metric.closedBall (0 : ℂ) 1,
      ∀ s : ℝ, 0 < s → s ≤ δ →
        _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤ η := by
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (_root_.Set.mem_range_self n)
  obtain ⟨N, _, hevent⟩ := exists_eventually_uniform_small_ball_energy_of_minimizing_sequence
    g hregular γ u hu hmin hη
  have hlim : _root_.Filter.Tendsto (fun t : ℝ => Kb * (3 * t) ^ β) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Kb * (3 * t) ^ β) :=
      continuous_const.mul ((Real.continuous_rpow_const hβ.le).comp
        (continuous_const.mul continuous_id))
    simpa only [_root_.MulZeroClass.mul_zero, Real.zero_rpow hβ.ne'] using hc.tendsto 0
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hlim (Iio_mem_nhds hη))
  let d₀ := _root_.Min.min (r / 2) (_root_.Min.min (δb / 3) (1 / 8))
  have hd₀ : 0 < d₀ := lt_min (half_pos hr) (lt_min (by positivity) (by norm_num))
  have hd₀r : d₀ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hd₀b : d₀ ≤ δb / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hd₀8 : d₀ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : Kb * (3 * d₀) ^ β < η := hrsub (by
    simpa only [_root_.Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hd₀] using hd₀r)
  let δ := d₀ / (2 : ℝ) ^ N
  have hδ : 0 < δ := div_pos hd₀ (by positivity)
  have hδd : δ ≤ d₀ := div_le_self hd₀.le (one_le_pow₀ (by norm_num))
  refine ⟨δ, hδ, hδd.trans hd₀8, ?_⟩
  intro x hx s hs hsδ
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  by_cases hnear : 1 - ‖x‖ ≤ 2 * d₀
  · have hx0 : x ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hnear
      linarith [hd₀8]
    let c := NormedSpace.normalize x
    have hc : c ∈ _root_.Metric.sphere (0 : ℂ) 1 :=
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx0)
    have hxc : _root_.Dist.dist x c = 1 - ‖x‖ := dist_normalize_of_norm_le_one hx0 hx1
    have hcap : _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall x s ⊆
        ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall c (3 * d₀) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hdist := dist_triangle z x c
      rw [hxc] at hdist
      have hzx : _root_.Dist.dist z x ≤ s := hz.2
      change _root_.Dist.dist z c ≤ 3 * d₀
      linarith [hsδ.trans hδd]
    exact (limsup_disk_energy_mono g u hu htotal hcap
      (inter_subset_left.trans _root_.Metric.ball_subset_closedBall)).trans
        ((hboundary c hc (3 * d₀) (by positivity) (by linarith [hd₀b])).trans hsmall.le)
  · have hxR : ‖x‖ + d₀ < 1 := by linarith
    have hset : _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall x s ⊆ _root_.Metric.closedBall x δ :=
      fun z hz => _root_.Metric.closedBall_subset_closedBall hsδ hz.2
    have hT : _root_.Metric.closedBall x δ ⊆ _root_.Metric.closedBall (0 : ℂ) 1 := by
      intro z hz
      have hnorm : ‖z‖ ≤ _root_.Dist.dist z x + ‖x‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
      exact mem_closedBall_zero_iff.mpr (by linarith [mem_closedBall.mp hz])
    apply (limsup_disk_energy_mono g u hu htotal hset hT).trans
    apply _root_.Filter.limsup_le_of_le
      (_root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
        _root_.MeasureTheory.integral_nonneg (disk_energy_nonneg g (u n)))).isCoboundedUnder_le
    filter_upwards [hevent] with n hn
    exact hn x d₀ hd₀ hxR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_small_limsup_disk_energy_of_boundary_power then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_small_limsup_disk_energy_of_boundary_power"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_small_limsup_disk_energy_of_boundary_power ``Submission.DifferentialGeometry.Geometry.exists_uniform_small_limsup_disk_energy_of_boundary_power

theorem exists_limsup_disk_energy_half_contraction_of_boundary_power
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    {β Kb δb : ℝ} (hβ : 0 < β) (hδb : 0 < δb)
    (hboundary : ∀ c ∈ _root_.Metric.sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δb →
      _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall c s,
        diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤ Kb * s ^ β) :
    ∃ ε δ θ : ℝ, 0 < ε ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < θ ∧ θ < 1 ∧
      (∀ x ∈ _root_.Metric.closedBall (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤ ε / 2) ∧
      ∀ (x : ℂ) (s : ℝ), 0 < s → s ≤ δ → ‖x‖ + s < 1 →
        (∀ᶠ n in _root_.Filter.atTop, (∫ z in _root_.Metric.closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) < ε) ∧
        _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.closedBall x (s / 2),
          diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤
          θ * _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.closedBall x s,
            diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  obtain ⟨ε, θ, hε, hθ, hθ1, hcontract⟩ :=
    exists_local_energy_contraction_with_minimizing_defect g hregular
  obtain ⟨δ, hδ, hδ8, hsmall⟩ := exists_uniform_small_limsup_disk_energy_of_boundary_power
    g hregular γ u hu hmin hβ hδb hboundary (half_pos hε)
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (_root_.Set.mem_range_self n)
  refine ⟨ε, δ, θ, hε, hδ, hδ8, hθ, hθ1, hsmall, ?_⟩
  intro x s hs hsδ hxs
  have hx : x ∈ _root_.Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (by linarith)
  have hsub : _root_.Metric.closedBall x s ⊆ _root_.Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ _root_.Dist.dist z x + ‖x‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
    exact mem_ball_zero_iff.mpr (by linarith [mem_closedBall.mp hz])
  let a (n : ℕ) := ∫ z in _root_.Metric.closedBall x s, diskMapEnergyDensity g (diskExtension (u n)) z
  let b (n : ℕ) := ∫ z in _root_.Metric.closedBall x (s / 2), diskMapEnergyDensity g (diskExtension (u n)) z
  have ha0 : ∀ᶠ n in _root_.Filter.atTop, 0 ≤ a n :=
    Eventually.of_forall fun n => _root_.MeasureTheory.integral_nonneg (disk_energy_nonneg g (u n))
  have hb0 : ∀ᶠ n in _root_.Filter.atTop, 0 ≤ b n :=
    Eventually.of_forall fun n => _root_.MeasureTheory.integral_nonneg (disk_energy_nonneg g (u n))
  have haB : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop a :=
    _root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (integral_disk_energy_le_total g (hu n) (hsub.trans _root_.Metric.ball_subset_closedBall)).trans (htotal n))
  have halim : _root_.Filter.limsup a _root_.Filter.atTop ≤ ε / 2 := by
    have h := hsmall x hx s hs hsδ
    rwa [inter_eq_right.mpr hsub] at h
  have hevent : ∀ᶠ n in _root_.Filter.atTop, a n < ε :=
    _root_.Filter.eventually_lt_of_limsup_lt (halim.trans_lt (half_lt_self hε)) haB
  let defect (n : ℕ) := riemannianDiskEnergy g (u n) -
    _root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
  have hdefect : _root_.Filter.Tendsto defect _root_.Filter.atTop (𝓝 0) := by
    simpa only [defect, sub_self] using hmin.sub_const
      (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))
  have herr : _root_.Filter.Tendsto (fun n => (1 - θ) * defect n) _root_.Filter.atTop (𝓝 0) := by
    simpa only [_root_.MulZeroClass.mul_zero] using hdefect.const_mul (1 - θ)
  refine ⟨hevent, ?_⟩
  apply limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero hθ.le ha0 haB hb0 herr
  filter_upwards [hevent] with n hn
  exact hcontract γ (u n) (hu n) x s hs hxs hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_limsup_disk_energy_half_contraction_of_boundary_power then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_limsup_disk_energy_half_contraction_of_boundary_power"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_limsup_disk_energy_half_contraction_of_boundary_power ``Submission.DifferentialGeometry.Geometry.exists_limsup_disk_energy_half_contraction_of_boundary_power

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_truncated_ball_power_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3) :
    ∃ p δ C : ℝ, 0 < p ∧ p ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ C ∧
      ∀ x ∈ _root_.Metric.closedBall (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        _root_.Filter.limsup (fun n => ∫ z in _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) _root_.Filter.atTop ≤ C * s ^ p := by
  obtain ⟨β, Kb, δb, hβ, _, hKb, hδb, hboundary⟩ :=
    exists_uniform_intrinsic_boundary_power_bound g γ hγ u hu hmin ψ hψ htrace hthird htwothird
  obtain ⟨_, δi, θ, _, hδi, _, hθ, hθ1, _, hhalf⟩ :=
    exists_limsup_disk_energy_half_contraction_of_boundary_power
      g hregular γ u hu hmin hβ hδb hboundary
  let e (n : ℕ) := diskMapEnergyDensity g (diskExtension (u n))
  let ν (S : Set ℂ) := _root_.Filter.limsup (fun n => ∫ z in S, e n z) _root_.Filter.atTop
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (_root_.Set.mem_range_self n)
  have h0 (n : ℕ) (z : ℂ) : 0 ≤ e n z := by
    unfold e diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hi (n : ℕ) := weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)
  have hsubsetBound {S : Set ℂ} (hS : S ⊆ _root_.Metric.closedBall (0 : ℂ) 1) (n : ℕ) :
      (∫ z in S, e n z) ≤ B :=
    (_root_.MeasureTheory.setIntegral_mono_set (hi n) (Eventually.of_forall (h0 n))
      (Eventually.of_forall hS)).trans (htotal n)
  have hmono : ∀ {S T : Set ℂ}, S ⊆ T → T ⊆ _root_.Metric.ball (0 : ℂ) 1 → ν S ≤ ν T := by
    intro S T hST hTD
    exact _root_.Filter.limsup_le_limsup (Eventually.of_forall fun n =>
      _root_.MeasureTheory.setIntegral_mono_set ((hi n).mono_set (hTD.trans _root_.Metric.ball_subset_closedBall))
        (Eventually.of_forall (h0 n)) (Eventually.of_forall hST))
      (_root_.Filter.isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun n => _root_.MeasureTheory.integral_nonneg (h0 n))).isCoboundedUnder_le
      (_root_.Filter.isBoundedUnder_of_eventually_le
        (Eventually.of_forall (hsubsetBound (hTD.trans _root_.Metric.ball_subset_closedBall))))
  have hν : 0 ≤ ν (_root_.Metric.ball (0 : ℂ) 1) :=
    _root_.Filter.le_limsup_of_frequently_le (Eventually.of_forall (fun n => _root_.MeasureTheory.integral_nonneg (h0 n))).frequently
      (_root_.Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall (hsubsetBound _root_.Metric.ball_subset_closedBall)))
  obtain ⟨p, δ, C, hp, _, hp2, hδ, hδ8, hC, hpower⟩ :=
    exists_uniform_truncated_ball_power_bound_of_boundary_bound_of_half_contraction ν
      hmono hν hβ hKb hδb hδi hθ.le hθ1 hboundary
      (fun x s hs hsδ hxs => (hhalf x s hs hsδ hxs).2)
  exact ⟨p, δ, C, hp, hp2, hδ, hδ8, hC, hpower⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_intrinsic_truncated_ball_power_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_intrinsic_truncated_ball_power_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_intrinsic_truncated_ball_power_bound ``Submission.DifferentialGeometry.Geometry.exists_uniform_intrinsic_truncated_ball_power_bound

end DifferentialGeometry.Geometry

end

end
