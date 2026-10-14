import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.Crosscut
import Submission.DifferentialGeometry.Analysis.Integration.Integral.IsometricDerivative
import Submission.DifferentialGeometry.Analysis.Complex.CircleRotation
import Submission.DifferentialGeometry.Topology.MetricSpace.BoundaryExtension
import Mathlib.MeasureTheory.Measure.Restrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_boundary_approach_neg_one
    (f : ℕ → ℂ → E) (v η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hv : ContinuousOn v (Metric.ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (η z)))
    (hη : ContinuousWithinAt η (Metric.sphere (0 : ℂ) 1) (-1))
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, _root_.Dist.dist z (-1) < R ∧ _root_.Dist.dist (v z) (η (-1)) < ε := by
  obtain ⟨S, hS, r, hr, ρ, hρ, _, _, β, _, hβv, _, _, hclose⟩ :=
    exists_small_boundary_crosscut_tendsto_uniformly f v η K hf hv hae hboundary hη
      henergy hR hε
  have hρ0 : 0 < ρ := hr.1.trans hρ.1
  have hρ2 : ρ < 2 := hρ.2.trans (hS.2.trans_le (min_le_right R 2))
  have ha0 : 0 < Real.arccos (ρ / 2) := Real.arccos_pos.mpr (by linarith)
  have hθ : (0 : ℝ) ∈ _root_.Set.Ioo (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2)) :=
    ⟨neg_lt_zero.mpr ha0, ha0⟩
  refine ⟨circleMap (-1) ρ 0, Complex.circleMap_neg_one_mem_ball ρ hρ0 hθ, ?_, ?_⟩
  · rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
    exact hρ.2.trans (hS.2.trans_le (min_le_left R 2))
  · have h := hclose ⟨0, _root_.Set.Ioo_subset_Icc_self hθ⟩
    rw [hβv 0 hθ] at h
    simpa only [dist_eq_norm] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_boundary_approach_neg_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_boundary_approach_neg_one target :: scope.openDecls } }

theorem exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound
    (f : ℕ → ℂ → E) (v η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hv : ContinuousOn v (Metric.ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (η z)))
    (hη : ContinuousOn η (Metric.sphere (0 : ℂ) 1))
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B) :
    ∀ p ∈ Metric.sphere (0 : ℂ) 1, ∀ ε > 0, ∀ R > 0,
      ∃ z ∈ Metric.ball (0 : ℂ) 1, _root_.Dist.dist z p < R ∧ _root_.Dist.dist (v z) (η p) < ε := by
  intro p hp ε hε R hR
  let c : Circle := ⟨-p, by
    change -p ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using hp⟩
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := rotation c
  have he : e (-1) = p := by
    change (-p) * (-1) = p
    ring
  have hmap : _root_.Set.MapsTo e (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz
  have hmaps : _root_.Set.MapsTo e (Metric.sphere (0 : ℂ) 1) (Metric.sphere (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_sphere, dist_zero_right, e.norm_map] using hz
  have hfn (n : ℕ) : LipschitzWith (K n) (f n ∘ e) := by
    simpa only [mul_one] using (hf n).comp e.isometry.lipschitz
  have hv' : ContinuousOn (v ∘ e) (Metric.ball (0 : ℂ) 1) :=
    hv.comp e.continuous.continuousOn hmap
  have hq : Measure.QuasiMeasurePreserving e
      (volume.restrict (Metric.ball (0 : ℂ) 1))
      (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    e.measurePreserving.quasiMeasurePreserving.restrict hmap
  have hae' : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      Tendsto (fun n => (f n ∘ e) z) _root_.Filter.atTop (𝓝 ((v ∘ e) z)) := hq.ae hae
  have hboundary' (z : ℂ) (hz : ‖z‖ = 1) :
      Tendsto (fun n => (f n ∘ e) z) _root_.Filter.atTop (𝓝 ((η ∘ e) z)) :=
    hboundary (e z) (by simpa only [e.norm_map] using hz)
  have hη' : ContinuousWithinAt (η ∘ e) (Metric.sphere (0 : ℂ) 1) (-1) :=
    (hη.comp e.continuous.continuousOn hmaps) (-1) (by simp)
  have henergy' (n : ℕ) :
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n ∘ e) z‖ ^ 2) ≤ B := by
    rw [e.integral_norm_fderiv_sq_comp_closedBall]
    exact henergy n
  obtain ⟨z, hz, hzp, hvz⟩ := exists_boundary_approach_neg_one
    (fun n => f n ∘ e) (v ∘ e) (η ∘ e) K hfn hv' hae' hboundary' hη' henergy' hε hR
  refine ⟨e z, hmap hz, ?_, ?_⟩
  · rw [← he, e.isometry.dist_eq]
    exact hzp
  · simpa only [Function.comp_apply, he] using hvz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound ``Submission.DifferentialGeometry.Analysis.exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound

theorem exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound
    (f : ℕ → ℂ → E) (v η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hv : UniformContinuousOn v (Metric.ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (η z)))
    (hη : ContinuousOn η (Metric.sphere (0 : ℂ) 1))
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B) :
    ∃ q : C(Topology.closedDisk, E), UniformContinuous q ∧
      (∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1), q ⟨z, Metric.ball_subset_closedBall hz⟩ = v z) ∧
      (∀ p (hp : p ∈ Metric.sphere (0 : ℂ) 1),
        q ⟨p, Metric.sphere_subset_closedBall hp⟩ = η p) ∧
      ∀ S : Set E, IsClosed S → _root_.Set.MapsTo v (Metric.ball (0 : ℂ) 1) S → _root_.Set.range q ⊆ S := by
  apply Topology.exists_continuous_disk_extension_of_uniformContinuousOn_of_boundary_approach hv
  intro p hp ε hε R hR
  simpa only [dist_eq_norm] using
    exists_interior_boundary_approach_of_lipschitz_sequence_energy_bound
      f v η K hf hv.continuousOn hae hboundary hη henergy p hp ε hε R hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound ``Submission.DifferentialGeometry.Analysis.exists_continuous_disk_extension_of_lipschitz_sequence_energy_bound

end DifferentialGeometry.Analysis

end
