import Submission.DifferentialGeometry.Geometry.Measure.Area.AnnulusCompetitor
import Submission.DifferentialGeometry.Geometry.Metric.LoopLengthBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M] [Nonempty M]



theorem exists_short_loop_filling_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ σ K : ℝ≥0, 0 < σ ∧ 0 < K ∧ ∀ (γ : freeLoop M) (L : ℝ≥0),
      (∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * _root_.EDist.edist x y) →
      riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 < σ →
      ∃ u ∈ spanningDiskCompetitors g γ,
        riemannianDiskArea g u ≤ K * (riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1) ^ 2 := by
  obtain ⟨ρ, K, hρ, hK, hann⟩ := exists_nearby_loop_annulus g
  refine ⟨ρ, K, hρ, hK, fun γ L hγ hshort => ?_⟩
  let γ₀ : freeLoop M := ContinuousMap.const loopCircle (γ 0)
  have h₀ : ∀ x y, riemannianEDistOf g (γ₀ x) (γ₀ y) ≤ (0 : ℝ≥0∞) * _root_.EDist.edist x y := by
    intro x y
    change riemannianEDistOf g (γ 0) (γ 0) ≤ _
    simp only [riemannianEDistOf_self, _root_.MulZeroClass.zero_mul, le_refl]
  have hD := loopDistance_from_constant_le_length g γ hγ
  have hnear : riemannianLoopDistance g γ₀ γ < ρ := by
    exact_mod_cast hD.trans_lt hshort
  obtain ⟨_, harea, hattach⟩ := hann γ₀ γ 0 L h₀ hγ hnear
  let u₀ : C(closedDisk, M) := ContinuousMap.const closedDisk (γ 0)
  have hu₀ : u₀ ∈ spanningDiskCompetitors g γ₀ := by
    refine ⟨rfl, 0, fun z w => ?_⟩
    simp only [u₀, ContinuousMap.const_apply, riemannianEDistOf_self, ENNReal.coe_zero, _root_.MulZeroClass.zero_mul, le_refl]
  obtain ⟨u, hu, hueq⟩ := hattach u₀ hu₀
  have hl₀ : riemannianCurveLength g (fun t => γ₀ (t : loopCircle)) 0 1 = 0 :=
    riemannianCurveLength_const g (γ 0) 0 1
  have ha₀ : riemannianDiskArea g u₀ = 0 := riemannianDiskArea_const g (γ 0)
  refine ⟨u, hu, ?_⟩
  rw [hueq, ha₀, zero_add]
  rw [hl₀, zero_add] at harea
  apply harea.trans
  have hl := riemannianCurveLength_nonneg g (fun t => γ (t : loopCircle)) 0 1
  calc
    (K : ℝ) * riemannianLoopDistance g γ₀ γ * riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1
        ≤ (K : ℝ) * riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 *
            riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 := by
          gcongr
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_short_loop_filling_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_short_loop_filling_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_short_loop_filling_bound ``Submission.DifferentialGeometry.Geometry.exists_short_loop_filling_bound



theorem exists_short_loop_contractibility_radius (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ σ : ℝ≥0, 0 < σ ∧ ∀ (γ : freeLoop M) (L : ℝ≥0),
      (∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * _root_.EDist.edist x y) →
      riemannianCurveLength g (fun t => γ (t : loopCircle)) 0 1 < σ → γ.Nullhomotopic := by
  obtain ⟨σ, _, hσ, _, hfill⟩ := exists_short_loop_filling_bound g
  refine ⟨σ, hσ, fun γ L hγ hshort => ?_⟩
  obtain ⟨u, ⟨htrace, _⟩, _⟩ := hfill γ L hγ hshort
  rw [← htrace]
  exact diskTrace_nullhomotopic u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_short_loop_contractibility_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_short_loop_contractibility_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_short_loop_contractibility_radius ``Submission.DifferentialGeometry.Geometry.exists_short_loop_contractibility_radius

end DifferentialGeometry.Geometry
