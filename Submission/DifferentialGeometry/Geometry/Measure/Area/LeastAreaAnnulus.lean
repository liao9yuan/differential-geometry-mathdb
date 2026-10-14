import Submission.DifferentialGeometry.Geometry.Measure.Area.LeastArea
import Submission.DifferentialGeometry.Geometry.Measure.Area.AnnulusCompetitor

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



theorem leastSpanningArea_le_add_annulus (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : lipschitzContractibleLoop g) {K : ℝ≥0}
    (hH : ∀ p q, riemannianEDistOf g
      (geodesicAnnulus g γ₀.val.val γ₁.val.val p) (geodesicAnnulus g γ₀.val.val γ₁.val.val q) ≤
        (K : ℝ≥0∞) * _root_.EDist.edist p q) :
    leastSpanningArea g γ₁ ≤ leastSpanningArea g γ₀ + geodesicAnnulusArea g γ₀.val.val γ₁.val.val := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u, hu, huarea⟩ := exists_spanningDisk_area_lt g γ₀ hε
  obtain ⟨v, hv, hvarea⟩ := exists_competitor_attach_geodesicAnnulus g hH hu
  have hle := leastSpanningArea_le_competitor g γ₁ hv
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.leastSpanningArea_le_add_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.leastSpanningArea_le_add_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.leastSpanningArea_le_add_annulus ``Submission.DifferentialGeometry.Geometry.leastSpanningArea_le_add_annulus



theorem exists_leastSpanningArea_annulus_bound (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ γ₀ γ₁ : lipschitzContractibleLoop g,
      riemannianLoopDistance g γ₀.val.val γ₁.val.val < ρ →
      |leastSpanningArea g γ₀ - leastSpanningArea g γ₁| ≤
        C * riemannianLoopDistance g γ₀.val.val γ₁.val.val *
          (riemannianCurveLength g (fun t => γ₀.val.val (t : loopCircle)) 0 1 +
            riemannianCurveLength g (fun t => γ₁.val.val (t : loopCircle)) 0 1) := by
  obtain ⟨ρ, C, hρ, hC, hann⟩ := exists_nearby_loop_annulus g
  refine ⟨ρ, C, hρ, hC, fun γ₀ γ₁ hnear => ?_⟩
  obtain ⟨L₀, h₀⟩ := γ₀.property
  obtain ⟨L₁, h₁⟩ := γ₁.property
  obtain ⟨⟨K₀₁, hK₀₁⟩, harea₀₁, _⟩ := hann γ₀.val.val γ₁.val.val L₀ L₁ h₀ h₁ hnear
  have hnear' : riemannianLoopDistance g γ₁.val.val γ₀.val.val < ρ := by
    rw [riemannianLoopDistance_symm]
    exact hnear
  obtain ⟨⟨K₁₀, hK₁₀⟩, harea₁₀, _⟩ := hann γ₁.val.val γ₀.val.val L₁ L₀ h₁ h₀ hnear'
  have hle₀₁ := leastSpanningArea_le_add_annulus g γ₀ γ₁ hK₀₁
  have hle₁₀ := leastSpanningArea_le_add_annulus g γ₁ γ₀ hK₁₀
  rw [riemannianLoopDistance_symm g γ₁.val.val γ₀.val.val,
    add_comm (riemannianCurveLength g (fun t => γ₁.val.val (t : loopCircle)) 0 1)] at harea₁₀
  rw [abs_sub_le_iff]
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_leastSpanningArea_annulus_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_leastSpanningArea_annulus_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_leastSpanningArea_annulus_bound ``Submission.DifferentialGeometry.Geometry.exists_leastSpanningArea_annulus_bound

end DifferentialGeometry.Geometry
