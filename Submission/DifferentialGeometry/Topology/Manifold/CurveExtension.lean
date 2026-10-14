import Submission.DifferentialGeometry.Topology.Manifold.Curve
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiff_curve_with_velocity_range_subset
    {x : M} (hx : I.IsInteriorPoint x) (v : TangentSpace I x)
    {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ _root_.Set.range γ ⊆ U ∧
      (⟨γ 0, mfderiv 𝓘(ℝ, ℝ) I γ 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)⟩ : TangentBundle I M) = ⟨x, v⟩ := by
  obtain ⟨ε, hε, γ, hγ, hγU, hvel⟩ :=
    exists_contMDiff_curve_with_velocity (by simp : (1 : ℕ∞ω) ≤ ∞) hx v hU
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := ε / 2
      rOut := ε
      rIn_pos := half_pos hε
      rIn_lt_rOut := half_lt_self hε }
  let ρ : ℝ → ℝ := fun t => b t * t
  have hbmem (t : ℝ) : ρ t ∈ _root_.Set.Icc (-ε) ε := by
    by_cases hbt : b t = 0
    · simpa [ρ, hbt] using (show (0 : ℝ) ∈ _root_.Set.Icc (-ε) ε from ⟨by linarith, hε.le⟩)
    · have ht : |t| < ε := by
        have hs : t ∈ Metric.ball (0 : ℝ) b.rOut := b.support_eq ▸ hbt
        simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hs
      have hbnd : |ρ t| ≤ |t| := by
        simp only [ρ, abs_mul, abs_of_nonneg b.nonneg]
        exact mul_le_of_le_one_left (abs_nonneg t) b.le_one
      exact ⟨(abs_le.mp (hbnd.trans ht.le)).1, (abs_le.mp (hbnd.trans ht.le)).2⟩
  have hb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ :=
    (b.contDiff.mul contDiff_id).contMDiff
  have heq : γ ∘ ρ =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) b.rIn_pos] with t ht
    change γ (b t * t) = γ t
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall ht), one_mul]
  refine ⟨γ ∘ ρ, hγ.comp_contMDiff hb hbmem, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hγU (hbmem t)
  · refine Eq.trans (TotalSpace.ext heq.self_of_nhds ?_) hvel
    exact heq_of_eq (congrArg (fun f : ℝ →L[ℝ] E => f 1) heq.mfderiv_eq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_contMDiff_curve_with_velocity_range_subset then
    throwError "Refusing to shadow existing declaration exists_contMDiff_curve_with_velocity_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_contMDiff_curve_with_velocity_range_subset ``Submission.exists_contMDiff_curve_with_velocity_range_subset
