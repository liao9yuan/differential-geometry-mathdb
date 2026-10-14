import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Coordinates.FixedChartIdentities
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_smooth_variation_fixed_initial_germ
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    {c b : ℝ} (hcb : c < b) :
    ∃ F : ℝ → ℝ → M,
      IsSmoothVariation (I := I) F ∧
      F 0 = f 0 ∧
      (∀ u, F u =ᶠ[𝓝 c] f 0) ∧
      (∀ u, F u b = f u b) := by
  obtain ⟨chi, hchi, _hcpt, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      (K := ({b} : Set ℝ)) isCompact_singleton (U := _root_.Set.Ioi ((c + b) / 2))
      isOpen_Ioi (by intro t ht; rw [_root_.Set.mem_singleton_iff] at ht; subst t; change (c + b) / 2 < b; linarith)
  have hchib : chi b = 1 := by
    have hb : chi =ᶠ[𝓝 b] 1 := by simpa only [nhdsSet_singleton] using hone
    exact hb.self_of_nhds
  have hzero : chi =ᶠ[𝓝 c] 0 := by
    filter_upwards [Iio_mem_nhds (by linarith : c < (c + b) / 2)] with s hs
    apply notMem_support.mp
    intro hmem
    have hx := hsupp (subset_closure hmem)
    exact (not_lt_of_ge hs.le) (show (c + b) / 2 < s from hx)
  let F : ℝ → ℝ → M := fun u s ↦ f (chi s * u) s
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · have hchiM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ) chi :=
      hchi.contMDiff.of_le (by
        change ((8 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hf.comp (((hchiM.comp contMDiff_snd).mul contMDiff_fst).prodMk contMDiff_snd)
  · funext s
    simp only [F, _root_.MulZeroClass.mul_zero]
  · intro u
    filter_upwards [hzero] with s hs
    simp only [F, hs, Pi.zero_apply, _root_.MulZeroClass.zero_mul]
  · intro u
    simp only [F, hchib, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.exists_smooth_variation_fixed_initial_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.exists_smooth_variation_fixed_initial_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.exists_smooth_variation_fixed_initial_germ ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.exists_smooth_variation_fixed_initial_germ

end DifferentialGeometry.Geometry.Riemannian.Variation
