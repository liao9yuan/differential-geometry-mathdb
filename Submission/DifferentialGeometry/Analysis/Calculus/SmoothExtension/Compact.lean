import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_compactSupport_extension_on_isCompact
    {n : ℕ∞} {f : E → F} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨χ, hχsmooth, hχcompact, hχone, hχsupport, _⟩ :=
    exists_mfd_bump (I := 𝓘(ℝ, E)) hK hU hKU
  let g : E → F := fun x => χ x • f x
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n g := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxχ : x ∈ tsupport χ := (tsupport_smul_subset_left χ f) hx
    have hfx : ContDiffAt ℝ n f x := (hf x (hχsupport hxχ)).contDiffAt
      (hU.mem_nhds (hχsupport hxχ))
    exact (hχsmooth.of_le (by exact_mod_cast le_top)).contMDiffAt.smul hfx.contMDiffAt
  refine ⟨g, contMDiff_iff_contDiff.mp hg, ?_, ?_⟩
  · exact hχcompact.smul_right
  · filter_upwards [hχone] with x hx
    simp only [g, hx, Pi.one_apply, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact ``Submission.DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact

end DifferentialGeometry.Analysis
