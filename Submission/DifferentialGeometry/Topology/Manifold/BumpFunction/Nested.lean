import Mathlib.Geometry.Manifold.BumpFunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace SmoothBumpFunction
open _root_.SmoothBumpFunction

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

open _root_.SmoothBumpFunction in
theorem exists_tsupport_subset_interior_one {center : M} (χ : SmoothBumpFunction I center) :
    ∃ ρ : SmoothBumpFunction I center,
      tsupport (ρ : M → ℝ) ⊆ interior {p | χ p = 1} ∩ (chartAt H center).source := by
  have hone : {p : M | χ p = 1} ∈ 𝓝 center := χ.eventuallyEq_one
  have hnhds : interior {p : M | χ p = 1} ∩ (chartAt H center).source ∈ 𝓝 center :=
    _root_.Filter.inter_mem (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hone))
      ((chartAt H center).open_source.mem_nhds (mem_chart_source H center))
  obtain ⟨ρ, _, hρ⟩ := (_root_.SmoothBumpFunction.nhds_basis_tsupport (I := I) center).mem_iff.mp hnhds
  exact ⟨ρ, hρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothBumpFunction.exists_tsupport_subset_interior_one then
    throwError "Refusing to shadow existing declaration SmoothBumpFunction.exists_tsupport_subset_interior_one"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothBumpFunction.exists_tsupport_subset_interior_one ``Submission.SmoothBumpFunction.exists_tsupport_subset_interior_one

end SmoothBumpFunction

end

end
