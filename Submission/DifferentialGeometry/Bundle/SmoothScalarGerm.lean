import Submission.DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.Algebra.Structures

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem exists_smooth_germ
    {f : M → ℝ} {U : Set M} {x : M} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ F =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (hU.mem_nhds hx)
  refine ⟨fun y => χ y * f y, ?_, ?_⟩
  · have hχ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => (χ : M → ℝ) y) :=
      χ.contMDiff.of_le (by exact_mod_cast le_top)
    have hU_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => χ y * f y) U :=
      hχ_smooth.contMDiffOn.mul hf
    have hcompl_part : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => χ y * f y) (tsupport χ)ᶜ := by
      apply (contMDiffOn_const (c := (0 : ℝ))).congr
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport hy, _root_.MulZeroClass.zero_mul]
    refine contMDiff_of_contMDiffOn_union_of_isOpen hU_part hcompl_part ?_
      hU (isOpen_compl_iff.mpr (isClosed_tsupport χ))
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact Or.inl (hχ hy)
    · exact Or.inr hy
  · filter_upwards [χ.eventuallyEq_one] with y hy
    rw [hy, Pi.one_apply, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_smooth_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_smooth_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_smooth_germ ``Submission.DifferentialGeometry.exists_smooth_germ

end DifferentialGeometry
