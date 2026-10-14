import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Submission.DifferentialGeometry.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace ContMDiffSection
open _root_.ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
variable {n : ℕ∞}

open _root_.ContMDiffSection in
theorem exists_compactly_supported_eq_nhdsSet
    (S : Cₛ^n⟮I; F, V⟯) {K : Set M} (hK : IsCompact K) :
    ∃ T : Cₛ^n⟮I; F, V⟯,
      IsCompact (closure {x : M | T x ≠ 0}) ∧ ∀ᶠ x in 𝓝ˢ K, T x = S x := by
  classical
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one⟩ :=
    DifferentialGeometry.Analysis.exists_bump_nhds (I := I) hK
  let T : Cₛ^n⟮I; F, V⟯ :=
    ⟨fun x => χ x • S x,
      (hχ_smooth.of_le (by exact_mod_cast le_top)).smul_section S.contMDiff⟩
  refine ⟨T, ?_, ?_⟩
  · apply hχ_compact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change χ x ≠ 0
    intro hzero
    apply hx
    change χ x • S x = 0
    rw [hzero, zero_smul]
  · filter_upwards [hχ_one] with x hx
    change χ x • S x = S x
    rw [hx, Pi.one_apply, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffSection.exists_compactly_supported_eq_nhdsSet then
    throwError "Refusing to shadow existing declaration ContMDiffSection.exists_compactly_supported_eq_nhdsSet"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffSection.exists_compactly_supported_eq_nhdsSet ``Submission.ContMDiffSection.exists_compactly_supported_eq_nhdsSet

end ContMDiffSection
