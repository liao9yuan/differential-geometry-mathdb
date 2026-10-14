/-
Authors: Jack McCarthy
Modified by: Ziyang Qin
-/
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open scoped _root_.Manifold _root_.Topology _root_.ContDiff
open _root_.Bundle _root_.Filter

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, IsScalarTower ℝ 𝕜 (V x)]
  [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}

theorem exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    (hs : ∀ i, CMDiff[u] n (T% (s i))) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs i)
  · filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exists_contMDiffSection_eqOn_nhd then
    throwError "Refusing to shadow existing declaration exists_contMDiffSection_eqOn_nhd"
  Lean.modifyEnv fun env => Lean.addAlias env `exists_contMDiffSection_eqOn_nhd ``Submission.exists_contMDiffSection_eqOn_nhd

open _root_.IsLocalFrameOn in
theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs.contMDiffOn i)
  · filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalFrameOn
  let env ← Lean.getEnv
  if env.contains `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd then
    throwError "Refusing to shadow existing declaration IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd ``Submission.IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
