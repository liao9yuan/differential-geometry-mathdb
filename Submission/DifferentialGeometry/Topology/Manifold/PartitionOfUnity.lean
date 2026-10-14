import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Submission.DifferentialGeometry.Topology.PartitionOfUnity.FiniteSum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open _root_.SmoothPartitionOfUnity in
theorem exists_isSubordinate_chartAt_source_inter_interior :
    ∃ rho : SmoothPartitionOfUnity M I M _root_.Set.univ,
      rho.IsSubordinate (fun x => (chartAt H x).source) ∧
      ∀ x ∈ I.interior M, tsupport (rho x) ⊆ I.interior M := by
  classical
  let U : M → Set M := fun x => if x ∈ I.interior M then
    (chartAt H x).source ∩ I.interior M else (chartAt H x).source
  have hUopen (x : M) : IsOpen (U x) := by
    dsimp only [U]
    split_ifs
    · exact (chartAt H x).open_source.inter (I.isOpen_interior (by simp : (∞ : WithTop ℕ∞) ≠ 0))
    · exact (chartAt H x).open_source
  have hUcover : (_root_.Set.univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    apply _root_.Set.mem_iUnion_of_mem x
    dsimp only [U]
    split_ifs with hx
    · exact ⟨mem_chart_source H x, hx⟩
    · exact mem_chart_source H x
  obtain ⟨rho, hrho⟩ := _root_.SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hUopen hUcover
  refine ⟨rho, ?_, ?_⟩
  · intro x y hy
    have h := hrho x hy
    dsimp only [U] at h
    split_ifs at h
    · exact h.1
    · exact h
  · intro x hx y hy
    have h := hrho x hy
    dsimp only [U] at h
    rw [if_pos hx] at h
    exact h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_inter_interior then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_inter_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_inter_interior ``Submission.SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_inter_interior

end SmoothPartitionOfUnity

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_countable_compactly_supported_chart_partition
    (χ : ∀ p : M, SmoothBumpFunction I p) :
    ∃ (ι : Type u), Countable ι ∧ ∃ (center : ι → M)
      (ρ : SmoothPartitionOfUnity ι I M _root_.Set.univ),
      (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
      (∀ i, tsupport (ρ i : M → ℝ) ⊆
        interior {p | χ (center i) p = 1} ∩ (extChartAt I (center i)).source) ∧
      (∀ (t : Finset ι) (p : M), (∑ i ∈ t, ρ i p) ≤ 1) ∧
      ∀ p : M, ∑ᶠ i, ρ i p = 1 := by
  let U : M → Set M := fun p => interior {q | χ p q = 1} ∩ (chartAt H p).source
  have hU (p : M) : U p ∈ 𝓝 p :=
    _root_.Filter.inter_mem (isOpen_interior.mem_nhds
      (mem_interior_iff_mem_nhds.mpr (χ p).eventuallyEq_one))
      ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  obtain ⟨ι, fs, hfs⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (fun p _ => hU p)
  let : Encodable ι := fs.locallyFinite.encodable (fun i => (fs i).nonempty_support)
  let ρ := fs.toSmoothPartitionOfUnity
  have hsub := hfs.toSmoothPartitionOfUnity
  refine ⟨ι, inferInstance, fs.c, ρ, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (fs i).hasCompactSupport.mono (fs.support_toSmoothPartitionOfUnity_subset i)
  · intro i
    simpa only [U, extChartAt_source] using hsub i
  · intro t p
    exact ρ.toPartitionOfUnity.sum_finset_le_one t p
  · intro p
    exact ρ.sum_eq_one (_root_.Set.mem_univ p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_countable_compactly_supported_chart_partition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_countable_compactly_supported_chart_partition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_countable_compactly_supported_chart_partition ``Submission.DifferentialGeometry.Geometry.exists_countable_compactly_supported_chart_partition

end DifferentialGeometry.Geometry

end

end
