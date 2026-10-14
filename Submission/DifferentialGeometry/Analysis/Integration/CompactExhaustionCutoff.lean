import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Topology.Compactness.SigmaCompact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Topology _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

include I

noncomputable def manifoldCompactExhaustion : CompactExhaustion M :=
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  CompactExhaustion.choice M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.manifoldCompactExhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.manifoldCompactExhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.manifoldCompactExhaustion ``Submission.DifferentialGeometry.Analysis.manifoldCompactExhaustion

noncomputable def compactExhaustionCutoff
    (K : CompactExhaustion M) (n : ℕ) : M → ℝ :=
  Classical.choose (exists_mfd_bump (I := I) (M := M)
    (K.isCompact n)
    isOpen_interior
    (K.subset_interior_succ n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.compactExhaustionCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.compactExhaustionCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.compactExhaustionCutoff ``Submission.DifferentialGeometry.Analysis.compactExhaustionCutoff

theorem compactExhaustionCutoff_spec (K : CompactExhaustion M) (n : ℕ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (compactExhaustionCutoff (I := I) (M := M) K n) ∧
      HasCompactSupport (compactExhaustionCutoff (I := I) (M := M) K n) ∧
      (∀ x ∈ K n, compactExhaustionCutoff (I := I) (M := M) K n x = 1) ∧
      tsupport (compactExhaustionCutoff (I := I) (M := M) K n) ⊆
        interior (K (n + 1)) ∧
      Set.range (compactExhaustionCutoff (I := I) (M := M) K n) ⊆ Set.Icc 0 1 := by
  classical
  let hB := exists_mfd_bump (I := I) (M := M)
    (K.isCompact n)
    isOpen_interior
    (K.subset_interior_succ n)
  let χ := Classical.choose hB
  have hχ := Classical.choose_spec hB
  change ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
    (∀ x ∈ K n, χ x = 1) ∧
    tsupport χ ⊆ interior (K (n + 1)) ∧
    Set.range χ ⊆ Set.Icc 0 1
  rcases hχ with ⟨hχsmooth, hχsupport, hχone, hχsubset, hχrange⟩
  refine ⟨hχsmooth, hχsupport, ?_, hχsubset, hχrange⟩
  intro x hx
  have hxmem : {y : M | χ y = (1 : M → ℝ) y} ∈ 𝓝 x :=
    (mem_nhdsSet_iff_forall.mp hχone) x hx
  change x ∈ {y : M | χ y = (1 : M → ℝ) y}
  exact mem_of_mem_nhds hxmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.compactExhaustionCutoff_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.compactExhaustionCutoff_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.compactExhaustionCutoff_spec ``Submission.DifferentialGeometry.Analysis.compactExhaustionCutoff_spec

theorem compactExhaustionCutoff_eventually_one_on_compact
    (K : CompactExhaustion M) (s : Set M) (hs : IsCompact s) :
    ∀ᶠ n in _root_.Filter.atTop, ∀ x ∈ s,
      compactExhaustionCutoff (I := I) (M := M) K n x = 1 := by
  obtain ⟨n₀, hn₀⟩ :=
    K.exists_superset_of_isCompact hs
  filter_upwards [_root_.Filter.eventually_ge_atTop n₀] with n hn x hx
  exact (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.1 x
    ((K.subset hn) (hn₀ hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.compactExhaustionCutoff_eventually_one_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.compactExhaustionCutoff_eventually_one_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.compactExhaustionCutoff_eventually_one_on_compact ``Submission.DifferentialGeometry.Analysis.compactExhaustionCutoff_eventually_one_on_compact

end DifferentialGeometry.Analysis
