import Submission.DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import Submission.DifferentialGeometry.Topology.Manifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

theorem closure_image_interior_eq_closure_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] {M : Set X} [ChartedSpace H M] [IsManifold I 1 M] :
    closure ((Subtype.val : M → X) '' I.interior M) = closure M := by
  refine Subset.antisymm (closure_mono ?_) ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · have hdense : Dense (I.interior M) := ModelWithCorners.dense_interior I
    have hrange : (Subtype.val : M → X) '' _root_.Set.univ = M := by
      rw [Set.image_univ, Subtype.range_coe]
    refine closure_minimal ?_ isClosed_closure
    calc M = (Subtype.val : M → X) '' closure (I.interior M) := by
          rw [hdense.closure_eq, hrange]
      _ ⊆ closure ((Subtype.val : M → X) '' I.interior M) :=
          image_closure_subset_closure_image continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closure_image_interior_eq_closure_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closure_image_interior_eq_closure_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closure_image_interior_eq_closure_range ``Submission.DifferentialGeometry.Topology.Manifold.closure_image_interior_eq_closure_range

theorem isOpen_image_interior_of_isImmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    {f : M → N} (hf : _root_.Manifold.IsImmersion I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsOpen (f '' I.interior M) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  exact immersion_image_mem_nhds (hf.isImmersionAt x) hdim hx
    ((I.isOpen_interior (n := ∞) (by norm_num)).mem_nhds hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion ``Submission.DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion

end DifferentialGeometry.Topology.Manifold
