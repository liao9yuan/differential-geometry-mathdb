import Submission.DifferentialGeometry.Topology.Embedding.Lift
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionImageNhds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace Manifold
open _root_.Manifold

section Range

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {m n : ℕ∞ω} {e : M → N} {f : N → P} {x : M}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.contMDiffAt_of_comp_of_range_mem_nhds
    (he : _root_.Manifold.IsSmoothEmbedding I J m e) (hn : n ≤ m)
    (hrange : _root_.Set.range e ∈ 𝓝 (e x)) (hfe : ContMDiffAt I K n (f ∘ e) x) :
    ContMDiffAt J K n f (e x) := by
  let U : TopologicalSpace.Opens N := ⟨interior (_root_.Set.range e), isOpen_interior⟩
  let y : U := ⟨e x, mem_interior_iff_mem_nhds.mpr hrange⟩
  have hsub : _root_.Set.range (Subtype.val : U → N) ⊆ _root_.Set.range e := by
    rintro _ ⟨z, rfl⟩
    exact interior_subset z.property
  let r : U → M := he.lift (Subtype.val : U → N) hsub
  have hr : ContMDiff J I n r :=
    (he.contMDiff_lift (contMDiff_subtype_val (I := J) (U := U)) hsub).of_le hn
  have hry : r y = x := he.isEmbedding.injective (he.comp_lift hsub y)
  have hfe' : ContMDiffAt I K n (f ∘ e) (r y) := by
    rw [hry]
    exact hfe
  have hres : ContMDiffAt J K n (fun z : U => f z.val) y := by
    apply (hfe'.comp y hr.contMDiffAt).congr_of_eventuallyEq
    filter_upwards with z
    exact congrArg f (he.comp_lift hsub z).symm
  exact contMDiffAt_subtype_iff.mp hres

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_range_mem_nhds then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_range_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_range_mem_nhds ``Submission.Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_range_mem_nhds

end Range

section Interior

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} {e : M → N} {f : N → P} {x : M}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.contMDiffAt_of_comp_of_isInteriorPoint
    (he : _root_.Manifold.IsSmoothEmbedding I J ∞ e) (hn : n ≤ ∞)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hx : I.IsInteriorPoint x)
    (hfe : ContMDiffAt I K n (f ∘ e) x) : ContMDiffAt J K n f (e x) := by
  have hrange : _root_.Set.range e ∈ 𝓝 (e x) := by
    simpa only [_root_.Set.image_univ] using
      DifferentialGeometry.Topology.immersion_image_mem_nhds
        (he.isImmersion.isImmersionAt x) hdim hx (s := _root_.Set.univ) Filter.univ_mem
  exact he.contMDiffAt_of_comp_of_range_mem_nhds hn hrange hfe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_isInteriorPoint ``Submission.Manifold.IsSmoothEmbedding.contMDiffAt_of_comp_of_isInteriorPoint

end Interior

end Manifold
