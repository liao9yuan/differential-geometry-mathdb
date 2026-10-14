import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace Manifold
open _root_.Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {f : M → N} {x : M}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range
    (hf : _root_.Manifold.IsSmoothEmbedding I J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hx : f x ∈ interior (_root_.Set.range f)) (hfx : J.IsInteriorPoint (f x)) :
    I.IsInteriorPoint x := by
  let U : TopologicalSpace.Opens N := ⟨interior (_root_.Set.range f), isOpen_interior⟩
  let y : U := ⟨f x, hx⟩
  have hsub : _root_.Set.range (Subtype.val : U → N) ⊆ _root_.Set.range f := by
    rintro _ ⟨z, rfl⟩
    exact interior_subset z.property
  let g : U → M := hf.lift (Subtype.val : U → N) hsub
  have hg : ContMDiff J I ∞ g :=
    hf.contMDiff_lift (contMDiff_subtype_val (I := J) (U := U)) hsub
  have hgy : g y = x := hf.isEmbedding.injective (hf.comp_lift hsub y)
  have hcomp : f ∘ g = (Subtype.val : U → N) := funext (hf.comp_lift hsub)
  have hfull : Function.Injective (mfderiv J J (f ∘ g) y) := by
    rw [hcomp]
    exact ((IsSmoothEmbedding.of_opens (I := J) (n := ∞) U).isImmersion.isImmersionAt y).injective_mfderiv
      (by simp)
  rw [mfderiv_comp y (hf.contMDiff.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))] at hfull
  have hinj : Function.Injective (mfderiv J I g y) := Function.Injective.of_comp hfull
  let L : F →L[ℝ] E := mfderiv J I g y
  have hsurj : Function.Surjective (mfderiv J I g y) :=
    (L.toLinearMap.linearEquivOfInjective hinj hdim.symm).surjective
  have hi : I.IsInteriorPoint (g y) :=
    (hg.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv hsurj
      (J.isInteriorPoint_iff_isInteriorPoint_val.mpr hfx)
  rwa [hgy] at hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range ``Submission.Manifold.IsSmoothEmbedding.isInteriorPoint_of_mem_interior_range

end Manifold
