import Submission.DifferentialGeometry.Topology.Embedding.CompactFrontier
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import Submission.DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Handle (chartedSpaceOfHomeomorph isManifoldOfHomeomorph
  contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
  contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph)
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem exists_manifold_image_open_subtype (U : TopologicalSpace.Opens M) (K : Set U)
    [ChartedSpace H K] [IsManifold I ∞ K]
    (hclosed : IsClosed (Subtype.val '' K : Set M))
    (hinduced : _root_.Manifold.IsSmoothEmbedding I J ∞ (Subtype.val : K → U))
    (hinterior : (Subtype.val : K → U) '' I.interior K = interior K) :
    ∃ charts : ChartedSpace H (Subtype.val '' K : Set M),
      letI := charts
      IsManifold I ∞ (Subtype.val '' K : Set M) ∧
      _root_.Manifold.IsSmoothEmbedding I J ∞ (Subtype.val : (Subtype.val '' K : Set M) → M) ∧
      (Subtype.val : (Subtype.val '' K : Set M) → M) ''
        I.interior (Subtype.val '' K : Set M) = interior (Subtype.val '' K : Set M) ∧
      (Subtype.val : (Subtype.val '' K : Set M) → M) ''
        I.boundary (Subtype.val '' K : Set M) = frontier (Subtype.val '' K : Set M) := by
  let R : Set M := Subtype.val '' K
  let e : K ≃ₜ R := _root_.Topology.IsEmbedding.subtypeVal.homeomorphImage K
  let _ : ChartedSpace H R := chartedSpaceOfHomeomorph e.symm
  let _ : IsManifold I ∞ R := isManifoldOfHomeomorph I e.symm
  let D : R ≃ₘ⟮I, I⟯ K :=
    { toEquiv := e.symm.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e.symm I ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e.symm I ∞ }
  have hval (x : K) : (D.symm x).val = x.val.val := rfl
  have hval' (x : R) : (D x).val.val = x.val := by
    have h := hval (D x)
    have hh : x.val = (D x).val.val := by simpa only [D.symm_apply_apply] using h
    exact hh.symm
  have hinterior' : (Subtype.val : R → M) '' I.interior R = interior R := by
    rw [← D.symm.image_interior (by simp), _root_.Set.image_image]
    change (fun x : K => x.val.val) '' I.interior K = interior R
    rw [← _root_.Set.image_image, hinterior]
    exact Embedding.image_interior_of_isOpenEmbedding U.isOpenEmbedding' K
  refine ⟨inferInstance, inferInstance, ?_, hinterior', ?_⟩
  · have h := isSmoothEmbedding_diffeomorph_precomp
      (Subtype.val ∘ (Subtype.val : K → U))
      (isSmoothEmbedding_fromOpen I J U (Subtype.val : K → U) hinduced) D
    simpa only [Function.comp_def, hval'] using h
  · change (Subtype.val : R → M) '' I.boundary R = frontier R
    rw [← I.compl_interior, _root_.Set.image_compl_eq_range_sdiff_image Subtype.val_injective,
      Subtype.range_coe, hinterior', frontier, hclosed.closure_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_manifold_image_open_subtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_manifold_image_open_subtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_manifold_image_open_subtype ``Submission.DifferentialGeometry.Topology.Manifold.exists_manifold_image_open_subtype

end DifferentialGeometry.Topology.Manifold
