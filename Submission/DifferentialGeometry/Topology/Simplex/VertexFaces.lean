import Submission.DifferentialGeometry.Topology.Simplex.VertexHomeomorphism
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Finset
namespace DifferentialGeometry.Simplex
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vertexMap_mem_convexHull_image_iff {v : ι → E} (hv : AffineIndependent ℝ v)
    (s : Set ι) (x : stdSimplex ℝ ι) :
    vertexMap v x ∈ convexHull ℝ (v '' s) ↔ ∀ i ∉ s, x.val i = 0 := by
  classical
  constructor
  · intro hx i hi
    apply hv.eq_zero_of_affineCombination_mem_affineSpan x.prop.2 (s := s)
      (i := i) _ (_root_.Finset.mem_univ i) hi
    rw [Finset.affineCombination_eq_linear_combination _ _ _ x.prop.2]
    exact convexHull_subset_affineSpan (v '' s) hx
  · intro hx
    have hs : ∑ i ∈ univ.filter (· ∈ s), x.val i = 1 := by
      rw [_root_.Finset.sum_subset (_root_.Finset.filter_subset _ _) (fun i _ hi => hx i (by simpa using hi))]
      exact x.prop.2
    have he : ∑ i ∈ univ.filter (· ∈ s), x.val i • v i = vertexMap v x := by
      apply _root_.Finset.sum_subset (_root_.Finset.filter_subset _ _)
      intro i _ hi
      rw [hx i (by simpa using hi), zero_smul]
    rw [← he]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => x.prop.1 i) hs
      (fun i hi => subset_convexHull ℝ _ ⟨i, (mem_filter.mp hi).2, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_mem_convexHull_image_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_mem_convexHull_image_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_mem_convexHull_image_iff ``Submission.DifferentialGeometry.Simplex.vertexMap_mem_convexHull_image_iff


theorem vertexMap_mem_proper_face_iff {v : ι → E} (hv : AffineIndependent ℝ v)
    (x : stdSimplex ℝ ι) :
    (∃ s : Finset ι, s ≠ Finset.univ ∧ vertexMap v x ∈ convexHull ℝ (v '' (s : Set ι))) ↔
      x ∈ boundary ι := by
  classical
  constructor
  · rintro ⟨s, hs, hx⟩
    have he : ∃ i, i ∉ s := by
      by_contra h
      push Not at h
      exact hs (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨i, hi⟩ := he
    exact ⟨i, (vertexMap_mem_convexHull_image_iff hv (s : Set ι) x).mp hx i hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Finset.univ.erase i, ?_, ?_⟩
    · exact (_root_.Finset.erase_ssubset (_root_.Finset.mem_univ i)).ne
    · apply (vertexMap_mem_convexHull_image_iff hv _ x).mpr
      intro j hj
      have hji : j = i := by simpa using hj
      simpa only [hji] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.vertexMap_mem_proper_face_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.vertexMap_mem_proper_face_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.vertexMap_mem_proper_face_iff ``Submission.DifferentialGeometry.Simplex.vertexMap_mem_proper_face_iff

end DifferentialGeometry.Simplex
