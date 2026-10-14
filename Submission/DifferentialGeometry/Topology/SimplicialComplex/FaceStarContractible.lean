import Submission.DifferentialGeometry.Topology.SimplicialComplex.FaceStar
import Submission.DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (s : Finset E) (hs : s ∈ K.faces)

include hs


theorem starConvex_faceOpenStar : StarConvex ℝ (s.centroid ℝ id) (faceOpenStar K s) := by
  intro x hx a b ha hb hab
  obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  have hst := subset_of_mem_faceOpenStar K s hx ht hxt
  have hbt : s.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    convexHull_mono (show (s : Set E) ⊆ t from hst)
      (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  let xx : K.space := ⟨x, hx.1⟩
  have hc : a • s.centroid ℝ id + b • x ∈ K.space :=
    Geometry.SimplicialComplex.convexHull_subset_space ht
      ((convex_convexHull ℝ (t : Set E)) hbt hxt ha hb hab)
  apply (mem_faceOpenStar_iff K s ⟨_, hc⟩).mpr
  intro p hp
  have hxpos := (mem_faceOpenStar_iff K s xx).mp hx p hp
  have hbpos : 0 < (s.card : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr
    (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)))
  have hv := vertexFunction_combo K (fun q ↦ if q = p then 1 else 0)
    ht (geometricFaceBarycenter K s hs) xx hbt hxt ha hb hab
  change vertexHeight K p ⟨a • s.centroid ℝ id + b • x, _⟩ =
    a * vertexHeight K p (geometricFaceBarycenter K s hs) + b * vertexHeight K p xx at hv
  rw [vertexHeight_geometricFaceBarycenter, if_pos hp] at hv
  rw [hv]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by simpa only [hb0, add_zero] using hab
    simpa only [hb0, ha1, one_mul, _root_.MulZeroClass.zero_mul, add_zero] using hbpos
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hbpos.le)
      (mul_pos (lt_of_le_of_ne hb (Ne.symm hb0)) hxpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.starConvex_faceOpenStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.starConvex_faceOpenStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.starConvex_faceOpenStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.starConvex_faceOpenStar


def faceOpenStarContraction :
    ContinuousMap.Homotopy (ContinuousMap.id (faceOpenStar K s))
      (ContinuousMap.const (faceOpenStar K s)
        ⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩) where
  toFun z := ⟨z.1.val • s.centroid ℝ id + (1 - z.1.val) • z.2.val,
    starConvex_faceOpenStar K s hs z.2.prop z.1.prop.1
      (sub_nonneg.mpr z.1.prop.2) (add_sub_cancel _ _)⟩
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction


@[simp]
theorem faceOpenStarContraction_apply (a : unitInterval) (x : faceOpenStar K s) :
    (faceOpenStarContraction K s hs (a, x)).val =
      a.val • s.centroid ℝ id + (1 - a.val) • x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceOpenStarContraction_apply


theorem contractibleSpace_faceOpenStar : ContractibleSpace (faceOpenStar K s) :=
  (starConvex_faceOpenStar K s hs).contractibleSpace
    ⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.contractibleSpace_faceOpenStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.contractibleSpace_faceOpenStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.contractibleSpace_faceOpenStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.contractibleSpace_faceOpenStar


theorem finiteHomologyType_faceOpenStar (k : Type u) [Field k] :
    DifferentialGeometry.Homology.finiteHomologyType k (TopCat.of (faceOpenStar K s)) := by
  let := contractibleSpace_faceOpenStar K s hs
  exact DifferentialGeometry.Homology.finiteHomologyType_of_contractible k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_faceOpenStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_faceOpenStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_faceOpenStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_faceOpenStar


theorem eulerChar_faceOpenStar (k : Type u) [Field k] :
    DifferentialGeometry.Homology.eulerChar k (TopCat.of (faceOpenStar K s)) = 1 := by
  let := contractibleSpace_faceOpenStar K s hs
  exact DifferentialGeometry.Homology.eulerChar_of_contractible k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_faceOpenStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.eulerChar_faceOpenStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.eulerChar_faceOpenStar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.eulerChar_faceOpenStar

end DifferentialGeometry.Topology.SimplicialComplex
