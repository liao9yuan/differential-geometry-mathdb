/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def eulerChar (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : ℤ :=
  faceEulerChar K.toPreAbstractSimplicialComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar

theorem eulerChar_eq_singular (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (k : Type) [Field k] :
    eulerChar K = Homology.eulerChar k (TopCat.of K.space) :=
  (eulerChar_geometricSpace_eq_faceEulerChar K k).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_singular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_singular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_singular ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_singular

theorem eulerChar_eq_of_isPLHomeomorphOn [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces] {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) : eulerChar K = eulerChar L := by
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of L.space) :=
      Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph
    _ = eulerChar L := (eulerChar_eq_singular L ℚ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isPLHomeomorphOn

theorem eulerChar_eq_of_isSubdivision {K K' : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite K'.faces] (hK' : IsSubdivision K' K) :
    eulerChar K' = eulerChar K := by
  rw [eulerChar_eq_singular K' ℚ, eulerChar_eq_singular K ℚ, hK'.space_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_isSubdivision

theorem eulerChar_of_isPLBall [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsPLBall n K.space) : eulerChar K = 1 := by
  obtain ⟨f, hf⟩ := hK
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of (stdSimplex ℝ (Fin (n + 1)))) :=
      (Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph).symm
    _ = 1 := eulerChar_stdSimplex n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLBall

theorem eulerChar_of_isPLSphere [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsPLSphere n K.space) : eulerChar K = 1 + (-1 : ℤ) ^ n := by
  obtain ⟨f, hf⟩ := hK
  calc
    eulerChar K = Homology.eulerChar ℚ (TopCat.of K.space) := eulerChar_eq_singular K ℚ
    _ = Homology.eulerChar ℚ (TopCat.of (stdSimplexBoundary (n + 1))) :=
      (Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph).symm
    _ = 1 + (-1 : ℤ) ^ n := eulerChar_stdSimplexBoundary n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere

theorem eulerChar_of_isPLSphere_one [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 1 K.space) : eulerChar K = 0 := by
  simpa using eulerChar_of_isPLSphere K hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_of_isPLSphere_one

def intersectionComplex (K L : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E where
  faces := K.faces ∩ L.faces
  isRelLowerSet_faces := by
    rintro s ⟨hsK, hsL⟩
    exact ⟨K.nonempty_of_mem_faces hsK, fun t hts ht =>
      ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex

theorem mem_intersectionComplex_faces_iff {K L : Geometry.SimplicialComplex ℝ E}
    {s : Finset E} : s ∈ (intersectionComplex K L).faces ↔ s ∈ K.faces ∧ s ∈ L.faces :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_intersectionComplex_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_intersectionComplex_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_intersectionComplex_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_intersectionComplex_faces_iff

theorem intersectionComplex_faces_finite (K L : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) : (intersectionComplex K L).faces.Finite :=
  hK.subset fun _ hs => hs.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.intersectionComplex_faces_finite

instance finite_intersectionComplex_faces (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : Finite (intersectionComplex K L).faces :=
  (intersectionComplex_faces_finite K L (Set.toFinite K.faces)).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_intersectionComplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_intersectionComplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_intersectionComplex_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_intersectionComplex_faces

instance finite_unionComplex_faces (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    Finite (unionComplex K L h).faces :=
  (unionComplex_faces_finite K L h (Set.toFinite K.faces) (Set.toFinite L.faces)).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_unionComplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_unionComplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_unionComplex_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_unionComplex_faces

theorem eulerChar_union_add_inter (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    eulerChar (unionComplex K L h) + eulerChar (intersectionComplex K L) =
      eulerChar K + eulerChar L := by
  have hu : (unionComplex K L h).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  have hi : (intersectionComplex K L).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  unfold eulerChar
  rw [faceEulerChar_congr hu, faceEulerChar_congr hi]
  exact faceEulerChar_sup_add_faceEulerChar_inf K.toPreAbstractSimplicialComplex
    L.toPreAbstractSimplicialComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_union_add_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_union_add_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_union_add_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_union_add_inter

end DifferentialGeometry.Topology.PiecewiseLinear
