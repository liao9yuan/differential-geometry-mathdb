import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary
import Submission.DifferentialGeometry.Topology.Simplex.VertexMap
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module _root_.Set
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

abbrev Square : Type := Fin 2 → unitInterval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Square ``Submission.DifferentialGeometry.Topology.Square

theorem square_nullhomotopic : (ContinuousMap.id Square).Nullhomotopic := by
  refine ⟨fun _ => (0 : unitInterval), ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => fun i => ⟨(1 - (p.1 : ℝ)) * (p.2 i : ℝ), ?_, ?_⟩, ?_⟩
    ?_ ?_⟩⟩
  · exact mul_nonneg (by linarith [(p.1).property.1, (p.1).property.2]) (p.2 i).property.1
  · nlinarith [(p.1).property.1, (p.1).property.2, (p.2 i).property.1, (p.2 i).property.2]
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have h1 : Continuous fun p : unitInterval × Square => (1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : unitInterval × Square => ((p.2 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact h1.mul h2
  · intro v
    funext i
    apply Subtype.ext
    simp
  · intro v
    funext i
    apply Subtype.ext
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.square_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.square_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.square_nullhomotopic ``Submission.DifferentialGeometry.Topology.square_nullhomotopic

theorem square_contractible : ContractibleSpace Square :=
  (contractible_iff_id_nullhomotopic Square).mpr square_nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.square_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.square_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.square_contractible ``Submission.DifferentialGeometry.Topology.square_contractible

theorem subsingleton_homology_two_square :
    Subsingleton (integralSingularHomology 2 Square) :=
  letI := square_contractible
  integralSingularHomology_subsingleton_of_contractible 2 (by omega) Square

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_homology_two_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_homology_two_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_homology_two_square ``Submission.DifferentialGeometry.Topology.subsingleton_homology_two_square

def halfPoint : unitInterval := ⟨1 / 2, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.halfPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.halfPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.halfPoint ``Submission.DifferentialGeometry.Topology.halfPoint

def squarePoint (a b : unitInterval) : Square := ![a, b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squarePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squarePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squarePoint ``Submission.DifferentialGeometry.Topology.squarePoint

def squareOrigin : Square := squarePoint 0 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareOrigin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareOrigin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareOrigin ``Submission.DifferentialGeometry.Topology.squareOrigin
def squareEast : Square := squarePoint 1 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareEast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareEast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareEast ``Submission.DifferentialGeometry.Topology.squareEast
def squareNorthEast : Square := squarePoint 1 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareNorthEast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareNorthEast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareNorthEast ``Submission.DifferentialGeometry.Topology.squareNorthEast
def squareNorth : Square := squarePoint 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareNorth ``Submission.DifferentialGeometry.Topology.squareNorth
def squareMidEast : Square := squarePoint halfPoint 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareMidEast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareMidEast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareMidEast ``Submission.DifferentialGeometry.Topology.squareMidEast
def squareMidNorth : Square := squarePoint halfPoint 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareMidNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareMidNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareMidNorth ``Submission.DifferentialGeometry.Topology.squareMidNorth

theorem squarePoint_zero (a b : unitInterval) : squarePoint a b 0 = a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squarePoint_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squarePoint_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squarePoint_zero ``Submission.DifferentialGeometry.Topology.squarePoint_zero
theorem squarePoint_one (a b : unitInterval) : squarePoint a b 1 = b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squarePoint_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squarePoint_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squarePoint_one ``Submission.DifferentialGeometry.Topology.squarePoint_one

def squareAffineMap (n : ℕ) (v : Fin (n + 1) → Square) :
    C(stdSimplex ℝ (Fin (n + 1)), Square) where
  toFun t := fun i => ⟨Simplex.vertexMap (fun j => (v j i : ℝ)) t, by
    refine convexHull_min ?_ (convex_Icc 0 1)
      (Simplex.vertexMap_mem_convexHull (fun j => (v j i : ℝ)) t)
    rintro x ⟨j, rfl⟩
    exact (v j i).property⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (Simplex.vertexMap (fun j => (v j i : ℝ))).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap ``Submission.DifferentialGeometry.Topology.squareAffineMap

theorem squareAffineMap_apply_coe (n : ℕ) (v : Fin (n + 1) → Square)
    (t : stdSimplex ℝ (Fin (n + 1))) (i : Fin 2) :
    ((squareAffineMap n v t i : unitInterval) : ℝ) = ∑ j, (t.val j) * (v j i : ℝ) := by
  simp [squareAffineMap, Simplex.vertexMap_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap_apply_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap_apply_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap_apply_coe ``Submission.DifferentialGeometry.Topology.squareAffineMap_apply_coe

def squareAffineSimplex (n : ℕ) (v : Fin (n + 1) → Square) :
    integralSingularSimplex n Square :=
  (integralSingularSimplexEquiv n Square).symm (squareAffineMap n v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineSimplex ``Submission.DifferentialGeometry.Topology.squareAffineSimplex

@[simp] theorem squareAffineSimplex_val (n : ℕ) (v : Fin (n + 1) → Square) :
    (TopCat.of Square).toSSetObjEquiv (Opposite.op ⦋n⦌) (squareAffineSimplex n v) =
      squareAffineMap n v :=
  Equiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineSimplex_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineSimplex_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineSimplex_val ``Submission.DifferentialGeometry.Topology.squareAffineSimplex_val

theorem squareAffineSimplex_face_eval (n : ℕ) (v : Fin (n + 2) → Square)
    (i : Fin (n + 2)) (t : stdSimplex ℝ (Fin (n + 1))) (i' : Fin 2) :
    (((integralSingularSimplexEquiv n Square)
        ((TopCat.toSSet.obj (TopCat.of Square)).δ i (squareAffineSimplex (n + 1) v))) t i'
        : ℝ) =
      (((integralSingularSimplexEquiv n Square)
        (squareAffineSimplex n (fun j => v (i.succAbove j)))) t i' : ℝ) := by
  simp only [integralSingularSimplexEquiv]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [squareAffineSimplex_val, squareAffineSimplex_val]
  exact Simplex.vertexMap_map (fun j => (v j i' : ℝ)) i.succAbove t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineSimplex_face_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineSimplex_face_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineSimplex_face_eval ``Submission.DifferentialGeometry.Topology.squareAffineSimplex_face_eval

theorem squareAffineSimplex_face (n : ℕ) (v : Fin (n + 2) → Square) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of Square)).δ i (squareAffineSimplex (n + 1) v) =
      squareAffineSimplex n (fun j => v (i.succAbove j)) := by
  apply (integralSingularSimplexEquiv n Square).injective
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i'
  exact Subtype.ext (squareAffineSimplex_face_eval n v i t i')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineSimplex_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineSimplex_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineSimplex_face ``Submission.DifferentialGeometry.Topology.squareAffineSimplex_face

theorem squareTriangleFace_zero (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((0 : Fin 3).succAbove j)) = ![Q, R] := by
  funext j
  fin_cases j <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareTriangleFace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareTriangleFace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareTriangleFace_zero ``Submission.DifferentialGeometry.Topology.squareTriangleFace_zero

theorem squareTriangleFace_one (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((1 : Fin 3).succAbove j)) = ![P, R] := by
  funext j
  fin_cases j <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareTriangleFace_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareTriangleFace_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareTriangleFace_one ``Submission.DifferentialGeometry.Topology.squareTriangleFace_one

theorem squareTriangleFace_two (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((2 : Fin 3).succAbove j)) = ![P, Q] := by
  funext j
  fin_cases j <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareTriangleFace_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareTriangleFace_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareTriangleFace_two ``Submission.DifferentialGeometry.Topology.squareTriangleFace_two

def squareTriangleChain (P Q R : Square) : (integralSingularChains Square).X 2 :=
  integralSimplexChain 2 (squareAffineSimplex 2 ![P, Q, R])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareTriangleChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareTriangleChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareTriangleChain ``Submission.DifferentialGeometry.Topology.squareTriangleChain

def squareSegmentChain (P Q : Square) : (integralSingularChains Square).X 1 :=
  integralSimplexChain 1 (squareAffineSimplex 1 ![P, Q])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSegmentChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSegmentChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSegmentChain ``Submission.DifferentialGeometry.Topology.squareSegmentChain

theorem squareTriangleChain_boundary (P Q R : Square) :
    (integralSingularChains Square).d 2 1 (squareTriangleChain P Q R) =
      squareSegmentChain Q R - squareSegmentChain P R + squareSegmentChain P Q := by
  rw [squareTriangleChain, integralSimplexChain_boundary]
  rw [Fin.sum_univ_three]
  rw [squareAffineSimplex_face, squareAffineSimplex_face, squareAffineSimplex_face]
  rw [squareTriangleFace_zero, squareTriangleFace_one, squareTriangleFace_two]
  norm_num
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareTriangleChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareTriangleChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareTriangleChain_boundary ``Submission.DifferentialGeometry.Topology.squareTriangleChain_boundary

def squareFundamentalChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareEast squareNorthEast -
    squareTriangleChain squareOrigin squareNorth squareNorthEast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalChain ``Submission.DifferentialGeometry.Topology.squareFundamentalChain

def squareLeftHalfChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareMidEast squareMidNorth -
    squareTriangleChain squareOrigin squareNorth squareMidNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareLeftHalfChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareLeftHalfChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareLeftHalfChain ``Submission.DifferentialGeometry.Topology.squareLeftHalfChain

def squareRightHalfChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareMidEast squareEast squareNorthEast -
    squareTriangleChain squareMidEast squareMidNorth squareNorthEast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareRightHalfChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareRightHalfChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareRightHalfChain ``Submission.DifferentialGeometry.Topology.squareRightHalfChain

def squareCornerChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareMidEast squareEast -
    squareTriangleChain squareNorth squareMidNorth squareNorthEast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareCornerChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareCornerChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareCornerChain ``Submission.DifferentialGeometry.Topology.squareCornerChain

theorem square_fold_identity :
    (integralSingularChains Square).d 2 1
      (squareFundamentalChain - squareLeftHalfChain - squareRightHalfChain +
        squareCornerChain) = 0 := by
  simp only [map_sub, map_add]
  simp only [squareFundamentalChain, squareLeftHalfChain, squareRightHalfChain, squareCornerChain,
    map_sub]
  rw [squareTriangleChain_boundary, squareTriangleChain_boundary, squareTriangleChain_boundary,
    squareTriangleChain_boundary, squareTriangleChain_boundary, squareTriangleChain_boundary,
    squareTriangleChain_boundary, squareTriangleChain_boundary]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.square_fold_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.square_fold_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.square_fold_identity ``Submission.DifferentialGeometry.Topology.square_fold_identity

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]
variable {Z : Type u} [TopologicalSpace Z]

def singularSimplexImage (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplex n Y :=
  ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm
    (f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexImage ``Submission.DifferentialGeometry.Topology.singularSimplexImage

@[simp] theorem singularSimplexImage_val (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    (TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌) (singularSimplexImage n f σ) =
      f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexImage_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexImage_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexImage_val ``Submission.DifferentialGeometry.Topology.singularSimplexImage_val

theorem singularSimplexImage_face (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) :
    singularSimplexImage n f ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (TopCat.toSSet.obj (TopCat.of Y)).δ i (singularSimplexImage (n + 1) f σ) := by
  apply ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImage_val]
  ext t
  simp only [ContinuousMap.comp_apply]
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply, singularSimplexImage_val]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexImage_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexImage_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexImage_face ``Submission.DifferentialGeometry.Topology.singularSimplexImage_face

theorem singularSimplexImage_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) (σ : integralSingularSimplex n X) :
    singularSimplexImage n (g.comp f) σ = singularSimplexImage n g (singularSimplexImage n f σ) := by
  apply ((TopCat.of Z).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImage_val, singularSimplexImage_val, singularSimplexImage_val, ContinuousMap.comp_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexImage_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexImage_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexImage_comp ``Submission.DifferentialGeometry.Topology.singularSimplexImage_comp

def singularChainImage (n : ℕ) (f : C(X, Y)) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains Y).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains Y).X n) ℕ
    (fun σ => integralSimplexChain n (singularSimplexImage n f σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularChainImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularChainImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularChainImage ``Submission.DifferentialGeometry.Topology.singularChainImage

theorem singularChainImage_simplex (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    singularChainImage n f (integralSimplexChain n σ) =
      integralSimplexChain n (singularSimplexImage n f σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularChainImage_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularChainImage_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularChainImage_simplex ``Submission.DifferentialGeometry.Topology.singularChainImage_simplex

theorem singularChainImage_d (n : ℕ) (f : C(X, Y)) :
    (singularChainImage n f).comp (((integralSingularChains X).d (n + 1) n).hom) =
      (((integralSingularChains Y).d (n + 1) n).hom).comp (singularChainImage (n + 1) f) := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
  rw [integralSimplexChain_boundary, map_sum]
  conv_rhs => rw [singularChainImage_simplex, integralSimplexChain_boundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, singularChainImage_simplex, singularSimplexImage_face]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularChainImage_d then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularChainImage_d"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularChainImage_d ``Submission.DifferentialGeometry.Topology.singularChainImage_d

theorem singularChainImage_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainImage n (g.comp f) = (singularChainImage n g).comp (singularChainImage n f) := by
  apply (integralSingularChainBasis n X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, singularChainImage_simplex]
  rw [singularSimplexImage_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularChainImage_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularChainImage_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularChainImage_comp ``Submission.DifferentialGeometry.Topology.singularChainImage_comp

end DifferentialGeometry.Topology
