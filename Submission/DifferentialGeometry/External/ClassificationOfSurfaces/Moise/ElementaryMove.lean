/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Submission.DifferentialGeometry.External.ClassificationOfSurfaces.Moise.AmbientHomeomorph
import Submission.DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The elementary supported move in polygonal Schoenflies

This is the normalized version of Moise Figure 3.3.  Four triangles fan from a point `(0,a)`
inside a fixed diamond.  Repositioning the fan point while fixing the four diamond vertices gives
a PL homeomorphism of the diamond, and hence an ambient homeomorphism by identity extension.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Vertices `0,1,2,3` are left, right, top, bottom; vertex `4` is the fan point. -/
def diamondFanPosition (a : ℝ) : Fin 5 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 2, planePoint 0 (-2), planePoint 0 a]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition

/-- The four maximal triangles in the fan of the diamond. -/
def diamondFanTriangles : Finset (Finset (Fin 5)) :=
  {{0, 4, 2}, {1, 2, 4}, {0, 3, 4}, {1, 4, 3}}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanTriangles then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanTriangles"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanTriangles ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanTriangles

@[simp] theorem diamondFanPosition_apply_zero (a : ℝ) :
    diamondFanPosition a 0 = planePoint (-1) 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_zero then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_zero ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_zero

@[simp] theorem diamondFanPosition_apply_one (a : ℝ) :
    diamondFanPosition a 1 = planePoint 1 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_one then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_one ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_one

@[simp] theorem diamondFanPosition_apply_two (a : ℝ) :
    diamondFanPosition a 2 = planePoint 0 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_two then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_two"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_two ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_two

@[simp] theorem diamondFanPosition_apply_three (a : ℝ) :
    diamondFanPosition a 3 = planePoint 0 (-2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_three then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_three"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_three ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_three

@[simp] theorem diamondFanPosition_apply_four (a : ℝ) :
    diamondFanPosition a 4 = planePoint 0 a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_four then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_four"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_four ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_apply_four

theorem diamondFanPosition_injective {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    Function.Injective (diamondFanPosition a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [diamondFanPosition, planePoint] at hij ⊢
  all_goals linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_injective then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_injective ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPosition_injective

private theorem affineIndependent_finset_of_range {V : Type}
    (position : V → Plane) {t : Finset V} (p : Fin 3 → V)
    (hp : AffineIndependent ℝ (position ∘ p)) (hrange : Set.range p = (t : Set V)) :
    AffineIndependent ℝ fun v : t => position v := by
  classical
  let eFun : Fin 3 → t := fun i => ⟨p i, by
    change p i ∈ (t : Set V)
    rw [← hrange]
    exact Set.mem_range_self i⟩
  have heBijective : Function.Bijective eFun := by
    constructor
    · intro i j hij
      apply hp.injective
      exact congrArg (fun v : t => position v) hij
    · rintro ⟨v, hv⟩
      have : v ∈ Set.range p := by rwa [hrange]
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, rfl⟩
  let e : Fin 3 ≃ t := Equiv.ofBijective eFun heBijective
  apply (affineIndependent_equiv e).mp
  convert hp using 1
  funext i
  rfl

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_finset_of_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_finset_of_range target :: scope.openDecls } }

theorem diamondFan_affineIndependent {a : ℝ} (ha0 : -2 < a) (ha2 : a < 2)
    {t : Finset (Fin 5)} (ht : t ∈ diamondFanTriangles) :
    AffineIndependent ℝ fun v : t => diamondFanPosition a v := by
  simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![0, 4, 2]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 0,
          diamondFanPosition a 4, diamondFanPosition a 2] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_zero, diamondFanPosition_apply_four,
          diamondFanPosition_apply_two, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![1, 2, 4]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 1,
          diamondFanPosition a 2, diamondFanPosition a 4] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_one, diamondFanPosition_apply_two,
          diamondFanPosition_apply_four, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![0, 3, 4]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 0,
          diamondFanPosition a 3, diamondFanPosition a 4] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_zero, diamondFanPosition_apply_three,
          diamondFanPosition_apply_four, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range (diamondFanPosition a) ![1, 4, 3]
    · have h : AffineIndependent ℝ ![diamondFanPosition a 1,
          diamondFanPosition a 4, diamondFanPosition a 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [diamondFanPosition_apply_one, diamondFanPosition_apply_four,
          diamondFanPosition_apply_three, planePoint_apply_zero, planePoint_apply_one,
          PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_affineIndependent then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_affineIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_affineIndependent ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_affineIndependent

/-- Vertical separator for the upper and lower pairs of left/right fan triangles. -/
noncomputable def diamondVerticalAffine : Plane →ᵃ[ℝ] ℝ := cartesianX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine

/-- Separator through the left vertex and fan point. -/
noncomputable def diamondLeftAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a • cartesianX - cartesianY + AffineMap.const ℝ Plane a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine

/-- Separator through the right vertex and fan point. -/
noncomputable def diamondRightAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a • cartesianX + cartesianY - AffineMap.const ℝ Plane a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine

/-- Separator of the upper-left and lower-right opposite fan triangles. -/
noncomputable def diamondDownDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - cartesianY + AffineMap.const ℝ Plane a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine

/-- Separator of the upper-right and lower-left opposite fan triangles. -/
noncomputable def diamondUpDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + cartesianY - AffineMap.const ℝ Plane a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine

@[simp] theorem diamondVerticalAffine_apply (x y : ℝ) :
    diamondVerticalAffine (planePoint x y) = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondVerticalAffine_apply

@[simp] theorem diamondLeftAffine_apply (a x y : ℝ) :
    diamondLeftAffine a (planePoint x y) = a * x - y + a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftAffine_apply

@[simp] theorem diamondRightAffine_apply (a x y : ℝ) :
    diamondRightAffine a (planePoint x y) = a * x + y - a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightAffine_apply

@[simp] theorem diamondDownDiagonalAffine_apply (a x y : ℝ) :
    diamondDownDiagonalAffine a (planePoint x y) = x - y + a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondDownDiagonalAffine_apply

@[simp] theorem diamondUpDiagonalAffine_apply (a x y : ℝ) :
    diamondUpDiagonalAffine a (planePoint x y) = x + y - a := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondUpDiagonalAffine_apply

/-- Splitting one edge of a nondegenerate triangle at an interior parameter covers the original
triangle by the two resulting triangles. -/
theorem triangle_edge_split_union (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    convexHull ℝ (Set.range ![p 0, p 2, AffineMap.lineMap (p 0) (p 1) c]) ∪
        convexHull ℝ (Set.range ![p 1, p 2, AffineMap.lineMap (p 0) (p 1) c]) =
      convexHull ℝ (Set.range p) := by
  let s := standardTrianglePosition
  let e := triangleAffineEquiv s p standardTrianglePosition_affineIndependent hp
  have href := referenceEdgeSplit_union c hc0 hc1
  have hline : AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c = planePoint c 0 := by
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply, planePoint]
  have hcarrier0 :
      referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set _) =
        Set.range ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c] := by
    ext x
    change x ∈ referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set _) ↔
      x ∈ Set.range ![planePoint 0 0, planePoint 0 1,
        AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c]
    rw [hline]
    simp [referenceEdgeSplitPosition, planePoint]
    tauto
  have hcarrier1 :
      referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set _) =
        Set.range ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c] := by
    ext x
    change x ∈ referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set _) ↔
      x ∈ Set.range ![planePoint 1 0, planePoint 0 1,
        AffineMap.lineMap (planePoint 0 0) (planePoint 1 0) c]
    rw [hline]
    simp [referenceEdgeSplitPosition, planePoint]
    tauto
  have href' :
      convexHull ℝ (Set.range ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c]) ∪
          convexHull ℝ (Set.range ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c]) =
        convexHull ℝ (Set.range s) := by
    have href0 :
        convexHull ℝ (referenceEdgeSplitPosition c ''
            (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
          convexHull ℝ (referenceEdgeSplitPosition c ''
            (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
          convexHull ℝ (Set.range standardTrianglePosition) := by
      calc
        convexHull ℝ (referenceEdgeSplitPosition c ''
              (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
            convexHull ℝ (referenceEdgeSplitPosition c ''
              (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
            ⋃ t ∈ referenceEdgeSplitTriangles,
              convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set _)) := by
                ext x
                simp only [Set.mem_union, Set.mem_iUnion]
                constructor
                · rintro (hx | hx)
                  · exact ⟨{0, 2, 3}, by simp [referenceEdgeSplitTriangles], hx⟩
                  · exact ⟨{1, 2, 3}, by simp [referenceEdgeSplitTriangles], hx⟩
                · rintro ⟨t, ht, hxt⟩
                  simp only [referenceEdgeSplitTriangles, Finset.mem_insert,
                    Finset.mem_singleton] at ht
                  rcases ht with rfl | rfl
                  · exact Or.inl hxt
                  · exact Or.inr hxt
        _ = convexHull ℝ (Set.range standardTrianglePosition) := by
          simpa only [standardTrianglePosition] using href
    rw [hcarrier0, hcarrier1] at href0
    simpa [s] using href0
  have hImageHull (r : Fin 3 → Plane) :
      e '' convexHull ℝ (Set.range r) = convexHull ℝ (Set.range (e ∘ r)) := by
    change e.toAffineMap '' convexHull ℝ (Set.range r) = _
    rw [e.toAffineMap.image_convexHull]
    congr 1
    ext x
    simp [Set.mem_image]
  have himage := congrArg (fun A : Set Plane => e '' A) href'
  rw [Set.image_union, hImageHull, hImageHull, hImageHull] at himage
  have hcomp0 : e ∘ ![s 0, s 2, AffineMap.lineMap (s 0) (s 1) c] =
      ![p 0, p 2, AffineMap.lineMap (p 0) (p 1) c] := by
    funext i
    fin_cases i
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 0
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 2
    · exact triangleAffineEquiv_apply_lineMap s p
        standardTrianglePosition_affineIndependent hp 0 1 c
  have hcomp1 : e ∘ ![s 1, s 2, AffineMap.lineMap (s 0) (s 1) c] =
      ![p 1, p 2, AffineMap.lineMap (p 0) (p 1) c] := by
    funext i
    fin_cases i
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 1
    · exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp 2
    · exact triangleAffineEquiv_apply_lineMap s p
        standardTrianglePosition_affineIndependent hp 0 1 c
  have hcomp : e ∘ s = p := by
    funext i
    exact triangleAffineEquiv_apply s p standardTrianglePosition_affineIndependent hp i
  rw [hcomp0, hcomp1, hcomp] at himage
  exact himage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.triangle_edge_split_union then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.triangle_edge_split_union"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.triangle_edge_split_union ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.triangle_edge_split_union

/-- The left triangular half of the fixed diamond. -/
def diamondLeftRegion : Set Plane :=
  convexHull ℝ (Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftRegion then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftRegion ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeftRegion

/-- The right triangular half of the fixed diamond. -/
def diamondRightRegion : Set Plane :=
  convexHull ℝ (Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightRegion then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightRegion ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRightRegion

/-- The fixed closed patch supporting the elementary move. -/
def diamondPatch : Set Plane := diamondLeftRegion ∪ diamondRightRegion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch

theorem isClosed_diamondPatch : IsClosed diamondPatch := by
  apply IsClosed.union
  · exact (Set.finite_range _).isClosed_convexHull ℝ
  · exact (Set.finite_range _).isClosed_convexHull ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.isClosed_diamondPatch then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.isClosed_diamondPatch"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.isClosed_diamondPatch ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.isClosed_diamondPatch

private theorem diamondCenter_lineMap (a : ℝ) :
    AffineMap.lineMap (planePoint 0 2) (planePoint 0 (-2)) ((2 - a) / 4) =
      planePoint 0 a := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply, planePoint] ; ring

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondCenter_lineMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondCenter_lineMap target :: scope.openDecls } }

private theorem diamondLeft_affineIndependent :
    AffineIndependent ℝ ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [planePoint, PiLp.sub_apply]

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeft_affineIndependent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondLeft_affineIndependent target :: scope.openDecls } }

private theorem diamondRight_affineIndependent :
    AffineIndependent ℝ ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [planePoint, PiLp.sub_apply]

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRight_affineIndependent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondRight_affineIndependent target :: scope.openDecls } }

theorem diamondFan_left_union {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∪
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      diamondLeftRegion := by
  have hc0 : 0 < (2 - a) / 4 := by linarith
  have hc1 : (2 - a) / 4 < 1 := by linarith
  have hsplit := triangle_edge_split_union
    ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0]
    diamondLeft_affineIndependent ((2 - a) / 4) hc0 hc1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hsplit
  rw [diamondCenter_lineMap] at hsplit
  have htop : diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint (-1) 0, planePoint 0 2} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have hbottom : diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint (-1) 0, planePoint 0 (-2)} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have houter : Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint (-1) 0] =
      ({planePoint (-1) 0, planePoint 0 (-2), planePoint 0 2} : Set Plane) := by
    ext x
    simp
  rw [htop, hbottom, diamondLeftRegion, houter]
  simpa using hsplit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_left_union then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_left_union"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_left_union ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_left_union

theorem diamondFan_right_union {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∪
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      diamondRightRegion := by
  have hc0 : 0 < (2 - a) / 4 := by linarith
  have hc1 : (2 - a) / 4 < 1 := by linarith
  have hsplit := triangle_edge_split_union
    ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0]
    diamondRight_affineIndependent ((2 - a) / 4) hc0 hc1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hsplit
  rw [diamondCenter_lineMap] at hsplit
  have htop : diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint 1 0, planePoint 0 2} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have hbottom : diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _) =
      ({planePoint 0 a, planePoint 1 0, planePoint 0 (-2)} : Set Plane) := by
    ext x
    simp [diamondFanPosition]
    tauto
  have houter : Set.range ![planePoint 0 2, planePoint 0 (-2), planePoint 1 0] =
      ({planePoint 1 0, planePoint 0 (-2), planePoint 0 2} : Set Plane) := by
    ext x
    simp
  rw [htop, hbottom, diamondRightRegion, houter]
  simpa using hsplit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_right_union then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_right_union"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_right_union ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_right_union

private theorem diamondFan_inter_02_12 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {1, 2, 4} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 4, 2} {1, 2, 4} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp at hv ⊢

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_12
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_12 target :: scope.openDecls } }

private theorem diamondFan_inter_03_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 3, 4} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 3, 4} {1, 4, 3} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp at hv ⊢

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_03_13
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_03_13 target :: scope.openDecls } }

private theorem diamondFan_inter_02_03 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {0, 3, 4} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {0, 4, 2} {0, 3, 4} (-diamondLeftAffine a)
  all_goals
    intro v hv
    fin_cases v <;> simp [diamondLeftAffine_apply] at hv ⊢ ; linarith

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_03
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_03 target :: scope.openDecls } }

private theorem diamondFan_inter_12_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({1, 2, 4} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (diamondFanPosition a)
    (diamondFanPosition_injective ha0 ha1) {1, 2, 4} {1, 4, 3} (diamondRightAffine a)
  all_goals
    intro v hv
    fin_cases v <;> simp [diamondRightAffine_apply] at hv ⊢ ; linarith

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_12_13
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_12_13 target :: scope.openDecls } }

private theorem diamondFan_inter_02_13 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({0, 4, 2} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({1, 4, 3} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({0, 4, 2} : Finset (Fin 5)) ∩ {1, 4, 3} : Finset (Fin 5)) : Set _)) := by
  let s : Finset (Fin 5) := {0, 4, 2}
  let t : Finset (Fin 5) := {1, 4, 3}
  let upperEdge : Finset (Fin 5) := {4, 2}
  let lowerEdge : Finset (Fin 5) := {4, 3}
  have hUpper :
      convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
          {p | (-diamondVerticalAffine) p = 0} =
        convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (s.image (diamondFanPosition a)) (-diamondVerticalAffine) (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [s] at hv ⊢)
    have hfilter : (s.image (diamondFanPosition a)).filter
        (fun p => (-diamondVerticalAffine) p = 0) =
        upperEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [s, upperEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [s, upperEdge] at hv ⊢
        · fin_cases v <;> simp [upperEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  have hLower :
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) ∩
          {p | diamondVerticalAffine p = 0} =
        convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (t.image (diamondFanPosition a)) diamondVerticalAffine (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [t] at hv ⊢)
    have hfilter : (t.image (diamondFanPosition a)).filter
        (fun p => diamondVerticalAffine p = 0) =
        lowerEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [t, lowerEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [t, lowerEdge] at hv ⊢
        · fin_cases v <;> simp [lowerEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  let horizontal : Plane →ᵃ[ℝ] ℝ := cartesianY - AffineMap.const ℝ Plane a
  have hEdges :
      convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) =
        {diamondFanPosition a 4} := by
    have h := convexHull_inter_of_affine_separation
      (upperEdge.image (diamondFanPosition a))
      (lowerEdge.image (diamondFanPosition a))
      ({diamondFanPosition a 4} : Finset Plane) horizontal
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [upperEdge, horizontal] at hv ⊢ ; linarith)
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [lowerEdge, horizontal] at hv ⊢ ; linarith)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [upperEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [upperEdge]⟩, by simp [horizontal]⟩)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [lowerEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [lowerEdge]⟩, by simp [horizontal]⟩)
    simpa only [Finset.coe_image, Finset.coe_singleton, convexHull_singleton] using h
  change convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) = _
  apply Set.Subset.antisymm
  · intro p hp
    have hxle : p 0 ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.1
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [s] at hv ⊢
    have hxge : 0 ≤ p 0 := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.2
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [t] at hv ⊢
    have hxzero : diamondVerticalAffine p = 0 := by
      change p 0 = 0
      linarith
    have hpUpper : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
      rw [← hUpper]
      exact ⟨hp.1, by simpa using hxzero⟩
    have hpLower : p ∈ convexHull ℝ
        (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
      rw [← hLower]
      exact ⟨hp.2, hxzero⟩
    have hpBoth : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) :=
      ⟨hpUpper, hpLower⟩
    rw [hEdges] at hpBoth
    have hp4 : p = diamondFanPosition a 4 := Set.mem_singleton_iff.mp hpBoth
    subst p
    exact subset_convexHull ℝ _ ⟨4, by simp [], rfl⟩
  · intro p hp
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hp,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hp⟩

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_13
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_02_13 target :: scope.openDecls } }

private theorem diamondFan_inter_12_03 {a : ℝ} (ha0 : -2 < a) (ha1 : a < 2) :
    convexHull ℝ (diamondFanPosition a '' (({1, 2, 4} : Finset (Fin 5)) : Set _)) ∩
        convexHull ℝ (diamondFanPosition a '' (({0, 3, 4} : Finset (Fin 5)) : Set _)) =
      convexHull ℝ (diamondFanPosition a ''
        ((({1, 2, 4} : Finset (Fin 5)) ∩ {0, 3, 4} : Finset (Fin 5)) : Set _)) := by
  let s : Finset (Fin 5) := {1, 2, 4}
  let t : Finset (Fin 5) := {0, 3, 4}
  let upperEdge : Finset (Fin 5) := {2, 4}
  let lowerEdge : Finset (Fin 5) := {3, 4}
  have hUpper :
      convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
          {p | diamondVerticalAffine p = 0} =
        convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (s.image (diamondFanPosition a)) diamondVerticalAffine (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [s] at hv ⊢)
    have hfilter : (s.image (diamondFanPosition a)).filter
        (fun p => diamondVerticalAffine p = 0) =
        upperEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [s, upperEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [s, upperEdge] at hv ⊢
        · fin_cases v <;> simp [upperEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  have hLower :
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) ∩
          {p | (-diamondVerticalAffine) p = 0} =
        convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
    have h := convexHull_inter_affine_zero_of_nonneg
      (t.image (diamondFanPosition a)) (-diamondVerticalAffine) (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [t] at hv ⊢)
    have hfilter : (t.image (diamondFanPosition a)).filter
        (fun p => (-diamondVerticalAffine) p = 0) =
        lowerEdge.image (diamondFanPosition a) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        fin_cases v <;> simp [t, lowerEdge] at hv hz ⊢
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, ?_, rfl⟩, ?_⟩
        · fin_cases v <;> simp [t, lowerEdge] at hv ⊢
        · fin_cases v <;> simp [lowerEdge] at hv ⊢
    rw [hfilter] at h
    simpa only [Finset.coe_image] using h
  let horizontal : Plane →ᵃ[ℝ] ℝ := cartesianY - AffineMap.const ℝ Plane a
  have hEdges :
      convexHull ℝ (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) =
        {diamondFanPosition a 4} := by
    have h := convexHull_inter_of_affine_separation
      (upperEdge.image (diamondFanPosition a))
      (lowerEdge.image (diamondFanPosition a))
      ({diamondFanPosition a 4} : Finset Plane) horizontal
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [upperEdge, horizontal] at hv ⊢ ; linarith)
      (by
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        fin_cases v <;> simp [lowerEdge, horizontal] at hv ⊢ ; linarith)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [upperEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [upperEdge]⟩, by simp [horizontal]⟩)
      (by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨v, hv, rfl⟩, hz⟩
          fin_cases v <;> simp [lowerEdge, horizontal] at hv hz ⊢ ; linarith
        · rintro rfl
          exact ⟨⟨4, by simp [lowerEdge]⟩, by simp [horizontal]⟩)
    simpa only [Finset.coe_image, Finset.coe_singleton, convexHull_singleton] using h
  change convexHull ℝ (diamondFanPosition a '' (s : Set (Fin 5))) ∩
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5))) = _
  apply Set.Subset.antisymm
  · intro p hp
    have hxge : 0 ≤ p 0 := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.1
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [s] at hv ⊢
    have hxle : p 0 ≤ 0 := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage diamondVerticalAffine) hp.2
      rintro q ⟨v, hv, rfl⟩
      fin_cases v <;> simp [t] at hv ⊢
    have hxzero : diamondVerticalAffine p = 0 := by
      change p 0 = 0
      linarith
    have hpUpper : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) := by
      rw [← hUpper]
      exact ⟨hp.1, hxzero⟩
    have hpLower : p ∈ convexHull ℝ
        (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) := by
      rw [← hLower]
      exact ⟨hp.2, by simpa using hxzero⟩
    have hpBoth : p ∈ convexHull ℝ
        (diamondFanPosition a '' (upperEdge : Set (Fin 5))) ∩
          convexHull ℝ (diamondFanPosition a '' (lowerEdge : Set (Fin 5))) :=
      ⟨hpUpper, hpLower⟩
    rw [hEdges] at hpBoth
    have hp4 : p = diamondFanPosition a 4 := Set.mem_singleton_iff.mp hpBoth
    subst p
    exact subset_convexHull ℝ _ ⟨4, by simp [], rfl⟩
  · intro p hp
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hp,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hp⟩

run_cmd do
  let target := ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_12_03
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFan_inter_12_03 target :: scope.openDecls } }

/-- The four-triangle fan of a fixed diamond, with fan point `(0,a)`. -/
noncomputable def diamondFanMesh (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) : TriangleMesh where
  Vertex := Fin 5
  position := diamondFanPosition a
  position_injective := diamondFanPosition_injective ha0 ha1
  triangles := diamondFanTriangles
  card_triangle := by
    intro t ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  affineIndependent_triangle := fun t ht =>
    diamondFan_affineIndependent ha0 ha1 ht
  triangle_inter := by
    intro s hs t ht
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl
    · simp
    · exact diamondFan_inter_02_12 ha0 ha1
    · exact diamondFan_inter_02_03 ha0 ha1
    · exact diamondFan_inter_02_13 ha0 ha1
    · simpa [Set.inter_comm, Finset.pair_comm] using diamondFan_inter_02_12 ha0 ha1
    · simp
    · exact diamondFan_inter_12_03 ha0 ha1
    · exact diamondFan_inter_12_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_02_03 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_12_03 ha0 ha1
    · simp
    · exact diamondFan_inter_03_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_02_13 ha0 ha1
    · simpa [Set.inter_comm] using diamondFan_inter_12_13 ha0 ha1
    · simpa [Set.inter_comm, Finset.pair_comm] using diamondFan_inter_03_13 ha0 ha1
    · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh

theorem diamondFanMesh_support (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support = diamondPatch := by
  rw [TriangleMesh.toPlaneComplex_support, diamondPatch,
    ← diamondFan_left_union ha0 ha1, ← diamondFan_right_union ha0 ha1]
  change (⋃ t ∈ diamondFanTriangles,
      convexHull ℝ (diamondFanPosition a '' (t : Set (Fin 5)))) = _
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨t, ht, hxt⟩
    simp only [diamondFanTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl hxt)
    · exact Or.inr (Or.inl hxt)
    · exact Or.inl (Or.inr hxt)
    · exact Or.inr (Or.inr hxt)
  · rintro ((hxt | hxt) | (hxt | hxt))
    · exact ⟨{0, 4, 2}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{0, 3, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 2, 4}, by simp [diamondFanTriangles], hxt⟩
    · exact ⟨{1, 4, 3}, by simp [diamondFanTriangles], hxt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanMesh_support

/-- Slack from the upper-right side of the diamond. -/
noncomputable def diamondSlackUR : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 - 2 • cartesianX - cartesianY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR

/-- Slack from the upper-left side of the diamond. -/
noncomputable def diamondSlackUL : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 + 2 • cartesianX - cartesianY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL

/-- Slack from the lower-right side of the diamond. -/
noncomputable def diamondSlackLR : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 - 2 • cartesianX + cartesianY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR

/-- Slack from the lower-left side of the diamond. -/
noncomputable def diamondSlackLL : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 2 + 2 • cartesianX + cartesianY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL

theorem diamondSlackUR_apply (x y : ℝ) :
    diamondSlackUR (planePoint x y) = 2 - 2 * x - y := by
  simp [diamondSlackUR]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_apply

theorem diamondSlackUL_apply (x y : ℝ) :
    diamondSlackUL (planePoint x y) = 2 + 2 * x - y := by
  simp [diamondSlackUL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_apply

theorem diamondSlackLR_apply (x y : ℝ) :
    diamondSlackLR (planePoint x y) = 2 - 2 * x + y := by
  simp [diamondSlackLR]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_apply

theorem diamondSlackLL_apply (x y : ℝ) :
    diamondSlackLL (planePoint x y) = 2 + 2 * x + y := by
  simp [diamondSlackLL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_apply

@[simp] theorem diamondSlackUR_eq (p : Plane) :
    diamondSlackUR p = 2 - 2 * p 0 - p 1 := by
  simp [diamondSlackUR]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_eq

@[simp] theorem diamondSlackUL_eq (p : Plane) :
    diamondSlackUL p = 2 + 2 * p 0 - p 1 := by
  simp [diamondSlackUL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_eq

@[simp] theorem diamondSlackLR_eq (p : Plane) :
    diamondSlackLR p = 2 - 2 * p 0 + p 1 := by
  simp [diamondSlackLR]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_eq

@[simp] theorem diamondSlackLL_eq (p : Plane) :
    diamondSlackLL p = 2 + 2 * p 0 + p 1 := by
  simp [diamondSlackLL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_eq

theorem diamondSlackUR_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackUR ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 0 + 4 * x 3 + (2 - a) * x 4 := by
  change diamondSlackUR (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackUR_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_baryEval then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_baryEval"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_baryEval ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUR_baryEval

theorem diamondSlackUL_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackUL ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 1 + 4 * x 3 + (2 - a) * x 4 := by
  change diamondSlackUL (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackUL_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_baryEval then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_baryEval"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_baryEval ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackUL_baryEval

theorem diamondSlackLR_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackLR ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 0 + 4 * x 2 + (2 + a) * x 4 := by
  change diamondSlackLR (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackLR_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_baryEval then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_baryEval"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_baryEval ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLR_baryEval

theorem diamondSlackLL_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (hsum : ∑ v, x v = 1) :
    diamondSlackLL ((diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x) =
      4 * x 1 + 4 * x 2 + (2 + a) * x 4 := by
  change diamondSlackLL (∑ v : Fin 5, x v • diamondFanPosition a v) = _
  rw [diamondSlackLL_eq]
  simp [diamondFanPosition, planePoint, Fin.sum_univ_succ] at hsum ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_baryEval then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_baryEval"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_baryEval ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondSlackLL_baryEval

/-- Closed four-halfspace description of the diamond. -/
def InDiamond (p : Plane) : Prop :=
  0 ≤ diamondSlackUR p ∧ 0 ≤ diamondSlackUL p ∧
    0 ≤ diamondSlackLR p ∧ 0 ≤ diamondSlackLL p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.InDiamond then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.InDiamond"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.InDiamond ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.InDiamond

theorem diamondPatch_eq_inDiamond : diamondPatch = {p | InDiamond p} := by
  apply Set.Subset.antisymm
  · rintro p (hp | hp)
    all_goals
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage _ ) hp
        rintro q ⟨i, rfl⟩
        fin_cases i <;> simp []
  · intro p hp
    rcases hp with ⟨hUR, hUL, hLR, hLL⟩
    rw [diamondSlackUR_eq] at hUR
    rw [diamondSlackUL_eq] at hUL
    rw [diamondSlackLR_eq] at hLR
    rw [diamondSlackLL_eq] at hLL
    by_cases hx : p 0 ≤ 0
    · left
      rw [diamondLeftRegion]
      let w : Fin 3 → ℝ :=
        ![(p 1 + 2 + 2 * p 0) / 4, (2 + 2 * p 0 - p 1) / 4, -p 0]
      apply mem_convexHull_range_fin3_of_weights _ p w
      · intro i
        fin_cases i <;> simp [w] <;>
          change 0 ≤ _ at hUR hUL hLR hLL <;> linarith
      · simp [w]
        ring
      · ext i
        fin_cases i <;> simp [w, planePoint]
        all_goals ring
    · right
      rw [diamondRightRegion]
      have hx' : 0 ≤ p 0 := le_of_not_ge hx
      let w : Fin 3 → ℝ :=
        ![(p 1 + 2 - 2 * p 0) / 4, (2 - 2 * p 0 - p 1) / 4, p 0]
      apply mem_convexHull_range_fin3_of_weights _ p w
      · intro i
        fin_cases i <;> simp [w] <;>
          change 0 ≤ _ at hUR hUL hLR hLL <;> linarith
      · simp [w]
        ring
      · ext i
        fin_cases i <;> simp [w, planePoint]
        all_goals ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch_eq_inDiamond then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch_eq_inDiamond"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch_eq_inDiamond ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondPatch_eq_inDiamond

/-- Points satisfying all four diamond inequalities strictly form an open subset of the patch. -/
def StrictlyInDiamond : Set Plane :=
  {p | 0 < diamondSlackUR p ∧ 0 < diamondSlackUL p ∧
    0 < diamondSlackLR p ∧ 0 < diamondSlackLL p}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.StrictlyInDiamond then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.StrictlyInDiamond"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.StrictlyInDiamond ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.StrictlyInDiamond

theorem baryEval_mem_strictlyInDiamond_of_center_pos (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2)
    (x : Fin 5 → ℝ) (h0 : ∀ v, 0 ≤ x v) (hsum : ∑ v, x v = 1) (h4 : 0 < x 4) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x ∈ StrictlyInDiamond := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [diamondSlackUR_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 0, h0 3]
  · rw [diamondSlackUL_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 1, h0 3]
  · rw [diamondSlackLR_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 0, h0 2]
  · rw [diamondSlackLL_baryEval a ha0 ha1 x hsum]
    nlinarith [h0 1, h0 2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.baryEval_mem_strictlyInDiamond_of_center_pos then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.baryEval_mem_strictlyInDiamond_of_center_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.baryEval_mem_strictlyInDiamond_of_center_pos ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.baryEval_mem_strictlyInDiamond_of_center_pos

theorem isOpen_strictlyInDiamond : IsOpen StrictlyInDiamond := by
  change IsOpen ((diamondSlackUR ⁻¹' Set.Ioi 0) ∩
    ((diamondSlackUL ⁻¹' Set.Ioi 0) ∩ ((diamondSlackLR ⁻¹' Set.Ioi 0) ∩
      (diamondSlackLL ⁻¹' Set.Ioi 0))))
  exact (isOpen_Ioi.preimage diamondSlackUR.continuous_of_finiteDimensional).inter
    ((isOpen_Ioi.preimage diamondSlackUL.continuous_of_finiteDimensional).inter
      ((isOpen_Ioi.preimage diamondSlackLR.continuous_of_finiteDimensional).inter
        (isOpen_Ioi.preimage diamondSlackLL.continuous_of_finiteDimensional)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.isOpen_strictlyInDiamond then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.isOpen_strictlyInDiamond"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.isOpen_strictlyInDiamond ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.isOpen_strictlyInDiamond

theorem strictlyInDiamond_subset_patch : StrictlyInDiamond ⊆ diamondPatch := by
  rw [diamondPatch_eq_inDiamond]
  rintro p ⟨hUR, hUL, hLR, hLL⟩
  exact ⟨hUR.le, hUL.le, hLR.le, hLL.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_patch then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_patch"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_patch ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_patch

theorem strictlyInDiamond_subset_interior : StrictlyInDiamond ⊆ interior diamondPatch :=
  interior_maximal strictlyInDiamond_subset_patch isOpen_strictlyInDiamond

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_interior then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_interior ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.strictlyInDiamond_subset_interior

/-- The fixed abstract diamond fan with its center repositioned from height `a` to height `b`. -/
noncomputable def diamondFanReposition (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) : TriangleMesh :=
  (diamondFanMesh a ha0 ha1).reposition (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition

theorem diamondFanReposition_support (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support = diamondPatch := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ diamondFanTriangles,
    convexHull ℝ (diamondFanPosition b '' (t : Set (Fin 5)))) = diamondPatch
  simpa only [TriangleMesh.toPlaneComplex_support, diamondFanMesh] using
    diamondFanMesh_support b hb0 hb1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support

theorem diamondFanReposition_support_eq_source (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support =
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanReposition_support a b ha0 ha1 hb0 hb1).trans
    (diamondFanMesh_support a ha0 ha1).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support_eq_source then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support_eq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support_eq_source ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_support_eq_source

theorem diamondFanReposition_baryEval_eq_of_center_zero (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (x : Fin 5 → ℝ) (h4 : x 4 = 0) :
    (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval x =
      (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval x := by
  change (∑ v : Fin 5, x v • diamondFanPosition b v) =
    ∑ v : Fin 5, x v • diamondFanPosition a v
  simp [diamondFanPosition, Fin.sum_univ_succ, h4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_baryEval_eq_of_center_zero then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_baryEval_eq_of_center_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_baryEval_eq_of_center_zero ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanReposition_baryEval_eq_of_center_zero

/-- Preserve barycentric coordinates while moving the fan point from `(0,a)` to `(0,b)`. -/
noncomputable def diamondFanSupportHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support ≃ₜ
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).repositionHomeomorph (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph

/-- The `diamondFanCenterRealization` declaration. -/
noncomputable def diamondFanCenterRealization (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x : Fin 5 → ℝ := Pi.single 4 1
  refine ⟨x, single_mem_stdSimplex ℝ 4, {0, 4, 2}, ?_, ?_⟩
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    simp only [x, Pi.single_apply]
    split_ifs with h
    · subst v
      simp at hv
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization

@[simp] theorem diamondFanCenterRealization_baryEval (a : ℝ) (ha0 : -2 < a) (ha1 : a < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanCenterRealization a ha0 ha1).1 = planePoint 0 a := by
  change (∑ v : Fin 5, Pi.single 4 1 v • diamondFanPosition a v) = planePoint 0 a
  simp [Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization_baryEval then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization_baryEval"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization_baryEval ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanCenterRealization_baryEval

theorem diamondFanSupportHomeomorph_center (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    ((diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1)
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1]
        rw [diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ : Plane) = planePoint 0 b := by
  let x := diamondFanCenterRealization a ha0 ha1
  have hxold :
      (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
        (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2 x =
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1]
        rw [diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ := by
    apply Subtype.ext
    exact diamondFanCenterRealization_baryEval a ha0 ha1
  change ((diamondFanMesh a ha0 ha1).repositionHomeomorph (diamondFanPosition b)
      (diamondFanPosition_injective hb0 hb1)
      (diamondFanMesh b hb0 hb1).affineIndependent_triangle
      (diamondFanMesh b hb0 hb1).triangle_inter
      ⟨planePoint 0 a, by
        rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
        simp [InDiamond]
        constructor <;> linarith⟩ : Plane) = planePoint 0 b
  erw [TriangleMesh.coe_repositionHomeomorph_apply]
  have hinv :
      ((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
        (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm
          ⟨planePoint 0 a, by
            rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
            simp [InDiamond]
            constructor <;> linarith⟩ = x := by
    rw [← hxold]
    exact ((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
      (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm_apply_apply x
  rw [hinv]
  change (∑ v : Fin 5, Pi.single 4 1 v • diamondFanPosition b v) = planePoint 0 b
  simp [Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph_center then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph_center"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph_center ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanSupportHomeomorph_center

/-- The barycentric fan move, viewed as a self-homeomorphism of the original diamond support. -/
noncomputable def diamondFanPatchHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support ≃ₜ
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1).trans
    (Homeomorph.setCongr (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph

theorem diamondFanPatchHomeomorph_apply_val (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (z : (diamondFanMesh a ha0 ha1).toPlaneComplex.support) :
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) =
      (diamondFanSupportHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) := by
  simp only [diamondFanPatchHomeomorph, Homeomorph.trans_apply]
  apply coe_setCongr_apply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_apply_val ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_apply_val

theorem diamondFanPatchHomeomorph_fixed_frontier (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (p : Plane) (hp : p ∈ frontier (diamondFanMesh a ha0 ha1).toPlaneComplex.support) :
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
      ⟨p,
        (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩
      : Plane) = p := by
  let e := (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
  let z : (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
    ⟨p, (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩
  let x : GeometricRealization (Fin 5)
      (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := e.symm z
  let weights : Fin 5 → ℝ := x.1
  have hxstd : weights ∈ stdSimplex ℝ (Fin 5) := by
    simpa only [weights, diamondFanMesh, TriangleMesh.toPlaneComplex] using x.property.1
  have hxeval : (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval weights = p := by
    have he : e x = z := e.apply_symm_apply z
    exact congrArg Subtype.val he
  have hx4 : weights 4 = 0 := by
    by_contra hne
    have hpos : 0 < weights 4 := lt_of_le_of_ne (hxstd.1 4) (Ne.symm hne)
    have hstrict := baryEval_mem_strictlyInDiamond_of_center_pos a ha0 ha1 weights
      hxstd.1 hxstd.2 hpos
    have hint : p ∈ interior diamondPatch := by
      rw [← hxeval]
      exact strictlyInDiamond_subset_interior hstrict
    have hfront : p ∈ frontier diamondPatch := by
      simpa only [diamondFanMesh_support a ha0 ha1] using hp
    exact (Set.disjoint_left.1 disjoint_interior_frontier hint hfront)
  have hbary :
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval weights = p :=
    (diamondFanReposition_baryEval_eq_of_center_zero a b ha0 ha1 hb0 hb1 weights hx4).trans
      hxeval
  have hmove : (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) =
      (diamondFanReposition a b ha0 ha1 hb0 hb1).toPlaneComplex.baryEval
        (((diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
          (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2).symm z).1 := by
    exact TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply
      (diamondFanMesh a ha0 ha1) (diamondFanPosition b)
      (diamondFanPosition_injective hb0 hb1)
      (diamondFanMesh b hb0 hb1).affineIndependent_triangle
      (diamondFanMesh b hb0 hb1).triangle_inter
      (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1) z
  calc
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
        ⟨p,
          (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed.frontier_subset hp⟩ :
      Plane) = (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1 z : Plane) := rfl
    _ = _ := hmove
    _ = p := by simpa only [weights, x, e] using hbary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_fixed_frontier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_fixed_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_fixed_frontier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanPatchHomeomorph_fixed_frontier

/-- The elementary fan move extended by the identity to the whole plane. -/
noncomputable def diamondFanAmbientHomeomorph (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) : Plane ≃ₜ Plane :=
  (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph (diamondFanPosition b)
    (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph

theorem diamondFanAmbientHomeomorph_center (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
  diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1 (planePoint 0 a) =
      planePoint 0 b := by
  erw [diamondFanAmbientHomeomorph, TriangleMesh.ambientRepositionHomeomorph,
    extendHomeomorphByIdentity_apply_mem _ _ _ (by
      rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
      simp [InDiamond]
      constructor <;> linarith)]
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨planePoint 0 a, by
      rw [diamondFanMesh_support a ha0 ha1, diamondPatch_eq_inDiamond]
      simp [InDiamond]
      constructor <;> linarith⟩ : Plane) = planePoint 0 b
  rw [diamondFanPatchHomeomorph_apply_val]
  exact diamondFanSupportHomeomorph_center a b ha0 ha1 hb0 hb1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_center then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_center"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_center ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_center

theorem diamondFanAmbientHomeomorph_eqOn_compl (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    Set.EqOn (diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1) id diamondPatchᶜ := by
  intro p hp
  apply (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph_eqOn_compl
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)
  rwa [diamondFanMesh_support a ha0 ha1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_eqOn_compl then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_eqOn_compl ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.diamondFanAmbientHomeomorph_eqOn_compl

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
