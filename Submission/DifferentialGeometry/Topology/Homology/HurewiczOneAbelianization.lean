import Submission.DifferentialGeometry.Topology.Homology.SquareFundamentalChain
import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import Submission.DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne
import Submission.DifferentialGeometry.Topology.Homology.SphereHurewicz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralConstSimplex_face (n : ℕ) (x : X) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralConstSimplex (n + 1) x) =
      integralConstSimplex n x := by
  apply (integralSingularSimplexEquiv n X).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (integralConstSimplex (n + 1) x)) t = x
  rw [integralConstSimplex, TopCat.toSSetObjEquiv_δ_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralConstSimplex_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralConstSimplex_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralConstSimplex_face ``Submission.DifferentialGeometry.Topology.integralConstSimplex_face

theorem integralConstChain_two_boundary (x : X) :
    (integralSingularChains X).d 2 1 (integralConstChain 2 x) = integralConstChain 1 x := by
  have h := integralSimplexChain_boundary_two (X := X) (integralConstSimplex 2 x)
  simp only [integralConstChain] at h ⊢
  rw [h, integralConstSimplex_face, integralConstSimplex_face, integralConstSimplex_face]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralConstChain_two_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralConstChain_two_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralConstChain_two_boundary ``Submission.DifferentialGeometry.Topology.integralConstChain_two_boundary

theorem integralConstChain_one_boundary (x : X) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralConstChain 1 x :=
  ⟨integralConstChain 2 x, integralConstChain_two_boundary x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralConstChain_one_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralConstChain_one_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralConstChain_one_boundary ``Submission.DifferentialGeometry.Topology.integralConstChain_one_boundary

theorem integralPathChain_refl_eq_constChain (x : X) :
    integralPathChain (Path.refl x) = integralConstChain 1 x := by
  have h : integralPathSimplex (Path.refl x) = integralConstSimplex 1 x := by
    apply (integralSingularSimplexEquiv 1 X).injective
    apply ContinuousMap.ext
    intro t
    rw [integralPathSimplex_apply]
    rfl
  rw [integralPathChain, integralConstChain, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_refl_eq_constChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_refl_eq_constChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_refl_eq_constChain ``Submission.DifferentialGeometry.Topology.integralPathChain_refl_eq_constChain

theorem stdSimplex_one_le_one (t : stdSimplex ℝ (Fin 2)) : (t.val 1 : ℝ) ≤ 1 := by
  have hsum : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
  have h0 : (0 : ℝ) ≤ t.val 0 := t.property.1 0
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.stdSimplex_one_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.stdSimplex_one_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.stdSimplex_one_le_one ``Submission.DifferentialGeometry.Topology.stdSimplex_one_le_one

theorem squareAffineMap_one_apply_coe (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) :
    (squareAffineMap 1 ![P, Q] t i : ℝ) =
      (1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ) := by
  have ht : t.val 0 = 1 - t.val 1 := by
    have h : t.val 0 + t.val 1 = 1 := by simpa [Fin.sum_univ_two] using t.property.2
    linarith
  fin_cases i <;>
    (rw [squareAffineMap_apply_coe, Fin.sum_univ_two, ht]
     simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap_one_apply_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap_one_apply_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap_one_apply_coe ``Submission.DifferentialGeometry.Topology.squareAffineMap_one_apply_coe

theorem squareAffineMap_one_eq_squarePoint (P Q : Square) (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![P, Q] t =
      squarePoint
        ⟨(1 - t.val 1) * (P 0 : ℝ) + t.val 1 * (Q 0 : ℝ), by
          have hP := (P 0).property
          have hQ := (Q 0).property
          have ht1 := stdSimplex_one_le_one t
          have ht0 := t.property.1 1
          exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1],
            by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩
        ⟨(1 - t.val 1) * (P 1 : ℝ) + t.val 1 * (Q 1 : ℝ), by
          have hP := (P 1).property
          have hQ := (Q 1).property
          have ht1 := stdSimplex_one_le_one t
          have ht0 := t.property.1 1
          exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1],
            by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩ := by
  funext i
  apply Subtype.ext
  rw [squareAffineMap_one_apply_coe P Q t i]
  fin_cases i <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint ``Submission.DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint

theorem integralSimplexImageGen_squareSegment (f : C(Square, X)) (P Q : Square)
    (σ : integralSingularSimplex 1 X)
    (h : ∀ t : stdSimplex ℝ (Fin 2), f (squareAffineMap 1 ![P, Q] t) =
      (integralSingularSimplexEquiv 1 X σ) t) :
    singularSimplexImageGen 1 f (squareAffineSimplex 1 ![P, Q]) = σ := by
  apply (integralSingularSimplexEquiv 1 X).injective
  rw [singularSimplexImageGen_apply_val, squareAffineSimplex_coe]
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.comp_apply]
  exact h t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSimplexImageGen_squareSegment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSimplexImageGen_squareSegment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSimplexImageGen_squareSegment ``Submission.DifferentialGeometry.Topology.integralSimplexImageGen_squareSegment

theorem integralPathChain_squareSegment (f : C(Square, X)) (P Q : Square)
    (σ : integralSingularSimplex 1 X)
    (h : ∀ t : stdSimplex ℝ (Fin 2), f (squareAffineMap 1 ![P, Q] t) =
      (integralSingularSimplexEquiv 1 X σ) t) :
    integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1 ![P, Q])) =
      integralSimplexChain 1 σ := by
  rw [integralSimplexImageGen_squareSegment f P Q σ h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_squareSegment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_squareSegment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_squareSegment ``Submission.DifferentialGeometry.Topology.integralPathChain_squareSegment

theorem singularChainImageGen_squareFundamentalChain_boundary (f : C(Square, X)) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 f squareFundamentalChain) =
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareEast, squareNorthEast])) -
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareNorth, squareNorthEast])) +
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareOrigin, squareEast])) -
      integralSimplexChain 1 (singularSimplexImageGen 1 f (squareAffineSimplex 1
        ![squareOrigin, squareNorth])) := by
  rw [singularChainImageGen_d_eq, squareFundamentalChain_boundary]
  simp only [map_sub, map_add, singularChainImageGen_simplex, squareSegmentChain]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularChainImageGen_squareFundamentalChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularChainImageGen_squareFundamentalChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularChainImageGen_squareFundamentalChain_boundary ``Submission.DifferentialGeometry.Topology.singularChainImageGen_squareFundamentalChain_boundary

def reverseSquareParam : C(Square, unitInterval) where
  toFun z := ⟨(z 0 : ℝ) * (1 - (z 1 : ℝ)), by
    have h0 := (z 0).property
    have h1 := (z 1).property
    exact ⟨by nlinarith [h0.1, h1.1, h1.2], by nlinarith [h0.2, h1.1, h1.2]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_apply 0)).mul
      (continuous_const.sub (continuous_subtype_val.comp (continuous_apply 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam ``Submission.DifferentialGeometry.Topology.reverseSquareParam

def concatSquareParam : C(Square, unitInterval) where
  toFun z := ⟨(z 0 : ℝ) * (1 + (z 1 : ℝ)) / 2, by
    have h0 := (z 0).property
    have h1 := (z 1).property
    have hz1 : (1 : ℝ) + z 1 ≤ 2 := by linarith [h1.2]
    have hmul : (z 0 : ℝ) * (1 + (z 1 : ℝ)) ≤ 1 * 2 :=
      mul_le_mul h0.2 hz1 (by linarith [h1.1]) (by linarith [h0.1])
    exact ⟨by nlinarith [h0.1, h1.1], by linarith⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_subtype_val.comp (continuous_apply 0)).mul
      (continuous_const.add (continuous_subtype_val.comp (continuous_apply 1)))).div_const 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.concatSquareParam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.concatSquareParam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.concatSquareParam ``Submission.DifferentialGeometry.Topology.concatSquareParam

def pathReverseSquare {a b : X} (p : Path a b) : C(Square, X) :=
  p.toContinuousMap.comp reverseSquareParam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare ``Submission.DifferentialGeometry.Topology.pathReverseSquare

def pathConcatSquare {a b c : X} (p : Path a b) (q : Path b c) : C(Square, X) :=
  (p.trans q).toContinuousMap.comp concatSquareParam

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare ``Submission.DifferentialGeometry.Topology.pathConcatSquare

theorem reverseSquareParam_apply (z : Square) :
    reverseSquareParam z = ⟨(z 0 : ℝ) * (1 - (z 1 : ℝ)), by
      have h0 := (z 0).property
      have h1 := (z 1).property
      exact ⟨by nlinarith [h0.1, h1.1, h1.2], by nlinarith [h0.2, h1.1, h1.2]⟩⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam_apply ``Submission.DifferentialGeometry.Topology.reverseSquareParam_apply

theorem pathReverseSquare_apply {a b : X} (p : Path a b) (z : Square) :
    pathReverseSquare p z = p (reverseSquareParam z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_apply ``Submission.DifferentialGeometry.Topology.pathReverseSquare_apply

theorem pathConcatSquare_apply {a b c : X} (p : Path a b) (q : Path b c) (z : Square) :
    pathConcatSquare p q z = (p.trans q) (concatSquareParam z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_apply ``Submission.DifferentialGeometry.Topology.pathConcatSquare_apply

theorem reverseSquareParam_squarePoint_zero (s : unitInterval) :
    reverseSquareParam (squarePoint s 0) = s := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam_squarePoint_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_zero ``Submission.DifferentialGeometry.Topology.reverseSquareParam_squarePoint_zero

theorem reverseSquareParam_squarePoint_one (s : unitInterval) :
    reverseSquareParam (squarePoint s 1) = 0 := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam_squarePoint_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_one ``Submission.DifferentialGeometry.Topology.reverseSquareParam_squarePoint_one

theorem reverseSquareParam_squarePoint_left (s : unitInterval) :
    reverseSquareParam (squarePoint 0 s) = 0 := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam_squarePoint_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_left ``Submission.DifferentialGeometry.Topology.reverseSquareParam_squarePoint_left

theorem reverseSquareParam_squarePoint_right (s : unitInterval) :
    reverseSquareParam (squarePoint 1 s) = ⟨1 - (s : ℝ), by
      have h := s.2
      exact ⟨by linarith [h.2], by linarith [h.1]⟩⟩ := by
  apply Subtype.ext
  simp only [reverseSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.reverseSquareParam_squarePoint_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.reverseSquareParam_squarePoint_right ``Submission.DifferentialGeometry.Topology.reverseSquareParam_squarePoint_right

theorem concatSquareParam_squarePoint_bottom (s : unitInterval) :
    concatSquareParam (squarePoint s 0) = ⟨(s : ℝ) / 2, by
      have h := s.2
      exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩ := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.concatSquareParam_squarePoint_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.concatSquareParam_squarePoint_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.concatSquareParam_squarePoint_bottom ``Submission.DifferentialGeometry.Topology.concatSquareParam_squarePoint_bottom

theorem concatSquareParam_squarePoint_top (s : unitInterval) :
    concatSquareParam (squarePoint s 1) = s := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.concatSquareParam_squarePoint_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.concatSquareParam_squarePoint_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.concatSquareParam_squarePoint_top ``Submission.DifferentialGeometry.Topology.concatSquareParam_squarePoint_top

theorem concatSquareParam_squarePoint_left (s : unitInterval) :
    concatSquareParam (squarePoint 0 s) = 0 := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.concatSquareParam_squarePoint_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.concatSquareParam_squarePoint_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.concatSquareParam_squarePoint_left ``Submission.DifferentialGeometry.Topology.concatSquareParam_squarePoint_left

theorem concatSquareParam_squarePoint_right (s : unitInterval) :
    concatSquareParam (squarePoint 1 s) = ⟨(1 + (s : ℝ)) / 2, by
      have h := s.2
      exact ⟨by linarith [h.1], by linarith [h.2]⟩⟩ := by
  apply Subtype.ext
  simp only [concatSquareParam, ContinuousMap.coe_mk, squarePoint_zero, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.concatSquareParam_squarePoint_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.concatSquareParam_squarePoint_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.concatSquareParam_squarePoint_right ``Submission.DifferentialGeometry.Topology.concatSquareParam_squarePoint_right

def squareInterpCoord (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) : unitInterval :=
  ⟨(1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ), by
    have hP := (P i).property
    have hQ := (Q i).property
    have ht1 := stdSimplex_one_le_one t
    have ht0 := t.property.1 1
    exact ⟨by nlinarith [hP.1, hQ.1, ht0, ht1], by nlinarith [hP.2, hQ.2, ht0, ht1]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord ``Submission.DifferentialGeometry.Topology.squareInterpCoord

theorem squareInterpCoord_apply_coe (P Q : Square) (t : stdSimplex ℝ (Fin 2)) (i : Fin 2) :
    (squareInterpCoord P Q t i : ℝ) =
      (1 - t.val 1) * (P i : ℝ) + t.val 1 * (Q i : ℝ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_apply_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_apply_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_apply_coe ``Submission.DifferentialGeometry.Topology.squareInterpCoord_apply_coe

theorem squareAffineMap_one_eq_squarePoint_coord (P Q : Square) (t : stdSimplex ℝ (Fin 2)) :
    squareAffineMap 1 ![P, Q] t =
      squarePoint (squareInterpCoord P Q t 0) (squareInterpCoord P Q t 1) := by
  rw [squareAffineMap_one_eq_squarePoint]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint_coord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint_coord ``Submission.DifferentialGeometry.Topology.squareAffineMap_one_eq_squarePoint_coord

theorem pathReverseSquare_bottom {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint s 0) = p s := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_bottom ``Submission.DifferentialGeometry.Topology.pathReverseSquare_bottom

theorem pathReverseSquare_top {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint s 1) = p 0 := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_top ``Submission.DifferentialGeometry.Topology.pathReverseSquare_top

theorem pathReverseSquare_left {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint 0 s) = p 0 := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_left ``Submission.DifferentialGeometry.Topology.pathReverseSquare_left

theorem pathReverseSquare_right {a b : X} (p : Path a b) (s : unitInterval) :
    pathReverseSquare p (squarePoint 1 s) = p.symm s := by
  rw [pathReverseSquare_apply, reverseSquareParam_squarePoint_right]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_right ``Submission.DifferentialGeometry.Topology.pathReverseSquare_right

theorem pathConcatSquare_bottom {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint s 0) = p s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_bottom, Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    push_cast
    ring
  · exfalso
    apply h
    push_cast
    linarith [s.2.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_bottom ``Submission.DifferentialGeometry.Topology.pathConcatSquare_bottom

theorem pathConcatSquare_top {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint s 1) = (p.trans q) s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_top]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_top ``Submission.DifferentialGeometry.Topology.pathConcatSquare_top

theorem pathConcatSquare_left {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint 0 s) = p 0 := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_left, Path.trans_apply]
  rw [dif_pos (by norm_num)]
  congr 1
  apply Subtype.ext
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_left ``Submission.DifferentialGeometry.Topology.pathConcatSquare_left

theorem pathConcatSquare_right {a b c : X} (p : Path a b) (q : Path b c) (s : unitInterval) :
    pathConcatSquare p q (squarePoint 1 s) = q s := by
  rw [pathConcatSquare_apply, concatSquareParam_squarePoint_right, Path.trans_apply]
  split_ifs with h
  · have hs : (s : ℝ) = 0 := by linarith [s.2.1, h]
    have hs' : s = 0 := Subtype.ext hs
    subst hs'
    refine (congrArg p ?_).trans (p.target.trans q.source.symm)
    apply Subtype.ext
    push_cast
    ring
  · congr 1
    apply Subtype.ext
    push_cast
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_right ``Submission.DifferentialGeometry.Topology.pathConcatSquare_right

theorem stdSimplexHomeomorphUnitInterval_coe (t : stdSimplex ℝ (Fin 2)) :
    ((stdSimplexHomeomorphUnitInterval t : unitInterval) : ℝ) = t.val 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.stdSimplexHomeomorphUnitInterval_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.stdSimplexHomeomorphUnitInterval_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.stdSimplexHomeomorphUnitInterval_coe ``Submission.DifferentialGeometry.Topology.stdSimplexHomeomorphUnitInterval_coe

theorem squareInterpCoord_origin_east_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareEast t 0 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareEast, squarePoint_zero,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_origin_east_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_origin_east_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_origin_east_zero ``Submission.DifferentialGeometry.Topology.squareInterpCoord_origin_east_zero

theorem squareInterpCoord_origin_east_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareEast t 1 = 0 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareEast, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_origin_east_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_origin_east_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_origin_east_one ``Submission.DifferentialGeometry.Topology.squareInterpCoord_origin_east_one

theorem squareInterpCoord_east_northEast_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareEast squareNorthEast t 0 = 1 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareEast, squareNorthEast, squarePoint_zero,
    ]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_east_northEast_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_east_northEast_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_east_northEast_zero ``Submission.DifferentialGeometry.Topology.squareInterpCoord_east_northEast_zero

theorem squareInterpCoord_east_northEast_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareEast squareNorthEast t 1 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareEast, squareNorthEast, squarePoint_one,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_east_northEast_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_east_northEast_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_east_northEast_one ``Submission.DifferentialGeometry.Topology.squareInterpCoord_east_northEast_one

theorem squareInterpCoord_north_northEast_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareNorth squareNorthEast t 0 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareNorth, squareNorthEast, squarePoint_zero,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_north_northEast_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_north_northEast_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_north_northEast_zero ``Submission.DifferentialGeometry.Topology.squareInterpCoord_north_northEast_zero

theorem squareInterpCoord_north_northEast_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareNorth squareNorthEast t 1 = 1 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareNorth, squareNorthEast, squarePoint_one]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_north_northEast_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_north_northEast_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_north_northEast_one ``Submission.DifferentialGeometry.Topology.squareInterpCoord_north_northEast_one

theorem squareInterpCoord_origin_north_zero (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareNorth t 0 = 0 := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareNorth, squarePoint_zero]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_origin_north_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_origin_north_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_origin_north_zero ``Submission.DifferentialGeometry.Topology.squareInterpCoord_origin_north_zero

theorem squareInterpCoord_origin_north_one (t : stdSimplex ℝ (Fin 2)) :
    squareInterpCoord squareOrigin squareNorth t 1 = stdSimplexHomeomorphUnitInterval t := by
  apply Subtype.ext
  simp only [squareInterpCoord, Subtype.coe_mk, squareOrigin, squareNorth, squarePoint_one,
    stdSimplexHomeomorphUnitInterval_coe]
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareInterpCoord_origin_north_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareInterpCoord_origin_north_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareInterpCoord_origin_north_one ``Submission.DifferentialGeometry.Topology.squareInterpCoord_origin_north_one

theorem pathReverseSquare_edge_bottom {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareOrigin, squareEast] t) =
        p (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_east_zero,
    squareInterpCoord_origin_east_one]
  exact pathReverseSquare_bottom p _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_edge_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_edge_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_edge_bottom ``Submission.DifferentialGeometry.Topology.pathReverseSquare_edge_bottom

theorem pathReverseSquare_edge_right {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareEast, squareNorthEast] t) =
        p.symm (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_east_northEast_zero,
    squareInterpCoord_east_northEast_one]
  exact pathReverseSquare_right p _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_edge_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_edge_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_edge_right ``Submission.DifferentialGeometry.Topology.pathReverseSquare_edge_right

theorem pathReverseSquare_edge_top {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareNorth, squareNorthEast] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_north_northEast_zero,
    squareInterpCoord_north_northEast_one]
  exact (pathReverseSquare_top p _).trans (Path.source p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_edge_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_edge_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_edge_top ``Submission.DifferentialGeometry.Topology.pathReverseSquare_edge_top

theorem pathReverseSquare_edge_left {a b : X} (p : Path a b) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathReverseSquare p (squareAffineMap 1 ![squareOrigin, squareNorth] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_north_zero,
    squareInterpCoord_origin_north_one]
  exact (pathReverseSquare_left p _).trans (Path.source p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_edge_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_edge_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_edge_left ``Submission.DifferentialGeometry.Topology.pathReverseSquare_edge_left

theorem pathConcatSquare_edge_bottom {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareOrigin, squareEast] t) =
        p (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_east_zero,
    squareInterpCoord_origin_east_one]
  exact pathConcatSquare_bottom p q _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_edge_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_edge_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_edge_bottom ``Submission.DifferentialGeometry.Topology.pathConcatSquare_edge_bottom

theorem pathConcatSquare_edge_right {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareEast, squareNorthEast] t) =
        q (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_east_northEast_zero,
    squareInterpCoord_east_northEast_one]
  exact pathConcatSquare_right p q _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_edge_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_edge_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_edge_right ``Submission.DifferentialGeometry.Topology.pathConcatSquare_edge_right

theorem pathConcatSquare_edge_top {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareNorth, squareNorthEast] t) =
        (p.trans q) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_north_northEast_zero,
    squareInterpCoord_north_northEast_one]
  exact pathConcatSquare_top p q _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_edge_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_edge_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_edge_top ``Submission.DifferentialGeometry.Topology.pathConcatSquare_edge_top

theorem pathConcatSquare_edge_left {a b c : X} (p : Path a b) (q : Path b c) :
    ∀ t : stdSimplex ℝ (Fin 2),
      pathConcatSquare p q (squareAffineMap 1 ![squareOrigin, squareNorth] t) =
        (Path.refl a) (stdSimplexHomeomorphUnitInterval t) := by
  intro t
  rw [squareAffineMap_one_eq_squarePoint_coord, squareInterpCoord_origin_north_zero,
    squareInterpCoord_origin_north_one]
  exact (pathConcatSquare_left p q _).trans (Path.source p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_edge_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_edge_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_edge_left ``Submission.DifferentialGeometry.Topology.pathConcatSquare_edge_left

theorem pathReverseSquare_boundary {a b : X} (p : Path a b) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 (pathReverseSquare p)
      squareFundamentalChain) =
      integralPathChain p.symm - integralConstChain 1 a +
        integralPathChain p - integralConstChain 1 a := by
  have h₁ := integralPathChain_squareSegment (pathReverseSquare p) squareEast squareNorthEast
    (integralPathSimplex p.symm) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathReverseSquare_edge_right p t)
  have h₂ := integralPathChain_squareSegment (pathReverseSquare p) squareNorth squareNorthEast
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathReverseSquare_edge_top p t)
  have h₃ := integralPathChain_squareSegment (pathReverseSquare p) squareOrigin squareEast
    (integralPathSimplex p) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathReverseSquare_edge_bottom p t)
  have h₄ := integralPathChain_squareSegment (pathReverseSquare p) squareOrigin squareNorth
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathReverseSquare_edge_left p t)
  rw [singularChainImageGen_squareFundamentalChain_boundary, h₁, h₂, h₃, h₄]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathReverseSquare_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathReverseSquare_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathReverseSquare_boundary ``Submission.DifferentialGeometry.Topology.pathReverseSquare_boundary

theorem pathConcatSquare_boundary {a b c : X} (p : Path a b) (q : Path b c) :
    (integralSingularChains X).d 2 1 (singularChainImageGen 2 (pathConcatSquare p q)
      squareFundamentalChain) =
      integralPathChain q - integralPathChain (p.trans q) +
        integralPathChain p - integralConstChain 1 a := by
  have h₁ := integralPathChain_squareSegment (pathConcatSquare p q) squareEast squareNorthEast
    (integralPathSimplex q) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_right p q t)
  have h₂ := integralPathChain_squareSegment (pathConcatSquare p q) squareNorth squareNorthEast
    (integralPathSimplex (p.trans q)) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_top p q t)
  have h₃ := integralPathChain_squareSegment (pathConcatSquare p q) squareOrigin squareEast
    (integralPathSimplex p) (by
      intro t
      rw [integralPathSimplex_apply]
      exact pathConcatSquare_edge_bottom p q t)
  have h₄ := integralPathChain_squareSegment (pathConcatSquare p q) squareOrigin squareNorth
    (integralConstSimplex 1 a) (by
      intro t
      simpa [integralConstSimplex] using pathConcatSquare_edge_left p q t)
  rw [singularChainImageGen_squareFundamentalChain_boundary, h₁, h₂, h₃, h₄]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathConcatSquare_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathConcatSquare_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathConcatSquare_boundary ``Submission.DifferentialGeometry.Topology.pathConcatSquare_boundary

theorem exists_integralPathChain_trans_sub_mem_range {a b c : X} (p : Path a b) (q : Path b c) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralPathChain (p.trans q) -
        integralPathChain p - integralPathChain q := by
  refine ⟨-(singularChainImageGen 2 (pathConcatSquare p q) squareFundamentalChain) -
    integralConstChain 2 a, ?_⟩
  rw [map_sub, map_neg, pathConcatSquare_boundary p q, integralConstChain_two_boundary]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralPathChain_trans_sub_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralPathChain_trans_sub_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralPathChain_trans_sub_mem_range ``Submission.DifferentialGeometry.Topology.exists_integralPathChain_trans_sub_mem_range

theorem exists_integralPathChain_add_symm_mem_range {a b : X} (p : Path a b) :
    ∃ w : (integralSingularChains X).X 2,
      (integralSingularChains X).d 2 1 w = integralPathChain p + integralPathChain p.symm := by
  refine ⟨singularChainImageGen 2 (pathReverseSquare p) squareFundamentalChain +
    (2 : ℤ) • integralConstChain 2 a, ?_⟩
  rw [map_add, map_zsmul, pathReverseSquare_boundary p, integralConstChain_two_boundary]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralPathChain_add_symm_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralPathChain_add_symm_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralPathChain_add_symm_mem_range ``Submission.DifferentialGeometry.Topology.exists_integralPathChain_add_symm_mem_range

theorem integralSingularCycleClass_add (n : ℕ) (z w : integralSingularCycles n X) :
    integralSingularCycleClass n X (z + w) =
      integralSingularCycleClass n X z + integralSingularCycleClass n X w := by
  rw [integralSingularCycleClass, integralSingularCycleClass, integralSingularCycleClass]
  rw [show Submodule.Quotient.mk (z + w) = Submodule.Quotient.mk z + Submodule.Quotient.mk w
    from map_add (Submodule.mkQ _) z w]
  exact map_add _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClass_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClass_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClass_add ``Submission.DifferentialGeometry.Topology.integralSingularCycleClass_add

theorem integralSingularCycleClass_zsmul (n : ℕ) (k : ℤ) (z : integralSingularCycles n X) :
    integralSingularCycleClass n X (k • z) = k • integralSingularCycleClass n X z := by
  rw [integralSingularCycleClass, integralSingularCycleClass]
  rw [show Submodule.Quotient.mk (k • z) = k • Submodule.Quotient.mk z
    from map_zsmul (Submodule.mkQ _) k z]
  exact map_zsmul _ k _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClass_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClass_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClass_zsmul ``Submission.DifferentialGeometry.Topology.integralSingularCycleClass_zsmul

theorem integralSingularCycleClass_eq_of_sub_mem_range (n : ℕ) (z w : integralSingularCycles n X)
    (h : ((z : (integralSingularChains X).X (n + 1)) -
        (w : (integralSingularChains X).X (n + 1))) ∈
      LinearMap.range ((integralSingularChains X).d (n + 2) (n + 1)).hom) :
    integralSingularCycleClass n X z = integralSingularCycleClass n X w := by
  obtain ⟨c, hc⟩ := h
  have hzw : z - w = integralSingularBoundaryToCycles n X c := by
    apply Subtype.ext
    change ((z : (integralSingularChains X).X (n + 1)) -
      (w : (integralSingularChains X).X (n + 1))) = (integralSingularBoundaryToCycles n X c :
        (integralSingularChains X).X (n + 1))
    rw [integralSingularBoundaryToCycles_coe]
    exact hc.symm
  have hz : z = w + integralSingularBoundaryToCycles n X c := by
    rw [← hzw]
    abel
  rw [hz, integralSingularCycleClass_add, integralSingularCycleClass_boundary, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycleClass_eq_of_sub_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycleClass_eq_of_sub_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycleClass_eq_of_sub_mem_range ``Submission.DifferentialGeometry.Topology.integralSingularCycleClass_eq_of_sub_mem_range

theorem integralPathChain_cycle {x : X} (γ : Path x x) :
    (integralSingularChains X).d 1 0 (integralPathChain γ) = 0 := by
  rw [integralPathChain_boundary, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_cycle ``Submission.DifferentialGeometry.Topology.integralPathChain_cycle

def integralPathLoopClass {x : X} (γ : Path x x) : integralSingularHomology 1 X :=
  integralSingularCycleClass 0 X ⟨integralPathChain γ, integralPathChain_cycle γ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathLoopClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathLoopClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathLoopClass ``Submission.DifferentialGeometry.Topology.integralPathLoopClass

theorem integralPathLoopClass_trans {x : X} (γ δ : Path x x) :
    integralPathLoopClass (γ.trans δ) =
      integralPathLoopClass γ + integralPathLoopClass δ := by
  obtain ⟨w, hw⟩ := exists_integralPathChain_trans_sub_mem_range γ δ
  have hdiff : (integralSingularChains X).d 2 1 w = integralPathChain (γ.trans δ) -
      (integralPathChain γ + integralPathChain δ) := by
    rw [hw]
    abel
  have hsum : (integralSingularChains X).d 1 0
      (integralPathChain γ + integralPathChain δ) = 0 := by
    rw [map_add, integralPathChain_cycle, integralPathChain_cycle, add_zero]
  have hkey := integralSingularCycleClass_eq_of_sub_mem_range 0
    ⟨integralPathChain (γ.trans δ), integralPathChain_cycle (γ.trans δ)⟩
    ⟨integralPathChain γ + integralPathChain δ, hsum⟩ ⟨w, hdiff⟩
  have hz : (⟨integralPathChain γ + integralPathChain δ, hsum⟩ : integralSingularCycles 0 X) =
      (⟨integralPathChain γ, integralPathChain_cycle γ⟩ : integralSingularCycles 0 X) +
        ⟨integralPathChain δ, integralPathChain_cycle δ⟩ := Subtype.ext rfl
  rw [hz, integralSingularCycleClass_add] at hkey
  exact hkey

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathLoopClass_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathLoopClass_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathLoopClass_trans ``Submission.DifferentialGeometry.Topology.integralPathLoopClass_trans

def simplexSourceVertex (σ : integralSingularSimplex 1 X) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexSourceVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexSourceVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexSourceVertex ``Submission.DifferentialGeometry.Topology.simplexSourceVertex

def simplexTargetVertex (σ : integralSingularSimplex 1 X) : X :=
  TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexTargetVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexTargetVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexTargetVertex ``Submission.DifferentialGeometry.Topology.simplexTargetVertex

theorem integralVertexChain_eq_zero_simplex (x : X) :
    integralVertexChain x = integralSimplexChain 0 (TopCat.toSSetObj₀Equiv.symm x) := by
  unfold integralVertexChain
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralVertexChain_eq_zero_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralVertexChain_eq_zero_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralVertexChain_eq_zero_simplex ``Submission.DifferentialGeometry.Topology.integralVertexChain_eq_zero_simplex

def integralSourceVertexMap :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 0 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 0) ℕ
    (fun σ => integralVertexChain (simplexSourceVertex σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSourceVertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSourceVertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSourceVertexMap ``Submission.DifferentialGeometry.Topology.integralSourceVertexMap

def integralTargetVertexMap :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 0 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 0) ℕ
    (fun σ => integralVertexChain (simplexTargetVertex σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralTargetVertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralTargetVertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralTargetVertexMap ``Submission.DifferentialGeometry.Topology.integralTargetVertexMap

theorem integralSourceVertexMap_simplex (σ : integralSingularSimplex 1 X) :
    integralSourceVertexMap (integralSimplexChain 1 σ) =
      integralVertexChain (simplexSourceVertex σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSourceVertexMap_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSourceVertexMap_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSourceVertexMap_simplex ``Submission.DifferentialGeometry.Topology.integralSourceVertexMap_simplex

theorem integralTargetVertexMap_simplex (σ : integralSingularSimplex 1 X) :
    integralTargetVertexMap (integralSimplexChain 1 σ) =
      integralVertexChain (simplexTargetVertex σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralTargetVertexMap_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralTargetVertexMap_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralTargetVertexMap_simplex ``Submission.DifferentialGeometry.Topology.integralTargetVertexMap_simplex

theorem integralTargetVertexMap_sub_sourceVertexMap :
    integralTargetVertexMap - integralSourceVertexMap =
      ((integralSingularChains X).d 1 0).hom := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.sub_apply, integralTargetVertexMap_simplex,
    integralSourceVertexMap_simplex, integralSimplexChain_boundary_one,
    integralSimplexChain_zero_vertex, integralSimplexChain_zero_vertex]
  simp only [simplexTargetVertex, simplexSourceVertex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralTargetVertexMap_sub_sourceVertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralTargetVertexMap_sub_sourceVertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralTargetVertexMap_sub_sourceVertexMap ``Submission.DifferentialGeometry.Topology.integralTargetVertexMap_sub_sourceVertexMap

def integralReversedPathCone [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 1) ℕ
    (fun σ => integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralReversedPathCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralReversedPathCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralReversedPathCone ``Submission.DifferentialGeometry.Topology.integralReversedPathCone

theorem integralReversedPathCone_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    integralReversedPathCone x (integralSimplexChain 0 σ) =
      integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralReversedPathCone_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralReversedPathCone_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralReversedPathCone_simplex ``Submission.DifferentialGeometry.Topology.integralReversedPathCone_simplex

def pathLoopOfSimplex [PathConnectedSpace X] (x : X) (σ : integralSingularSimplex 1 X) :
    Path x x :=
  (PathConnectedSpace.somePath x (simplexSourceVertex σ)).trans
    ((integralSimplexPath σ).trans (PathConnectedSpace.somePath x (simplexTargetVertex σ)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathLoopOfSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathLoopOfSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathLoopOfSimplex ``Submission.DifferentialGeometry.Topology.pathLoopOfSimplex

noncomputable def integralPathConeNullHomology [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) : (integralSingularChains X).X 2 :=
  Classical.choose (exists_integralPathChain_add_symm_mem_range
    (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathConeNullHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathConeNullHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathConeNullHomology ``Submission.DifferentialGeometry.Topology.integralPathConeNullHomology

theorem integralPathConeNullHomology_spec [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    (integralSingularChains X).d 2 1 (integralPathConeNullHomology x σ) =
      integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)) +
        integralPathChain (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)).symm :=
  Classical.choose_spec (exists_integralPathChain_add_symm_mem_range
    (PathConnectedSpace.somePath x (TopCat.toSSetObj₀Equiv σ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathConeNullHomology_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathConeNullHomology_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathConeNullHomology_spec ``Submission.DifferentialGeometry.Topology.integralPathConeNullHomology_spec

def integralPathConeNullHomotopy [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 2 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 2) ℕ
    (fun σ => integralPathConeNullHomology x σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathConeNullHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathConeNullHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathConeNullHomotopy ``Submission.DifferentialGeometry.Topology.integralPathConeNullHomotopy

theorem integralPathConeNullHomotopy_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 0 X) :
    integralPathConeNullHomotopy x (integralSimplexChain 0 σ) =
      integralPathConeNullHomology x σ := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathConeNullHomotopy_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathConeNullHomotopy_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathConeNullHomotopy_simplex ``Submission.DifferentialGeometry.Topology.integralPathConeNullHomotopy_simplex

theorem integralPathCone_equation [PathConnectedSpace X] (x : X) :
    ((integralSingularChains X).d 2 1).hom.comp (integralPathConeNullHomotopy x) =
      integralVertexPathCone x + integralReversedPathCone x := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply, integralPathConeNullHomotopy_simplex,
    integralPathConeNullHomology_spec, LinearMap.add_apply, integralVertexPathCone_simplex,
    integralReversedPathCone_simplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathCone_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathCone_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathCone_equation ``Submission.DifferentialGeometry.Topology.integralPathCone_equation

def integralPathLoopChainMap [PathConnectedSpace X] (x : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 1) ℕ
    (fun σ => integralPathChain (pathLoopOfSimplex x σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathLoopChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathLoopChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathLoopChainMap ``Submission.DifferentialGeometry.Topology.integralPathLoopChainMap

theorem integralPathLoopChainMap_simplex [PathConnectedSpace X] (x : X)
    (σ : integralSingularSimplex 1 X) :
    integralPathLoopChainMap x (integralSimplexChain 1 σ) =
      integralPathChain (pathLoopOfSimplex x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathLoopChainMap_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathLoopChainMap_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathLoopChainMap_simplex ``Submission.DifferentialGeometry.Topology.integralPathLoopChainMap_simplex

theorem integralSourceVertexMap_eq_targetVertexMap_of_cycle [PathConnectedSpace X]
    (z : integralSingularCycles 0 X) :
    integralSourceVertexMap (z : (integralSingularChains X).X 1) =
      integralTargetVertexMap (z : (integralSingularChains X).X 1) := by
  have h := LinearMap.congr_fun integralTargetVertexMap_sub_sourceVertexMap
    (z : (integralSingularChains X).X 1)
  rw [LinearMap.sub_apply] at h
  have hz : (integralSingularChains X).d 1 0 (z : (integralSingularChains X).X 1) = 0 := z.property
  rw [hz, sub_eq_zero] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSourceVertexMap_eq_targetVertexMap_of_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSourceVertexMap_eq_targetVertexMap_of_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSourceVertexMap_eq_targetVertexMap_of_cycle ``Submission.DifferentialGeometry.Topology.integralSourceVertexMap_eq_targetVertexMap_of_cycle

def HurewiczOneLoopGeneration [PathConnectedSpace X] (x : X) : Prop :=
  ∀ y : integralSingularHomology 1 X,
    y ∈ Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczOneLoopGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczOneLoopGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczOneLoopGeneration ``Submission.DifferentialGeometry.Topology.HurewiczOneLoopGeneration

def HurewiczOneVertexPairing [PathConnectedSpace X] (x : X) : Prop :=
  ∀ z : integralSingularCycles 0 X,
    ((z : (integralSingularChains X).X 1) -
      integralPathLoopChainMap x (z : (integralSingularChains X).X 1)) ∈
      LinearMap.range ((integralSingularChains X).d 2 1).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczOneVertexPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczOneVertexPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczOneVertexPairing ``Submission.DifferentialGeometry.Topology.HurewiczOneVertexPairing

def HurewiczOneMultiplicative (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) (a b : HomotopyGroup (Fin 1) X x),
    sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczOneMultiplicative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczOneMultiplicative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczOneMultiplicative ``Submission.DifferentialGeometry.Topology.HurewiczOneMultiplicative

def HurewiczOneKernel (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) (a : HomotopyGroup (Fin 1) X x),
    sphereHurewicz 0 x c a = 0 → a ∈ commutator (HomotopyGroup (Fin 1) X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.HurewiczOneKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.HurewiczOneKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.HurewiczOneKernel ``Submission.DifferentialGeometry.Topology.HurewiczOneKernel

theorem hurewiczOneLoopGeneration_punit (x : PUnit.{u + 1}) : HurewiczOneLoopGeneration x := by
  have hsub : Subsingleton (integralSingularHomology 1 (PUnit.{u + 1})) :=
    integralSingularHomology_subsingleton_of_contractible (X := PUnit.{u + 1}) 1 (by omega)
  intro y
  rw [@Subsingleton.elim _ hsub y 0]
  exact Submodule.zero_mem _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczOneLoopGeneration_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczOneLoopGeneration_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczOneLoopGeneration_punit ``Submission.DifferentialGeometry.Topology.hurewiczOneLoopGeneration_punit

noncomputable def abelianization_equiv_of_surjective_ker_eq_commutator {G : Type*} [Group G]
    {A : Type*} [CommGroup A] (f : G →* A) (hsurj : Function.Surjective f)
    (hker : f.ker = commutator G) : Abelianization G ≃* A :=
  QuotientGroup.liftEquiv (commutator G) hsurj hker.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.abelianization_equiv_of_surjective_ker_eq_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.abelianization_equiv_of_surjective_ker_eq_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.abelianization_equiv_of_surjective_ker_eq_commutator ``Submission.DifferentialGeometry.Topology.abelianization_equiv_of_surjective_ker_eq_commutator

def hurewiczSphereMonoidHom (x : X)
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b) :
    HomotopyGroup (Fin 1) X x →* Multiplicative (integralSingularHomology 1 X) where
  toFun a := Multiplicative.ofAdd (sphereHurewicz 0 x c a)
  map_one' := by rw [sphereHurewicz_one]; rfl
  map_mul' a b := by rw [hmul]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczSphereMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczSphereMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczSphereMonoidHom ``Submission.DifferentialGeometry.Topology.hurewiczSphereMonoidHom

theorem abelianizationHomotopyGroupOne_equiv_of_hurewiczOne [PathConnectedSpace X] (x : X)
    (c : integralSingularHomology (0 + 1) (liftedHomotopySphere.{u} 0))
    (hmul : ∀ a b : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b)
    (hsurj : Function.Surjective (sphereHurewicz 0 x c))
    (hker : ∀ a : HomotopyGroup (Fin 1) X x, sphereHurewicz 0 x c a = 0 →
      a ∈ commutator (HomotopyGroup (Fin 1) X x)) :
    Nonempty (Abelianization (HomotopyGroup (Fin 1) X x) ≃*
      Multiplicative (integralSingularHomology 1 X)) := by
  refine ⟨abelianization_equiv_of_surjective_ker_eq_commutator
    (hurewiczSphereMonoidHom x c hmul) ?_ ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := hsurj (Multiplicative.toAdd y)
    exact ⟨a, by simpa [hurewiczSphereMonoidHom] using congrArg Multiplicative.ofAdd ha⟩
  · refine le_antisymm ?_ (Abelianization.commutator_subset_ker _)
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact hker a (by simpa [hurewiczSphereMonoidHom] using ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_hurewiczOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_hurewiczOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_hurewiczOne ``Submission.DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_hurewiczOne


end DifferentialGeometry.Topology
