import Submission.DifferentialGeometry.Topology.SphereSeparation.SubdivisionBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def singularBarycentricSubdivision (X : TopCat) :
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X ⟶
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  barycentricSubdivisionChainEndomorphism X
    (barycentricSubdivisionBoundaryCompatible X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision

@[simp]
theorem singularBarycentricSubdivision_f
    (X : TopCat) (n : ℕ) :
    (singularBarycentricSubdivision X).f n =
      barycentricSubdivisionDegreeMap X n :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f

theorem singularBarycentricSubdivision_f_zero (X : TopCat) :
    (singularBarycentricSubdivision X).f 0 = 𝟙 _ :=
  barycentricSubdivisionDegreeMap_zero X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_f_zero


theorem singularBarycentricSubdivision_naturality
    {X Y : TopCat} (f : X ⟶ Y) :
    singularBarycentricSubdivision X ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        singularBarycentricSubdivision Y :=
  barycentricSubdivisionChainEndomorphism_naturality f
    (barycentricSubdivisionBoundaryCompatible X)
    (barycentricSubdivisionBoundaryCompatible Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivision_naturality


noncomputable def singularBarycentricSubdivisionIterate
    (X : TopCat) : (k : ℕ) →
    _root_.CategoryTheory.End (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)
  | 0 => 𝟙 _
  | k + 1 => singularBarycentricSubdivisionIterate X k ≫
      singularBarycentricSubdivision X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate

@[simp]
theorem singularBarycentricSubdivisionIterate_zero (X : TopCat) :
    singularBarycentricSubdivisionIterate X 0 = 𝟙 _ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_zero

theorem singularBarycentricSubdivisionIterate_succ
    (X : TopCat) (k : ℕ) :
    singularBarycentricSubdivisionIterate X (k + 1) =
      singularBarycentricSubdivisionIterate X k ≫
        singularBarycentricSubdivision X := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_succ ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_succ


theorem singularBarycentricSubdivisionIterate_naturality
    {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    singularBarycentricSubdivisionIterate X k ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        singularBarycentricSubdivisionIterate Y k := by
  induction k with
  | zero => simp [singularBarycentricSubdivisionIterate]
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ,
        singularBarycentricSubdivisionIterate_succ,
        Category.assoc, singularBarycentricSubdivision_naturality,
        ← Category.assoc, ih, Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_naturality

@[simp]
theorem singularBarycentricSubdivisionIterate_f_zero
    (X : TopCat) (k : ℕ) :
    (singularBarycentricSubdivisionIterate X k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp [singularBarycentricSubdivisionIterate]
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ]
      simp only [HomologicalComplex.comp_f,
        singularBarycentricSubdivision_f_zero, ih, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_f_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularBarycentricSubdivisionIterate_f_zero

end DifferentialGeometry.Topology.SphereSeparation
