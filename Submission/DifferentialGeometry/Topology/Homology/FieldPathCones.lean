/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.PathCones
import Submission.DifferentialGeometry.Topology.Homology.BettiNumber

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X]

abbrev fieldSingularChains : ChainComplex (ModuleCat k) ℕ :=
  ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat k)).obj (ModuleCat.of k k)).obj (TopCat.of X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularChains ``Submission.DifferentialGeometry.Topology.fieldSingularChains

def fieldSimplexChain (n : ℕ) (σ : integralSingularSimplex n X) :
    (fieldSingularChains (k := k) (X := X)).X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of k k) σ).hom 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSimplexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSimplexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSimplexChain ``Submission.DifferentialGeometry.Topology.fieldSimplexChain

def fieldSingularChainFinsuppIso (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).X n ≅
      ModuleCat.of k (integralSingularSimplex n X →₀ k) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    |>.coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit k k (integralSingularSimplex n X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularChainFinsuppIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularChainFinsuppIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularChainFinsuppIso ``Submission.DifferentialGeometry.Topology.fieldSingularChainFinsuppIso

def fieldSingularChainBasis (n : ℕ) :
    _root_.Module.Basis (integralSingularSimplex n X) k
      ((fieldSingularChains (k := k) (X := X)).X n) :=
  Basis.ofRepr (fieldSingularChainFinsuppIso (k := k) (X := X) n).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularChainBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularChainBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularChainBasis ``Submission.DifferentialGeometry.Topology.fieldSingularChainBasis

theorem fieldSingularChainFinsuppIso_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    (fieldSingularChainFinsuppIso (k := k) (X := X) n).hom
        (fieldSimplexChain (k := k) n σ) = Finsupp.single σ 1 := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan (ModuleCat.of k k) n)
    (ModuleCat.finsuppCoconeIsColimit k k (integralSingularSimplex n X)) ⟨σ⟩
  have he := congrArg (fun f => f.hom (1 : k)) h
  change (fieldSingularChainFinsuppIso (k := k) (X := X) n).hom
      (fieldSimplexChain (k := k) n σ) = (Finsupp.lsingle σ) 1 at he
  simpa only [Finsupp.lsingle_apply] using he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularChainFinsuppIso_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularChainFinsuppIso_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularChainFinsuppIso_simplex ``Submission.DifferentialGeometry.Topology.fieldSingularChainFinsuppIso_simplex

theorem fieldSingularChainBasis_apply (n : ℕ) (σ : integralSingularSimplex n X) :
    fieldSingularChainBasis (k := k) (X := X) n σ = fieldSimplexChain (k := k) n σ := by
  apply (fieldSingularChainBasis (k := k) (X := X) n).repr.injective
  rw [(fieldSingularChainBasis (k := k) (X := X) n).repr_self]
  exact (fieldSingularChainFinsuppIso_simplex (k := k) (X := X) n σ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularChainBasis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularChainBasis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularChainBasis_apply ``Submission.DifferentialGeometry.Topology.fieldSingularChainBasis_apply

theorem fieldSimplexChain_boundary (n : ℕ) (σ : integralSingularSimplex (n + 1) X) :
    (fieldSingularChains (k := k) (X := X)).d (n + 1) n
        (fieldSimplexChain (k := k) (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : k) ^ i.val •
        fieldSimplexChain (k := k) n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := ModuleCat.of k k) σ
  let ev : (ModuleCat.of k k ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of k k)).X n) →+
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of k k)).X n :=
    { toFun := fun f => f 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  refine he.trans ?_
  refine (map_sum ev _ Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul k]
  push_cast
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSimplexChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSimplexChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSimplexChain_boundary ``Submission.DifferentialGeometry.Topology.fieldSimplexChain_boundary

theorem fieldSimplexChain_boundary_one (σ : integralSingularSimplex 1 X) :
    (fieldSingularChains (k := k) (X := X)).d 1 0 (fieldSimplexChain (k := k) 1 σ) =
      fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) := by
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using fieldSimplexChain_boundary (k := k) 0 σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSimplexChain_boundary_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSimplexChain_boundary_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSimplexChain_boundary_one ``Submission.DifferentialGeometry.Topology.fieldSimplexChain_boundary_one

theorem fieldSimplexChain_boundary_two (σ : integralSingularSimplex 2 X) :
    (fieldSingularChains (k := k) (X := X)).d 2 1 (fieldSimplexChain (k := k) 2 σ) =
      fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) +
          fieldSimplexChain (k := k) 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) := by
  simpa [Fin.sum_univ_succ, Fin.sum_univ_two, sub_eq_add_neg, add_assoc] using
    fieldSimplexChain_boundary (k := k) 1 σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSimplexChain_boundary_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSimplexChain_boundary_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSimplexChain_boundary_two ``Submission.DifferentialGeometry.Topology.fieldSimplexChain_boundary_two

def fieldPathChain {x y : X} (p : Path x y) :
    (fieldSingularChains (k := k) (X := X)).X 1 :=
  fieldSimplexChain (k := k) 1 (integralPathSimplex p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldPathChain ``Submission.DifferentialGeometry.Topology.fieldPathChain

theorem fieldPathChain_simplexPath (σ : integralSingularSimplex 1 X) :
    fieldPathChain (k := k) (integralSimplexPath σ) = fieldSimplexChain (k := k) 1 σ := by
  unfold fieldPathChain
  rw [integralPathSimplex_simplexPath]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldPathChain_simplexPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldPathChain_simplexPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldPathChain_simplexPath ``Submission.DifferentialGeometry.Topology.fieldPathChain_simplexPath

variable [SimplyConnectedSpace X]

def fieldSingularConeZero (a : X) :
    (fieldSingularChains (k := k) (X := X)).X 0 →ₗ[k]
      (fieldSingularChains (k := k) (X := X)).X 1 :=
  (fieldSingularChainBasis (k := k) (X := X) 0).constr
    (M' := (fieldSingularChains (k := k) (X := X)).X 1) ℕ (fun σ =>
      fieldPathChain (k := k) (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeZero ``Submission.DifferentialGeometry.Topology.fieldSingularConeZero

theorem fieldSingularConeZero_simplex (a : X) (σ : integralSingularSimplex 0 X) :
    fieldSingularConeZero (k := k) a (fieldSimplexChain (k := k) 0 σ) =
      fieldPathChain (k := k) (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)) := by
  rw [← fieldSingularChainBasis_apply]
  exact (fieldSingularChainBasis (k := k) (X := X) 0).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeZero_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeZero_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeZero_simplex ``Submission.DifferentialGeometry.Topology.fieldSingularConeZero_simplex

def fieldSingularConeTriangle (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularSimplex 2 X :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeTriangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeTriangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeTriangle ``Submission.DifferentialGeometry.Topology.fieldSingularConeTriangle

theorem fieldSingularConeTriangle_faces (a : X) (σ : integralSingularSimplex 1 X) :
    ∀ i : Fin 3, (TopCat.toSSet.obj (TopCat.of X)).δ i (fieldSingularConeTriangle a σ) =
      ![integralPathSimplex (integralSimplexPath σ),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)))] i :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeTriangle_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeTriangle_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeTriangle_faces ``Submission.DifferentialGeometry.Topology.fieldSingularConeTriangle_faces

def fieldSingularConeOne (a : X) :
    (fieldSingularChains (k := k) (X := X)).X 1 →ₗ[k]
      (fieldSingularChains (k := k) (X := X)).X 2 :=
  (fieldSingularChainBasis (k := k) (X := X) 1).constr
    (M' := (fieldSingularChains (k := k) (X := X)).X 2) ℕ (fun σ =>
      fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeOne ``Submission.DifferentialGeometry.Topology.fieldSingularConeOne

theorem fieldSingularConeOne_simplex (a : X) (σ : integralSingularSimplex 1 X) :
    fieldSingularConeOne (k := k) a (fieldSimplexChain (k := k) 1 σ) =
      fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ) := by
  rw [← fieldSingularChainBasis_apply]
  exact (fieldSingularChainBasis (k := k) (X := X) 1).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeOne_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeOne_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeOne_simplex ``Submission.DifferentialGeometry.Topology.fieldSingularConeOne_simplex

theorem fieldSingularConeTriangle_boundary (a : X) (σ : integralSingularSimplex 1 X) :
    (fieldSingularChains (k := k) (X := X)).d 2 1
        (fieldSimplexChain (k := k) 2 (fieldSingularConeTriangle a σ)) =
      fieldSimplexChain (k := k) 1 σ -
        fieldSingularConeZero (k := k) a
          (fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) +
        fieldSingularConeZero (k := k) a
          (fieldSimplexChain (k := k) 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) := by
  rw [fieldSimplexChain_boundary_two]
  rw [fieldSingularConeTriangle_faces a σ 0, fieldSingularConeTriangle_faces a σ 1,
    fieldSingularConeTriangle_faces a σ 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change fieldPathChain (k := k) (integralSimplexPath σ) -
      fieldPathChain (k := k) (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))) +
      fieldPathChain (k := k) (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))) = _
  rw [fieldPathChain_simplexPath]
  rw [fieldSingularConeZero_simplex, fieldSingularConeZero_simplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeTriangle_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeTriangle_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeTriangle_boundary ``Submission.DifferentialGeometry.Topology.fieldSingularConeTriangle_boundary

theorem fieldSingularConeOne_equation (a : X) :
    ((fieldSingularChains (k := k) (X := X)).d 2 1).hom.comp
        (fieldSingularConeOne (k := k) a) =
      LinearMap.id - (fieldSingularConeZero (k := k) a).comp
        ((fieldSingularChains (k := k) (X := X)).d 1 0).hom := by
  apply (fieldSingularChainBasis (k := k) (X := X) 1).ext
  intro σ
  rw [fieldSingularChainBasis_apply]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    fieldSingularConeOne_simplex, fieldSingularConeTriangle_boundary,
    fieldSimplexChain_boundary_one, map_sub]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeOne_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeOne_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeOne_equation ``Submission.DifferentialGeometry.Topology.fieldSingularConeOne_equation

theorem fieldSingularConeOne_bounds (a : X)
    (c : (fieldSingularChains (k := k) (X := X)).X 1)
    (hc : (fieldSingularChains (k := k) (X := X)).d 1 0 c = 0) :
    (fieldSingularChains (k := k) (X := X)).d 2 1
        (fieldSingularConeOne (k := k) a c) = c := by
  have h := LinearMap.congr_fun (fieldSingularConeOne_equation (k := k) a) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hc, map_zero, sub_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularConeOne_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularConeOne_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularConeOne_bounds ``Submission.DifferentialGeometry.Topology.fieldSingularConeOne_bounds

omit [SimplyConnectedSpace X] in
theorem fieldSingularHomology_one_vanishing_iff :
    Subsingleton (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of X)) ↔
      ∀ c : (fieldSingularChains (k := k) (X := X)).X 1,
        (fieldSingularChains (k := k) (X := X)).d 1 0 c = 0 →
          ∃ b : (fieldSingularChains (k := k) (X := X)).X 2,
            (fieldSingularChains (k := k) (X := X)).d 2 1 b = c := by
  change Subsingleton ((fieldSingularChains (k := k) (X := X)).homology 1) ↔ _
  rw [← ModuleCat.isZero_iff_subsingleton,
    ← _root_.HomologicalComplex.exactAt_iff_isZero_homology,
    _root_.HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularHomology_one_vanishing_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularHomology_one_vanishing_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularHomology_one_vanishing_iff ``Submission.DifferentialGeometry.Topology.fieldSingularHomology_one_vanishing_iff

theorem fieldSingularHomology_one_subsingleton :
    Subsingleton (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 1).obj
      (ModuleCat.of k k)).obj (TopCat.of X)) := by
  apply fieldSingularHomology_one_vanishing_iff.mpr
  intro c hc
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨fieldSingularConeOne (k := k) a c, fieldSingularConeOne_bounds a c hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularHomology_one_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularHomology_one_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularHomology_one_subsingleton ``Submission.DifferentialGeometry.Topology.fieldSingularHomology_one_subsingleton

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Homology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem bettiOne_eq_zero_of_simplyConnectedSpace : bettiOne X = 0 := by
  let _ : Subsingleton (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 1).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)) :=
    Topology.fieldSingularHomology_one_subsingleton (k := ℚ) (X := X)
  exact Module.finrank_zero_of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiOne_eq_zero_of_simplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiOne_eq_zero_of_simplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiOne_eq_zero_of_simplyConnectedSpace ``Submission.DifferentialGeometry.Homology.bettiOne_eq_zero_of_simplyConnectedSpace

end DifferentialGeometry.Homology
