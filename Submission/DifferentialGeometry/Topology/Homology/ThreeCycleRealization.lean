import Submission.DifferentialGeometry.Topology.Homology.TwoCycleRealization
import Submission.DifferentialGeometry.Topology.Homology.SimplexFilling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [hpi : Subsingleton (HomotopyGroup (Fin 2) X x)]

def integralSingularConeTetrahedron (σ : integralSingularSimplex 2 X) :
    integralSingularSimplex 3 X :=
  (exists_integralSingularSimplex_of_compatible_faces 1 x (integralSingularConeFaces x σ)
    (integralSingularConeFaces_compatible x σ)).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTetrahedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTetrahedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTetrahedron ``Submission.DifferentialGeometry.Topology.integralSingularConeTetrahedron

theorem integralSingularConeTetrahedron_face (σ : integralSingularSimplex 2 X)
    (i : Fin 4) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralSingularConeTetrahedron x σ) =
      integralSingularConeFaces x σ i :=
  (exists_integralSingularSimplex_of_compatible_faces 1 x (integralSingularConeFaces x σ)
    (integralSingularConeFaces_compatible x σ)).choose_spec i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTetrahedron_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTetrahedron_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTetrahedron_face ``Submission.DifferentialGeometry.Topology.integralSingularConeTetrahedron_face

def integralSingularConeTwo :
    (integralSingularChains X).X 2 →ₗ[ℤ] (integralSingularChains X).X 3 :=
  (integralSingularChainBasis 2 X).constr (M' := (integralSingularChains X).X 3) ℕ
    (fun σ => integralSimplexChain 3 (integralSingularConeTetrahedron x σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTwo ``Submission.DifferentialGeometry.Topology.integralSingularConeTwo

theorem integralSingularConeTwo_simplex (σ : integralSingularSimplex 2 X) :
    integralSingularConeTwo x (integralSimplexChain 2 σ) =
      integralSimplexChain 3 (integralSingularConeTetrahedron x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 2 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTwo_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTwo_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTwo_simplex ``Submission.DifferentialGeometry.Topology.integralSingularConeTwo_simplex

theorem integralSingularConeTetrahedron_boundary (σ : integralSingularSimplex 2 X) :
    (integralSingularChains X).d 3 2
      (integralSimplexChain 3 (integralSingularConeTetrahedron x σ)) =
      integralSimplexChain 2 σ - integralSingularConeOne x
        ((integralSingularChains X).d 2 1 (integralSimplexChain 2 σ)) := by
  rw [integralSimplexChain_boundary]
  simp only [integralSingularConeTetrahedron_face]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2
    (integralSingularConeFaces x σ i)) = _
  rw [Fin.sum_univ_four, integralSimplexChain_boundary_two, map_add, map_sub,
    integralSingularConeOne_simplex, integralSingularConeOne_simplex,
    integralSingularConeOne_simplex]
  norm_num
  dsimp [integralSingularConeFaces, Fin.cons]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTetrahedron_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTetrahedron_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTetrahedron_boundary ``Submission.DifferentialGeometry.Topology.integralSingularConeTetrahedron_boundary

theorem integralSingularConeTwo_equation :
    ((integralSingularChains X).d 3 2).hom.comp (integralSingularConeTwo x) =
      LinearMap.id - (integralSingularConeOne x).comp ((integralSingularChains X).d 2 1).hom := by
  apply (integralSingularChainBasis 2 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, LinearMap.comp_apply,
    integralSingularConeTwo_simplex, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  exact integralSingularConeTetrahedron_boundary x σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTwo_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTwo_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTwo_equation ``Submission.DifferentialGeometry.Topology.integralSingularConeTwo_equation

theorem integralSingularConeTwo_bounds (z : (integralSingularChains X).X 2)
    (hz : (integralSingularChains X).d 2 1 z = 0) :
    (integralSingularChains X).d 3 2 (integralSingularConeTwo x z) = z := by
  have h := LinearMap.congr_fun (integralSingularConeTwo_equation x) z
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hz, map_zero, sub_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTwo_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTwo_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTwo_bounds ``Submission.DifferentialGeometry.Topology.integralSingularConeTwo_bounds

def integralSingularThreeCycleProjection :
    (integralSingularChains X).X 3 →ₗ[ℤ] integralSingularCycles 2 X :=
  (LinearMap.id - (integralSingularConeTwo x).comp
    ((integralSingularChains X).d 3 2).hom).codRestrict (integralSingularCycles 2 X) fun z => by
      change (integralSingularChains X).d 3 2
        (z - integralSingularConeTwo x ((integralSingularChains X).d 3 2 z)) = 0
      rw [map_sub, integralSingularConeTwo_bounds, sub_self]
      exact congrArg (fun f => f z) ((integralSingularChains X).d_comp_d 3 2 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularThreeCycleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularThreeCycleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularThreeCycleProjection ``Submission.DifferentialGeometry.Topology.integralSingularThreeCycleProjection

theorem integralSingularThreeCycleProjection_val (z : (integralSingularChains X).X 3) :
    (integralSingularThreeCycleProjection x z).val =
      z - integralSingularConeTwo x ((integralSingularChains X).d 3 2 z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularThreeCycleProjection_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularThreeCycleProjection_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularThreeCycleProjection_val ``Submission.DifferentialGeometry.Topology.integralSingularThreeCycleProjection_val

@[simp] theorem integralSingularThreeCycleProjection_cycle (z : integralSingularCycles 2 X) :
    integralSingularThreeCycleProjection x z.val = z := by
  apply Subtype.ext
  rw [integralSingularThreeCycleProjection_val]
  have hz : (integralSingularChains X).d 3 2 z.val = 0 := z.property
  rw [hz, map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularThreeCycleProjection_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularThreeCycleProjection_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularThreeCycleProjection_cycle ``Submission.DifferentialGeometry.Topology.integralSingularThreeCycleProjection_cycle

def integralSingularConeThreeFaces (σ : integralSingularSimplex 3 X) :
    Fin 5 → integralSingularSimplex 3 X :=
  Fin.cons σ fun i => integralSingularConeTetrahedron x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeFaces ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeFaces

theorem integralSingularConeThreeFaces_compatible (σ : integralSingularSimplex 3 X)
    (i : Fin 5) (j : Fin 4) :
    (TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeThreeFaces x σ i) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
        (integralSingularConeThreeFaces x σ (i.succAbove j)) := by
  have h00 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 0
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 0 by decide))
  have h01 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 1 by decide))
  have h02 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (0 : Fin 3) ≤ 2 by decide))
  have h11 : (TopCat.toSSet.obj (TopCat.of X)).δ 1
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (1 : Fin 3) ≤ 1 by decide))
  have h12 : (TopCat.toSSet.obj (TopCat.of X)).δ 1
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (1 : Fin 3) ≤ 2 by decide))
  have h22 : (TopCat.toSSet.obj (TopCat.of X)).δ 2
      ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ
      (show (2 : Fin 3) ≤ 2 by decide))
  fin_cases i <;> fin_cases j
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h00]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h01]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h02]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h00]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h11]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h12]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h01]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h11]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ))
    rw [h22]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 σ
    simp only [integralSingularConeTetrahedron_face]
    rfl
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    rw [h02]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    rw [h12]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 3 (integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTetrahedron_face]
    change integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 3 σ)) = integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    rw [h22]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeFaces_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeFaces_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeFaces_compatible ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeFaces_compatible

private def integralSingularConeThreeBoundaryMap (σ : integralSingularSimplex 3 X) :
    C(DifferentialGeometry.Simplex.boundary (Fin 5), X) :=
  DifferentialGeometry.Simplex.boundaryDesc
    (fun i => integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i))
    (fun i j p => by
      have h := congrArg (fun s => integralSingularSimplexEquiv 2 X s p)
        (integralSingularConeThreeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j
          (integralSingularConeThreeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeThreeFaces x σ (i.succAbove j))) p at h
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
      exact h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeBoundaryMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularConeThreeBoundaryMap target :: scope.openDecls } }

def integralSingularConeThreeSphereMap (σ : integralSingularSimplex 3 X) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) :=
  (integralSingularConeThreeBoundaryMap x σ).comp
    ⟨(DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm,
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 4) ℝ).symm).symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeSphereMap

theorem integralSingularConeThreeSphereMap_simplexBoundarySphereChain
    (σ : integralSingularSimplex 3 X) :
    (integralSingularChainMap
      ((integralSingularConeThreeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain.{u} 2) =
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)).val := by
  have h := integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain 2
    (fun i => integralSingularSimplexEquiv 3 X (integralSingularConeThreeFaces x σ i))
    (by
      intro i j p
      have he := congrArg (fun s => integralSingularSimplexEquiv 2 X s p)
        (integralSingularConeThreeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j
          (integralSingularConeThreeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeThreeFaces x σ (i.succAbove j))) p at he
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at he
      exact he)
  change (integralSingularChainMap
      ((integralSingularConeThreeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain 2) = _ at h
  rw [h]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • integralSimplexChain 3
    (integralSingularConeThreeFaces x σ i)) = _
  rw [integralSingularThreeCycleProjection_val, integralSimplexChain_boundary,
    map_sum]
  simp only [map_zsmul, integralSingularConeTwo_simplex]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • integralSimplexChain 3
      (integralSingularConeThreeFaces x σ i)) =
    integralSimplexChain 3 σ - ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      integralSimplexChain 3 (integralSingularConeTetrahedron x
        ((TopCat.toSSet.obj (TopCat.of X)).δ i σ))
  have hz : integralSingularConeThreeFaces x σ 0 = σ := rfl
  have hs (i : Fin 4) : integralSingularConeThreeFaces x σ i.succ =
      integralSingularConeTetrahedron x ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := rfl
  rw [Fin.sum_univ_succ, hz]
  simp only [hs, Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ,
    mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  exact (sub_eq_add_neg _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereChain ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereChain

theorem span_integralSingularThreeCycleProjection :
    Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
      integralSingularCycleClass 2 X
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)))) = ⊤ := by
  let f := (integralSingularCycleClassLinearMap 2 X).comp (integralSingularThreeCycleProjection x)
  have hspan : Submodule.span ℤ (Set.range (integralSingularChainBasis 3 X)) ≤
      Submodule.comap f (Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ))))) := by
    rw [Submodule.span_le]
    rintro z ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨σ, by
      simp only [f, LinearMap.comp_apply, integralSingularChainBasis_apply,
        integralSingularCycleClassLinearMap_apply]⟩
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 2 X y
  have hz : f z.val ∈ Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 3 X =>
      integralSingularCycleClass 2 X
        (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)))) := by
    apply hspan
    rw [Basis.span_eq]
    exact Submodule.mem_top
  simpa only [f, LinearMap.comp_apply, integralSingularThreeCycleProjection_cycle,
    integralSingularCycleClassLinearMap_apply] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_integralSingularThreeCycleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_integralSingularThreeCycleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_integralSingularThreeCycleProjection ``Submission.DifferentialGeometry.Topology.span_integralSingularThreeCycleProjection

theorem integralSingularConeThreeSphereMap_simplexBoundarySphereClass
    (σ : integralSingularSimplex 3 X) :
    freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)) =
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
    integralSingularCycleClass_map]
  congr 1
  apply Subtype.ext
  rw [integralSingularCycleMap_val]
  exact integralSingularConeThreeSphereMap_simplexBoundarySphereChain x σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.integralSingularConeThreeSphereMap_simplexBoundarySphereClass

include hpi in
theorem span_range_freeSphereHomologyImage_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 2 c)) = ⊤ := by
  obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 2 c).mp hc
    (simplexBoundarySphereClass.{u} 2)
  apply top_unique
  rw [← span_integralSingularThreeCycleProjection x]
  apply Submodule.span_le.mpr
  rintro y ⟨σ, rfl⟩
  change integralSingularCycleClass 2 X
      (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) ∈ _
  rw [← integralSingularConeThreeSphereMap_simplexBoundarySphereClass, hk,
    freeSphereHomologyImage_zsmul]
  have hm : freeSphereHomologyImage (X := X) 2 c
      (ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ)) ∈
      Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 2 c)) :=
    Submodule.subset_span ⟨ZerothHomotopy.mk (integralSingularConeThreeSphereMap x σ), rfl⟩
  exact zsmul_mem hm k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_three ``Submission.DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_three

include hpi in
theorem span_range_sphereHurewicz_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Submodule.span ℤ (Set.range (sphereHurewicz 2 x c)) = ⊤ := by
  rw [sphereHurewicz,
    (homotopyGroupToFreeSphere_surjective 2 x).range_comp (freeSphereHomologyImage 2 c)]
  exact span_range_freeSphereHomologyImage_three x c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_range_sphereHurewicz_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_range_sphereHurewicz_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_range_sphereHurewicz_three ``Submission.DifferentialGeometry.Topology.span_range_sphereHurewicz_three

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup
    (x : X) [hpi : Subsingleton (HomotopyGroup (Fin 2) X x)]
    [Subsingleton (HomotopyGroup (Fin 3) X x)] :
    Subsingleton (integralSingularHomology 3 X) := by
  have hspan := span_range_sphereHurewicz_three x
    (integralLiftedSphereGenerator.{u} 2)
    (integralLiftedSphereGenerator_isGenerator 2)
  have hzero : Submodule.span ℤ
      (Set.range (sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro y ⟨a, rfl⟩
    rw [Subsingleton.elim a 1, sphereHurewicz_one]
  have ht : (⊤ : Submodule ℤ (integralSingularHomology 3 X)) = ⊥ := hspan.symm.trans hzero
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have h : a ∈ (⊤ : Submodule ℤ (integralSingularHomology 3 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  have hb : b = 0 := by
    have h : b ∈ (⊤ : Submodule ℤ (integralSingularHomology 3 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  exact ha.trans hb.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup ``Submission.DifferentialGeometry.Topology.integralSingularHomology_three_subsingleton_of_subsingleton_homotopyGroup

end DifferentialGeometry.Topology
