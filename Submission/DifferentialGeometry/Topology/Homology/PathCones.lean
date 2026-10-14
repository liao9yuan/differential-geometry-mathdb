import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathCones

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularConeTriangle_face (a : X) (σ : integralSingularSimplex 1 X)
    (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralSingularConeTriangle a σ) =
      ![integralPathSimplex (integralSimplexPath σ),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)))] i :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose_spec i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTriangle_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTriangle_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTriangle_face ``Submission.DifferentialGeometry.Topology.integralSingularConeTriangle_face

@[simp] theorem integralSingularConeTriangle_face_zero (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle a σ) = σ := by
  rw [integralSingularConeTriangle_face]
  exact integralPathSimplex_simplexPath σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTriangle_face_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTriangle_face_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTriangle_face_zero ``Submission.DifferentialGeometry.Topology.integralSingularConeTriangle_face_zero

@[simp] theorem integralSingularConeTriangle_face_one (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle a σ) =
      integralPathSimplex (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))) := by
  exact integralSingularConeTriangle_face a σ 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTriangle_face_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTriangle_face_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTriangle_face_one ``Submission.DifferentialGeometry.Topology.integralSingularConeTriangle_face_one

@[simp] theorem integralSingularConeTriangle_face_two (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle a σ) =
      integralPathSimplex (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))) := by
  exact integralSingularConeTriangle_face a σ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeTriangle_face_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeTriangle_face_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeTriangle_face_two ``Submission.DifferentialGeometry.Topology.integralSingularConeTriangle_face_two

end DifferentialGeometry.Topology
