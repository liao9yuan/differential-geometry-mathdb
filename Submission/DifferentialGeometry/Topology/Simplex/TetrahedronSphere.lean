import Submission.DifferentialGeometry.Topology.Simplex.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def tetrahedronSphereFaces (g : C(stdSimplex ℝ (Fin 4), X)) (x : X) :
    Fin 5 → C(stdSimplex ℝ (Fin 4), X) :=
  simplexSphereFaces g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronSphereFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronSphereFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronSphereFaces ``Submission.DifferentialGeometry.Simplex.tetrahedronSphereFaces

theorem tetrahedronSphereFaces_compatible (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x)
    (i : Fin 5) (j : Fin 4) (p : stdSimplex ℝ (Fin 3)) :
    tetrahedronSphereFaces g x i (stdSimplex.map j.succAbove p) =
      tetrahedronSphereFaces g x (i.succAbove j)
        (stdSimplex.map (j.predAbove i).succAbove p) :=
  simplexSphereFaces_compatible g x hg i j p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronSphereFaces_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronSphereFaces_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronSphereFaces_compatible ``Submission.DifferentialGeometry.Simplex.tetrahedronSphereFaces_compatible

def tetrahedronSphereMap (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) :=
  simplexSphereMap g x hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronSphereMap ``Submission.DifferentialGeometry.Simplex.tetrahedronSphereMap

theorem tetrahedronSphereMap_face (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x)
    (i : Fin 5) (p : stdSimplex ℝ (Fin 4)) :
    tetrahedronSphereMap g x hg
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 4) ℝ).symm
        ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) =
      tetrahedronSphereFaces g x i p :=
  simplexSphereMap_face g x hg i p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.tetrahedronSphereMap_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.tetrahedronSphereMap_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.tetrahedronSphereMap_face ``Submission.DifferentialGeometry.Simplex.tetrahedronSphereMap_face

end DifferentialGeometry.Simplex
