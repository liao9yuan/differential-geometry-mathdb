import Submission.DifferentialGeometry.Topology.Simplex.BoundaryGluing
import Mathlib.Topology.Homotopy.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def triangleSphereFaces (g : C(stdSimplex ℝ (Fin 3), X)) (x : X) :
    Fin 4 → C(stdSimplex ℝ (Fin 3), X) :=
  Fin.cons g (fun _ => ContinuousMap.const _ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleSphereFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleSphereFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleSphereFaces ``Submission.DifferentialGeometry.Simplex.triangleSphereFaces

theorem triangleSphereFaces_compatible (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    triangleSphereFaces g x i (stdSimplex.map j.succAbove p) =
      triangleSphereFaces g x (i.succAbove j)
        (stdSimplex.map (j.predAbove i).succAbove p) := by
  have h (k : Fin 3) : g (stdSimplex.map k.succAbove p) = x :=
    hg _ ⟨k, map_succAbove_apply_pivot k p⟩
  fin_cases i <;> fin_cases j <;> first
    | exact h _
    | exact (h _).symm
    | rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleSphereFaces_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleSphereFaces_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleSphereFaces_compatible ``Submission.DifferentialGeometry.Simplex.triangleSphereFaces_compatible

def triangleSphereMap (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X) :=
  boundarySphereDesc (triangleSphereFaces g x) (triangleSphereFaces_compatible g x hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.triangleSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.triangleSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.triangleSphereMap ``Submission.DifferentialGeometry.Simplex.triangleSphereMap

end DifferentialGeometry.Simplex
