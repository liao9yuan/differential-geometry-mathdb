/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def FreeSourceGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (y : M) : Prop :=
  ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x ∧ ∀ σ ∈ R.faces,
    x ∈ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) → ∀ v ∈ σ, v ∉ Ac.space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.FreeSourceGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.FreeSourceGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.FreeSourceGerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.FreeSourceGerm

def IsFreeDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∉ BdM ∧ FreeSourceGerm R Ac g S y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDoubleGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDoubleGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDoubleGerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDoubleGerm

def IsFreeBoundaryDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  y ∈ BdM ∧ FreeSourceGerm R Ac g S y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeBoundaryDoubleGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsFreeBoundaryDoubleGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeBoundaryDoubleGerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsFreeBoundaryDoubleGerm

def IsFreeInteriorDoubleGerm (R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2))) (BdM : Set M)
    (y : M) : Prop :=
  IsFreeDoubleGerm R Ac g S BdM y ∧
    ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeInteriorDoubleGerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsFreeInteriorDoubleGerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeInteriorDoubleGerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsFreeInteriorDoubleGerm

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open _root_.Classical in
noncomputable def regionGluedMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) → M :=
  fun x => if x ∈ Rc.space then ec.symm (simplicialMap Rs φ x) else D x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regionGluedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regionGluedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regionGluedMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regionGluedMap

end MetricAmbient

end DifferentialGeometry.Topology.PiecewiseLinear
