import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import Submission.DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeModel := 𝓘(ℝ, ThreeSpace)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeModel

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def tangentChartEquiv (p x : M)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    TangentSpace ThreeModel x ≃ₗ[ℝ] ThreeSpace :=
  (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).linearEquivAt ℝ x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv

structure TangentOrientationSection where
  orientation : (x : M) → Orientation ℝ (TangentSpace ThreeModel x) (Fin 3)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin 3) (tangentChartEquiv M p y (hU hy)) (orientation y) =
          Orientation.map (Fin 3) (tangentChartEquiv M p x hx) (orientation x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection

variable {M}


def TangentOrientationSection.restrictOpen
    (o : TangentOrientationSection M) (U : TopologicalSpace.Opens M) :
    TangentOrientationSection U where
  orientation x := o.orientation x.1
  locally_constant := by
    let O : DifferentialGeometry.ManifoldOrientation ThreeModel M 3 :=
      { dimension_eq := by simp
        orientation := o.orientation
        locally_constant := o.locally_constant }
    exact (O.restrictOpen U).locally_constant

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen

@[simp]
theorem TangentOrientationSection.restrictOpen_orientation
    (o : TangentOrientationSection M) (U : TopologicalSpace.Opens M) (x : U) :
    (o.restrictOpen U).orientation x = o.orientation x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen_orientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.restrictOpen_orientation


def TangentOrientationSection.inChart (o : TangentOrientationSection M) (p x : M)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    Orientation ℝ ThreeSpace (Fin 3) :=
  Orientation.map (Fin 3) (tangentChartEquiv M p x hx) (o.orientation x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.inChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.inChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.inChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.inChart

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]

def PreservesTangentOrientationAt (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) : Prop :=
  Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf)
      (oM.orientation x) = oN.orientation (f x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientationAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientationAt

def PreservesTangentOrientation (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) : Prop :=
  ContMDiff ThreeModel ThreeModel ∞ f ∧
    ∀ x : M, ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x),
      PreservesTangentOrientationAt oM oN f x hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PreservesTangentOrientation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
