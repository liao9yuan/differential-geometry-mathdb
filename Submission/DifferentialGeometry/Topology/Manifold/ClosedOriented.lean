import Submission.DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u v w

structure ClosedOrientedManifold (n : ℕ) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) Carrier]
  [smooth : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  orientation : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Carrier n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold

attribute [instance] ClosedOrientedManifold.topology ClosedOrientedManifold.charts
  ClosedOrientedManifold.smooth ClosedOrientedManifold.hausdorff ClosedOrientedManifold.compact

namespace ClosedOrientedManifold

variable {n : ℕ}

def opposite (M : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{u} n where
  Carrier := M.Carrier
  orientation := M.orientation.opposite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.opposite

@[simp] theorem opposite_carrier (M : ClosedOrientedManifold.{u} n) :
    M.opposite.Carrier = M.Carrier := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_carrier ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_carrier

@[simp] theorem opposite_orientation (M : ClosedOrientedManifold.{u} n) :
    M.opposite.orientation = M.orientation.opposite := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_orientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_orientation

@[simp] theorem opposite_opposite (M : ClosedOrientedManifold.{u} n) :
    M.opposite.opposite = M := by
  cases M
  dsimp only [opposite]
  congr 1
  exact ManifoldOrientation.opposite_opposite _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_opposite ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.opposite_opposite

abbrev OrientedDiffeomorph (M : ClosedOrientedManifold.{u} n)
    (N : ClosedOrientedManifold.{v} n) :=
  {f : M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N.Carrier //
    f.preservesOrientation M.orientation N.orientation}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph

def OrientedDiffeomorph.refl (M : ClosedOrientedManifold.{u} n) :
    OrientedDiffeomorph M M :=
  ⟨Diffeomorph.refl _ _ ∞, Diffeomorph.preservesOrientation_refl M.orientation⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.refl ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.refl

def OrientedDiffeomorph.symm {M : ClosedOrientedManifold.{u} n}
    {N : ClosedOrientedManifold.{v} n} (f : OrientedDiffeomorph M N) :
    OrientedDiffeomorph N M :=
  ⟨f.1.symm, Diffeomorph.preservesOrientation_symm f.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.symm ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.symm

def OrientedDiffeomorph.trans {M : ClosedOrientedManifold.{u} n}
    {N : ClosedOrientedManifold.{v} n} {P : ClosedOrientedManifold.{w} n}
    (f : OrientedDiffeomorph M N) (g : OrientedDiffeomorph N P) :
    OrientedDiffeomorph M P :=
  ⟨f.1.trans g.1, Diffeomorph.preservesOrientation_trans f.2 g.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.trans ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph.trans

end ClosedOrientedManifold

structure ConnectedClosedOrientedManifold (n : ℕ) extends ClosedOrientedManifold.{u} n where
  [connected : ConnectedSpace Carrier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold

attribute [instance] ConnectedClosedOrientedManifold.connected

namespace ConnectedClosedOrientedManifold

variable {n : ℕ}

def opposite (M : ConnectedClosedOrientedManifold.{u} n) :
    ConnectedClosedOrientedManifold.{u} n where
  toClosedOrientedManifold := M.toClosedOrientedManifold.opposite
  connected := M.connected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite

@[simp] theorem opposite_carrier (M : ConnectedClosedOrientedManifold.{u} n) :
    M.opposite.Carrier = M.Carrier := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite_carrier ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.opposite_carrier

end ConnectedClosedOrientedManifold

end DifferentialGeometry.Topology
