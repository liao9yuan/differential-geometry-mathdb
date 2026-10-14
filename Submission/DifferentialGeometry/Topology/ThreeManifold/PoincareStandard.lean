import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import Submission.DifferentialGeometry.Topology.Manifold.Components
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

structure PoincareStandardPresentation (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  standard : ∀ F ∈ factors, isStandardFactor F
  diffeomorph : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ (finiteConnectedSum factors).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PoincareStandardPresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PoincareStandardPresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PoincareStandardPresentation ``Submission.DifferentialGeometry.Topology.PoincareStandardPresentation

def isPoincareStandard (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  Nonempty (PoincareStandardPresentation M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard ``Submission.DifferentialGeometry.Topology.isPoincareStandard

theorem isPoincareStandard_connectedSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isPoincareStandard M) :
    ConnectedSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.toHomeomorph.connectedSpace_iff.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_connectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_connectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_connectedSpace ``Submission.DifferentialGeometry.Topology.isPoincareStandard_connectedSpace

theorem isPoincareStandard_compactSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isPoincareStandard M) :
    CompactSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.symm.toHomeomorph.compactSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_compactSpace ``Submission.DifferentialGeometry.Topology.isPoincareStandard_compactSpace

theorem not_isPoincareStandard_of_isEmpty (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsEmpty M] : ¬isPoincareStandard M := by
  intro h
  let := isPoincareStandard_connectedSpace h
  exact isEmptyElim (Classical.choice (inferInstance : Nonempty M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_isPoincareStandard_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_isPoincareStandard_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_isPoincareStandard_of_isEmpty ``Submission.DifferentialGeometry.Topology.not_isPoincareStandard_of_isEmpty

theorem isPoincareStandard_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (hN : isPoincareStandard N) :
    isPoincareStandard M := by
  obtain ⟨p⟩ := hN
  exact ⟨⟨p.factors, p.standard, f.trans p.diffeomorph⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph ``Submission.DifferentialGeometry.Topology.isPoincareStandard_of_diffeomorph

theorem isPoincareStandard_iff_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    isPoincareStandard M ↔ isPoincareStandard N :=
  ⟨isPoincareStandard_of_diffeomorph f.symm, isPoincareStandard_of_diffeomorph f⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_iff_of_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_iff_of_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_iff_of_diffeomorph ``Submission.DifferentialGeometry.Topology.isPoincareStandard_iff_of_diffeomorph

theorem isPoincareStandard_finite_sum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isStandardFactor F) : isPoincareStandard (finiteConnectedSum L).Carrier :=
  ⟨⟨L, hL, Diffeomorph.refl _ _ ∞⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_finite_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_finite_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_finite_sum ``Submission.DifferentialGeometry.Topology.isPoincareStandard_finite_sum

theorem isPoincareStandard_sphere : isPoincareStandard standardThreeSphereLift.{u}.Carrier := by
  exact isPoincareStandard_finite_sum [] (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_sphere ``Submission.DifferentialGeometry.Topology.isPoincareStandard_sphere

theorem isPoincareStandard_of_standard_factor (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor M) : isPoincareStandard M.Carrier := by
  exact isPoincareStandard_finite_sum [M] (by simpa using h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_of_standard_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_of_standard_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_of_standard_factor ``Submission.DifferentialGeometry.Topology.isPoincareStandard_of_standard_factor

@[simp] theorem isPoincareStandard_opposite_iff (M : ConnectedClosedOrientedManifold.{u} 3) :
    isPoincareStandard M.opposite.Carrier ↔ isPoincareStandard M.Carrier := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_opposite_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_opposite_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_opposite_iff ``Submission.DifferentialGeometry.Topology.isPoincareStandard_opposite_iff

def componentIsPoincareStandard (M : ClosedOrientedManifold.{u} 3)
    (C : ConnectedComponents M.Carrier) : Prop :=
  isPoincareStandard (M.component C).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.componentIsPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.componentIsPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.componentIsPoincareStandard ``Submission.DifferentialGeometry.Topology.componentIsPoincareStandard

def SphericalCutCapTransition.poincareControlled {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) : Prop :=
  E.controlledBy componentIsPoincareStandard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled

theorem SphericalCutCapTransition.poincareControlled_iff
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q) :
    E.poincareControlled ↔
      ∀ C : ConnectedComponents E.discarded.Carrier,
        isPoincareStandard (E.discarded.component C).Carrier := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_iff ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_iff

def FiniteCutCapTrace.poincareControlled (T : FiniteCutCapTrace.{u}) : Prop :=
  T.controlledBy componentIsPoincareStandard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled

theorem FiniteCutCapTrace.poincareControlled_iff (T : FiniteCutCapTrace.{u}) :
    T.poincareControlled ↔ ∀ i : Fin T.eventCount, (T.transition i).poincareControlled := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_iff ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_iff

theorem FiniteCutCapTrace.discarded_poincareStandard (T : FiniteCutCapTrace.{u})
    (h : T.poincareControlled) (i : Fin T.eventCount)
    (C : ConnectedComponents (T.transition i).discarded.Carrier) :
    isPoincareStandard ((T.transition i).discarded.component C).Carrier := h i C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.discarded_poincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.discarded_poincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.discarded_poincareStandard ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.discarded_poincareStandard

end DifferentialGeometry.Topology
