import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientationReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import Submission.DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionReconstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

theorem exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction
    {M : Topology.ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (W.isPoincareStandard hsum
      Topology.poincareStandardSumClosed_holds)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction

def smoothPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture

theorem smoothPoincareConjecture_of_poincareControlledExtinction
    (hsum : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)
  obtain ⟨o⟩ := Topology.Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  exact exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction
    (W := (hext { Carrier := M, orientation := o } g).some)
    (hsum := fun i => hsum _ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_poincareControlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_poincareControlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_poincareControlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_poincareControlledExtinction

def topologicalPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
    Nonempty (M ≃ₜ Topology.standardThreeSphereLift.{u}.Carrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture

theorem topologicalPoincareConjecture_of_smoothStructureInput
    (hsm : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ConnectedSpace M] [SimplyConnectedSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
      ∃ inst : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI := inst
        Nonempty (IsManifold (𝓡 3) ∞ M))
    (hsmooth : smoothPoincareConjecture.{u}) :
    topologicalPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _
  obtain ⟨inst, hman⟩ := hsm M
  let inst := inst
  let smooth : IsManifold (𝓡 3) ∞ M := hman.some
  exact ⟨(hsmooth M).some.toHomeomorph⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture_of_smoothStructureInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture_of_smoothStructureInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture_of_smoothStructureInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.topologicalPoincareConjecture_of_smoothStructureInput


theorem exists_diffeomorph_standardThreeSphere_of_controlledExtinction
    {M : ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) :=
  exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_controlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_controlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_controlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_diffeomorph_standardThreeSphere_of_controlledExtinction

theorem smoothPoincareConjecture_of_controlledExtinction
    (hext : ∀ (M : ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)
  obtain ⟨o⟩ := Topology.Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  exact exists_diffeomorph_standardThreeSphere_of_controlledExtinction
    (W := (hext { Carrier := M, orientation := o } g).some)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_controlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_controlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_controlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture_of_controlledExtinction

end DifferentialGeometry.PDE.RicciFlow.Surgery
