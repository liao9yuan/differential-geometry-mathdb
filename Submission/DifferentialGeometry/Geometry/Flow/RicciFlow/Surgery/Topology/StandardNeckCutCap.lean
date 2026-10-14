import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapTransitionSkeleton
import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private def sphereTwoPoint : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwoPoint target :: scope.openDecls } }

private def sphereThreePoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreePoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreePoint target :: scope.openDecls } }

def sphereThreeStage : OrientedThreeStage where
  Carrier := Sphere 3
  orientation := TangentOrientationSection.ofManifoldOrientation
    (DifferentialGeometry.sphereOrientation 3 (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage

theorem sphereThreeStage_nonempty : Nonempty sphereThreeStage.Carrier := ⟨sphereThreePoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_nonempty

def standardNeckTubeIsSmoothEmbedding : Prop :=
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeIsSmoothEmbedding

theorem standardNeckTubeSystem_tube_smooth (h : standardNeckTubeIsSmoothEmbedding) :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : standardNeckTubeSystem.Index,
      _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
        (standardNeckTubeSystem.tube a) := by
  intro a
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_tube_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_tube_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_tube_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_tube_smooth

theorem standardNeckTubeSystem_nontrivial :
    Nonempty standardNeckTubeSystem.Index ∨ Nonempty (Sphere 3) :=
  Or.inl standardNeckTubeSystem_index_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_nontrivial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_nontrivial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_nontrivial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_nontrivial

theorem standardNeckTubeSystem_boundarySpheres_disjoint :
    Disjoint (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.false)))
      (Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.true))) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  have h' : standardNeckTubeFun (x, TubeSystem.boundaryLevel _root_.Bool.false) =
      standardNeckTubeFun (y, TubeSystem.boundaryLevel _root_.Bool.true) := hy.symm
  have h2 : (TubeSystem.boundaryLevel _root_.Bool.false : ℝ) = (TubeSystem.boundaryLevel _root_.Bool.true : ℝ) :=
    congrArg (fun z : TubeDomain => (z.2 : ℝ)) (standardNeckTubeFun_injective h')
  exact absurd h2 (by norm_num [TubeSystem.boundaryLevel])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySpheres_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySpheres_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySpheres_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySpheres_disjoint

theorem standardNeckTubeSystem_boundarySphere_ne :
    standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.false) ≠
      standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.true) := by
  intro h
  have hmem : standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.false) sphereTwoPoint ∈
      Set.range (standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.true)) := by
    rw [← h]
    exact Set.mem_range_self _
  exact Set.disjoint_left.mp standardNeckTubeSystem_boundarySpheres_disjoint
    (Set.mem_range_self _) hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySphere_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySphere_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySphere_ne ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_boundarySphere_ne

theorem standardNeckTubeSystem_core_nonempty : (standardNeckTubeSystem.core).Nonempty :=
  ⟨standardNeckTubeSystem.boundarySphere (PUnit.unit, _root_.Bool.false) sphereTwoPoint,
    TubeSystem.boundarySphere_mem_core (T := standardNeckTubeSystem) _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_core_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_core_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_core_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_core_nonempty

theorem standardNeckTubeSystem_removedBand_ne_univ :
    standardNeckTubeSystem.removedBand PUnit.unit ≠ Set.univ := by
  intro h
  obtain ⟨x, hx⟩ := standardNeckTubeSystem_core_nonempty
  rw [TubeSystem.core, Set.mem_compl_iff] at hx
  exact hx (Set.mem_iUnion.mpr ⟨PUnit.unit, by rw [h]; exact Set.mem_univ x⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_ne_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_ne_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_ne_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardNeckTubeSystem_removedBand_ne_univ

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceThreeSpacePEmpty : ChartedSpace ThreeSpace PEmpty where
  atlas := ∅
  chartAt := fun x => PEmpty.elim x
  mem_chart_source := fun x => PEmpty.elim x
  chart_mem_atlas := fun x => PEmpty.elim x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceThreeSpacePEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceThreeSpacePEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceThreeSpacePEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceThreeSpacePEmpty

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelSomeENatTopPEmpty : IsManifold ThreeModel ∞ PEmpty where
  compatible := by
    intro e _ he _
    exact he.elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelSomeENatTopPEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelSomeENatTopPEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelSomeENatTopPEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelSomeENatTopPEmpty

private def emptyTangentOrientationSection : TangentOrientationSection PEmpty where
  orientation := fun x => PEmpty.elim x
  locally_constant := fun p => PEmpty.elim p

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTangentOrientationSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyTangentOrientationSection target :: scope.openDecls } }

def emptyOrientedThreeStage : OrientedThreeStage where
  Carrier := PEmpty
  orientation := emptyTangentOrientationSection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyOrientedThreeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyOrientedThreeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyOrientedThreeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyOrientedThreeStage

theorem SmoothCutCapTransition.nonempty_output {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty N.Carrier := by
  by_cases hI : Nonempty X.trace.tubes.Index
  · obtain ⟨a⟩ := hI
    exact ⟨X.trace.capping.cap (a, _root_.Bool.false) ⟨0, by simp [ThreeBall]⟩⟩
  · have hEmpty : IsEmpty X.trace.tubes.Index := ⟨fun a => hI ⟨a⟩⟩
    have hcore : X.trace.tubes.core = Set.univ :=
      @TubeSystem.core_eq_univ_of_isEmpty _ _ X.trace.tubes hEmpty
    obtain ⟨p⟩ := X.source_nonempty
    exact ⟨X.trace.capping.coreInclusion ⟨p, by rw [hcore]; exact Set.mem_univ p⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output

theorem SmoothCutCapTransition.nonempty_output_piece {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty Q.Carrier ∨ Nonempty D.Carrier := by
  obtain ⟨n⟩ := X.nonempty_output
  cases h : X.presentation n with
  | inl q => exact Or.inl ⟨q⟩
  | inr d => exact Or.inr ⟨d⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output_piece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output_piece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output_piece ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_output_piece

theorem not_nonempty_smoothCutCapTransition_of_isEmpty_pieces
    {P Q D N : OrientedThreeStage.{u}} (hQ : IsEmpty Q.Carrier) (hD : IsEmpty D.Carrier) :
    ¬ Nonempty (SmoothCutCapTransition P Q D N) := by
  rintro ⟨X⟩
  rcases X.nonempty_output_piece with h | h
  · exact hQ.false h.some
  · exact hD.false h.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_of_isEmpty_pieces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_of_isEmpty_pieces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_of_isEmpty_pieces ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_of_isEmpty_pieces

theorem not_nonempty_smoothCutCapTransition_empty_output (P N : OrientedThreeStage.{0}) :
    ¬ Nonempty (SmoothCutCapTransition P emptyOrientedThreeStage emptyOrientedThreeStage N) :=
  not_nonempty_smoothCutCapTransition_of_isEmpty_pieces PEmpty.instIsEmpty PEmpty.instIsEmpty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_empty_output then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_empty_output"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_empty_output ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_smoothCutCapTransition_empty_output

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
