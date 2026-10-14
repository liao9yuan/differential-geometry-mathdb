import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Submission.DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Connected.TotallyDisconnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × _root_.Set.Icc (-2 : ℝ) 2

local instance _root_.Submission.DifferentialGeometry.Topology.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instFactLtRealNegOfNat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instFactLtRealNegOfNat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instFactLtRealNegOfNat_differentialGeometry ``Submission.DifferentialGeometry.Topology.instFactLtRealNegOfNat_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell ``Submission.DifferentialGeometry.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatClosedCell
local instance _root_.Submission.DifferentialGeometry.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell ``Submission.DifferentialGeometry.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell

def sphereToClosedCell (z : S²) : ClosedCell 3 :=
  ⟨z.1, le_of_eq (by simpa only [Metric.mem_sphere, dist_zero_right] using z.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereToClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereToClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereToClosedCell ``Submission.DifferentialGeometry.Topology.sphereToClosedCell

structure SphericalTubeSystem (M : ClosedOrientedManifold.{u} 3) where
  Index : Type
  [finiteIndex : Fintype Index]
  tube : Index → C(Tube, M.Carrier)
  smooth : ∀ a, _root_.Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ (tube a)
  disjoint : Pairwise fun a b => Disjoint (_root_.Set.range (tube a)) (_root_.Set.range (tube b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem

attribute [instance] SphericalTubeSystem.finiteIndex

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def removedBand (a : T.Index) : Set M.Carrier :=
  T.tube a '' {z : Tube | (-1 : ℝ) < z.2.1 ∧ z.2.1 < 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.removedBand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.removedBand ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.removedBand

def core : Set M.Carrier := (⋃ a, T.removedBand a)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.core ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.core

def surgeryRegion : Set M.Carrier :=
  ⋃ a, T.tube a '' {z : Tube | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion

abbrev Boundary := T.Index × Bool

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.Boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.Boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.Boundary ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.Boundary

def boundaryLevel (side : Bool) : _root_.Set.Icc (-2 : ℝ) 2 :=
  if side then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryLevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundaryLevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundaryLevel ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundaryLevel

def boundarySphere (b : T.Boundary) : C(S², M.Carrier) :=
  (T.tube b.1).comp
    ⟨fun z => (z, boundaryLevel b.2), continuous_id.prodMk continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere

theorem boundarySphere_mem_core (b : T.Boundary) (z : S²) :
    T.boundarySphere b z ∈ T.core := by
  intro h
  obtain ⟨a, y, hy, heq⟩ := by
    simpa only [core, _root_.Set.mem_compl_iff, _root_.Set.mem_iUnion, removedBand, _root_.Set.mem_image] using h
  have ha : a = b.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne)
      (Set.mem_range_self y) ⟨(z, boundaryLevel b.2), heq.symm⟩
  subst a
  have hcoord := congrArg (fun q : Tube => (q.2 : ℝ))
    ((T.smooth b.1).isEmbedding.injective heq)
  rcases b with ⟨a, side⟩
  cases side <;> simp [boundaryLevel] at hcoord <;>
    rcases hy with ⟨hlo, hhi⟩ <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere_mem_core ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.boundarySphere_mem_core

def coreBoundarySphere (b : T.Boundary) : C(S², T.core) :=
  ⟨fun z => ⟨T.boundarySphere b z, T.boundarySphere_mem_core b z⟩,
    (T.boundarySphere b).continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBoundarySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBoundarySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBoundarySphere ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBoundarySphere

def outwardVector (b : T.Boundary) (z : S²) :
    TangentSpace (𝓡 3) (T.boundarySphere b z) :=
  mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (T.tube b.1)
    (z, boundaryLevel b.2)
    (0, (if b.2 then -1 else 1) • EuclideanSpace.single 0 (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.outwardVector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.outwardVector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.outwardVector ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.outwardVector

end SphericalTubeSystem

structure SphericalCapping (M N : ClosedOrientedManifold.{u} 3)
    (T : SphericalTubeSystem M) where
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) T.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ T.core]
  core_induced : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : T.core → M.Carrier)
  core_compact : IsCompact T.core
  core_boundary : (𝓡∂ 3).boundary T.core = ⋃ b, _root_.Set.range (T.coreBoundarySphere b)
  coreInclusion : C(T.core, N.Carrier)
  core_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ coreInclusion
  cap : T.Boundary → C(ClosedCell 3, N.Carrier)
  cap_embedding : ∀ b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (cap b)
  attaching : T.Boundary → (S² ≃ₘ⟮𝓡 2, 𝓡 2⟯ S²)
  boundary_eq : ∀ b z,
    cap b (sphereToClosedCell z) = coreInclusion (T.coreBoundarySphere b (attaching b z))
  exhaustive : _root_.Set.range coreInclusion ∪ (⋃ b, _root_.Set.range (cap b)) = _root_.Set.univ
  core_cap_intersection : ∀ b,
    _root_.Set.range coreInclusion ∩ _root_.Set.range (cap b) =
      _root_.Set.range (coreInclusion.comp (T.coreBoundarySphere b))
  cap_disjoint : Pairwise fun b b' => Disjoint (_root_.Set.range (cap b)) (_root_.Set.range (cap b'))
  core_positive : ∀ x : T.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : T.core → M.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : T.core → M.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x).toLinearMap hj))
        (M.orientation.orientation x.1) = N.orientation.orientation (coreInclusion x)
  cap_positive : ∀ b, ∀ x : ClosedCell 3, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (cap b x)
  boundary_orientation_reversing : ∀ b z (v w : TangentSpace (𝓡 2) z),
    let f : S² → M.Carrier := T.boundarySphere b ∘ attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S² → EuclideanSpace ℝ (Fin 3)) z
    (0 < ((M.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons (T.outwardVector b (attaching b z)) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (if b.2 then (1 : ℝ) else -1) *
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping ``Submission.DifferentialGeometry.Topology.SphericalCapping

structure SphericalCutCapTransition (M Q : ClosedOrientedManifold.{u} 3) where
  source_nonempty : Nonempty M.Carrier
  tubes : SphericalTubeSystem M
  capped : ClosedOrientedManifold.{u} 3
  capping : SphericalCapping M capped tubes
  discarded : ClosedOrientedManifold.{u} 3
  presentation : capped.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Q.Carrier ⊕ discarded.Carrier)
  presentation_positive : ∀ x : capped.Carrier,
    Orientation.map (Fin 3)
      (presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (capped.orientation.orientation x) =
        match presentation x with
        | Sum.inl q => Q.orientation.orientation q
        | Sum.inr d => discarded.orientation.orientation d
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : tubes.core, ∃ q : Q.Carrier,
      presentation (capping.coreInclusion x) = Sum.inl q ∧ ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : tubes.core,
      presentation (capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : ClosedCell 3, presentation (capping.cap b z) = Sum.inl q}
  nontrivial : Nonempty tubes.Index ∨ Nonempty discarded.Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def retainedCore : Set E.tubes.core :=
  {x | ∃ q : Q.Carrier, E.presentation (E.capping.coreInclusion x) = Sum.inl q}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore

def retainedOutput (x : E.retainedCore) : Q.Carrier := Classical.choose x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput

theorem retainedOutput_eq (x : E.retainedCore) :
    E.presentation (E.capping.coreInclusion x.1) = Sum.inl (E.retainedOutput x) :=
  Classical.choose_spec x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.retainedOutput_eq

theorem retainedCore_isEmpty_iff : IsEmpty E.retainedCore ↔ IsEmpty Q.Carrier := by
  constructor
  · intro h
    refine ⟨fun q => ?_⟩
    obtain ⟨x, r, hr, _⟩ := E.every_component_meets_core (ConnectedComponents.mk q)
    exact h.false ⟨x, r, hr⟩
  · intro h
    exact ⟨fun x => h.false (E.retainedOutput x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore_isEmpty_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore_isEmpty_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore_isEmpty_iff ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore_isEmpty_iff

def controlledBy
    (D : (P : ClosedOrientedManifold.{u} 3) → ConnectedComponents P.Carrier → Prop) : Prop :=
  ∀ c : ConnectedComponents E.discarded.Carrier, D E.discarded c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.controlledBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.controlledBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.controlledBy ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.controlledBy

end SphericalCutCapTransition

structure FiniteCutCapTrace where
  eventCount : ℕ
  eventCount_pos : 0 < eventCount
  stage : Fin (eventCount + 1) → ClosedOrientedManifold.{u} 3
  transition : (i : Fin eventCount) →
    SphericalCutCapTransition (stage i.castSucc) (stage i.succ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace

namespace FiniteCutCapTrace

def controlledBy (T : FiniteCutCapTrace.{u})
    (D : (M : ClosedOrientedManifold.{u} 3) → ConnectedComponents M.Carrier → Prop) : Prop :=
  ∀ i : Fin T.eventCount, (T.transition i).controlledBy D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.controlledBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.controlledBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.controlledBy ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.controlledBy

def extinct (T : FiniteCutCapTrace.{u}) : Prop :=
  IsEmpty (T.stage (Fin.last T.eventCount)).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.extinct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.extinct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.extinct ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.extinct

abbrev InitialIdentification (T : FiniteCutCapTrace.{u})
    (M : ClosedOrientedManifold.{u} 3) :=
  ClosedOrientedManifold.OrientedDiffeomorph M (T.stage 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.InitialIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.InitialIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.InitialIdentification ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.InitialIdentification

end FiniteCutCapTrace

end DifferentialGeometry.Topology
