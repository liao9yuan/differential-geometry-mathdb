import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {T : TubeSystem M} (K : Capping T N)
  (A : T.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : T.Boundary → Sphere 2 ≃ₜ Sphere 2)
  (hboundary : ∀ b y, A b (sphereToThreeBall y) = sphereToThreeBall (a b y))

def reparametrizeCaps : Capping T N where
  coreInclusion := K.coreInclusion
  coreEmbedding := K.coreEmbedding
  cap b := (K.cap b).comp ⟨A b, (A b).continuous⟩
  capEmbedding b := (K.capEmbedding b).comp (A b).isEmbedding
  attaching b := (a b).trans (K.attaching b)
  boundary_eq b y := by
    change K.cap b (A b (sphereToThreeBall y)) =
      K.coreInclusion (T.coreBoundarySphere b (K.attaching b (a b y)))
    rw [hboundary]
    exact K.boundary_eq b (a b y)
  exhaustive := by
    change _root_.Set.range K.coreInclusion ∪ (⋃ b, _root_.Set.range (K.cap b ∘ A b)) = _root_.Set.univ
    simp only [Surjective.range_comp (A _).surjective]
    exact K.exhaustive
  core_cap_intersection b := by
    change _root_.Set.range K.coreInclusion ∩ _root_.Set.range (K.cap b ∘ A b) =
      _root_.Set.range (K.coreInclusion.comp (T.coreBoundarySphere b))
    rw [(A b).surjective.range_comp]
    exact K.core_cap_intersection b
  cap_disjoint := by
    intro b c hbc
    change Disjoint (_root_.Set.range (K.cap b ∘ A b)) (_root_.Set.range (K.cap c ∘ A c))
    rw [(A b).surjective.range_comp, (A c).surjective.range_comp]
    exact K.cap_disjoint hbc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps

theorem reparametrizeCaps_coreInclusion :
    (K.reparametrizeCaps A a hboundary).coreInclusion = K.coreInclusion := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_coreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_coreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_coreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_coreInclusion

theorem reparametrizeCaps_cap (b : T.Boundary) (x : ThreeBall) :
    (K.reparametrizeCaps A a hboundary).cap b x = K.cap b (A b x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_cap

theorem reparametrizeCaps_attaching (b : T.Boundary) (y : Sphere 2) :
    (K.reparametrizeCaps A a hboundary).attaching b y = K.attaching b (a b y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_attaching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_attaching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_attaching ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.reparametrizeCaps_attaching

theorem range_cap_reparametrizeCaps (b : T.Boundary) :
    range ((K.reparametrizeCaps A a hboundary).cap b) = _root_.Set.range (K.cap b) :=
  (A b).surjective.range_comp (K.cap b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_cap_reparametrizeCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_cap_reparametrizeCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_cap_reparametrizeCaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping.range_cap_reparametrizeCaps

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)
  (A : E.tubes.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : E.tubes.Boundary → Sphere 2 ≃ₜ Sphere 2)
  (hboundary : ∀ b y, A b (sphereToThreeBall y) = sphereToThreeBall (a b y))

def reparametrizeCaps : CutCapTopology M Q D N where
  tubes := E.tubes
  capping := E.capping.reparametrizeCaps A a hboundary
  presentation := E.presentation
  nontrivial := E.nontrivial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps

theorem reparametrizeCaps_retainedCore :
    (E.reparametrizeCaps A a hboundary).retainedCore = E.retainedCore := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_retainedCore

theorem reparametrizeCaps_tubes : (E.reparametrizeCaps A a hboundary).tubes = E.tubes := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_tubes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_tubes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_tubes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_tubes

theorem reparametrizeCaps_presentation :
    (E.reparametrizeCaps A a hboundary).presentation = E.presentation := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_presentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.reparametrizeCaps_presentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology
