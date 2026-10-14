import Submission.DifferentialGeometry.Topology.Covering.Fiber.Equivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

theorem finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [SimplyConnectedSpace E]
    (p : E → X) (hp : IsCoveringMap p) (x : X) (e : p ⁻¹' {x})
    [Finite (p ⁻¹' {x})] : Finite (FundamentalGroup X x) :=
  Finite.of_equiv _
    (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hp x e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover ``Submission.DifferentialGeometry.Topology.finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover

theorem finite_fundamentalGroup_of_compact_simplyConnected_cover
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E] [SimplyConnectedSpace E]
    (p : E → X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x : X) :
    Finite (FundamentalGroup X x) := by
  let : Finite (p ⁻¹' {x}) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact
      hp x
  obtain ⟨e, he⟩ := hsurj x
  exact finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover p hp x ⟨e, he⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finite_fundamentalGroup_of_compact_simplyConnected_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finite_fundamentalGroup_of_compact_simplyConnected_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finite_fundamentalGroup_of_compact_simplyConnected_cover ``Submission.DifferentialGeometry.Topology.finite_fundamentalGroup_of_compact_simplyConnected_cover

end DifferentialGeometry.Topology
