import Submission.DifferentialGeometry.Topology.Covering.Fiber.Equivalence
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Data.Set.Card

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology.Covering

theorem exists_encard_fiber_eq_natCast_of_compact
    {E X : Type*} [TopologicalSpace E] [CompactSpace E]
    [TopologicalSpace X] [T1Space X] [PathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) :
    ∃ k : ℕ, ∀ y : X, {x : E | p x = y}.encard = (k : ℕ∞) := by
  classical
  let y₀ : X := Classical.choice inferInstance
  refine ⟨(p ⁻¹' {y₀}).ncard, ?_⟩
  intro y
  let := Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact hp y
  have hcard : (p ⁻¹' {y}).ncard = (p ⁻¹' {y₀}).ncard :=
    Nat.card_congr (Equiv.ofBijective
      (hp.monodromy (.mk (PathConnectedSpace.somePath y y₀)))
      (hp.monodromy_bijective _))
  change (p ⁻¹' {y}).encard = _
  rw [← Set.coe_ncard_eq_encard, hcard]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.exists_encard_fiber_eq_natCast_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.exists_encard_fiber_eq_natCast_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.exists_encard_fiber_eq_natCast_of_compact ``Submission.DifferentialGeometry.Topology.Covering.exists_encard_fiber_eq_natCast_of_compact

end DifferentialGeometry.Topology.Covering
