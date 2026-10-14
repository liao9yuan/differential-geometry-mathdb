import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathCones
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cochains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual degree-one cohomology contraction -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The same path cone gives an actual primitive for every original
integral 1-cocycle. -/
theorem integralSingularCocycle_one_primitive (a : X) (φ : integralSingularCochain 1 X)
    (hφ : integralSingularCoboundary X 1 2 φ = 0) :
    integralSingularCoboundary X 0 1 (φ.comp (integralSingularConeZero a)) = φ := by
  apply LinearMap.ext
  intro c
  have h := LinearMap.congr_fun (integralSingularConeOne_equation a) c
  change (integralSingularChains X).d 2 1 (integralSingularConeOne a c) =
    c - integralSingularConeZero a ((integralSingularChains X).d 1 0 c) at h
  have hz := LinearMap.congr_fun hφ (integralSingularConeOne a c)
  change φ ((integralSingularChains X).d 2 1 (integralSingularConeOne a c)) = 0 at hz
  rw [h, map_sub, sub_eq_zero] at hz
  exact hz.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycle_one_primitive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycle_one_primitive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycle_one_primitive ``Submission.DifferentialGeometry.Topology.integralSingularCocycle_one_primitive

/-- First integral singular cohomology vanishes on every simply connected
space. This supplies the exact H¹-vanishing needed in the source's duality
step directly at the cochain level. -/
theorem integralSingularCohomology_one_subsingleton :
    Subsingleton (integralSingularCohomology 1 X) := by
  apply (integralSingularCohomology_one_vanishing_iff X).mpr
  intro φ hφ
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨φ.comp (integralSingularConeZero a), integralSingularCocycle_one_primitive a φ hφ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology_one_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology_one_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology_one_subsingleton ``Submission.DifferentialGeometry.Topology.integralSingularCohomology_one_subsingleton

end DifferentialGeometry.Topology
