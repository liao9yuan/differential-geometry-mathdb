import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Original zero-chain representatives and their actual homology classes -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Retain the ORIGINAL kernel's integer action on actual zero-cycles. -/
instance integralZeroCyclesModule : Module ℤ (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) :=
  (LinearMap.ker ((integralSingularChains X).sc 0).g.hom).module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroCyclesModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroCyclesModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroCyclesModule ``Submission.DifferentialGeometry.Topology.integralZeroCyclesModule

/-- Every original zero-chain is a cycle for the actual degree-zero differential. -/
def integralZeroCycleInclusion : (integralSingularChains X).X 0 →ₗ[ℤ]
    LinearMap.ker ((integralSingularChains X).sc 0).g.hom :=
  (LinearMap.id : (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 0).codRestrict
    (LinearMap.ker ((integralSingularChains X).sc 0).g.hom) (fun c => by
    change (integralSingularChains X).d 0 ((ComplexShape.down ℕ).next 0) c = 0
    rw [ChainComplex.next_nat_zero, (integralSingularChains X).shape 0 0 (by simp)]
    rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroCycleInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroCycleInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroCycleInclusion ``Submission.DifferentialGeometry.Topology.integralZeroCycleInclusion

/-- The original homology class of an actual zero-chain. -/
def integralZeroChainClass : (integralSingularChains X).X 0 →ₗ[ℤ] integralSingularHomology 0 X :=
  (moduleHomologyClass ((integralSingularChains X).sc 0)).comp integralZeroCycleInclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroChainClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroChainClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroChainClass ``Submission.DifferentialGeometry.Topology.integralZeroChainClass

/-- Every element of ORIGINAL H0 is represented by an original zero-chain. -/
theorem integralZeroChainClass_surjective : Function.Surjective (integralZeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, hc⟩ := moduleHomologyClass_surjective ((integralSingularChains X).sc 0) a
  exact ⟨c.val, hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroChainClass_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroChainClass_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroChainClass_surjective ``Submission.DifferentialGeometry.Topology.integralZeroChainClass_surjective

/-- A zero-chain class vanishes exactly when the SAME chain is an actual boundary. -/
theorem integralZeroChainClass_eq_zero_iff (c : (integralSingularChains X).X 0) :
    integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c := by
  have h := moduleHomologyClass_eq_zero_iff ((integralSingularChains X).sc 0) (integralZeroCycleInclusion c)
  change (integralZeroChainClass c = 0 ↔ ∃ b : (integralSingularChains X).X ((ComplexShape.down ℕ).prev 0),
    (integralSingularChains X).d ((ComplexShape.down ℕ).prev 0) 0 b = c) at h
  exact h.trans (congrArg (fun i => ∃ b : (integralSingularChains X).X i,
    (integralSingularChains X).d i 0 b = c) (ChainComplex.prev ℕ 0)).to_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroChainClass_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroChainClass_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroChainClass_eq_zero_iff ``Submission.DifferentialGeometry.Topology.integralZeroChainClass_eq_zero_iff

/-- Equality of actual zero-chain classes is equality modulo SAME original boundaries. -/
theorem integralZeroChainClass_eq_iff (c d : (integralSingularChains X).X 0) :
    integralZeroChainClass c = integralZeroChainClass d ↔ ∃ b : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 b = c - d := by
  rw [← sub_eq_zero, ← map_sub, integralZeroChainClass_eq_zero_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroChainClass_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroChainClass_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroChainClass_eq_iff ``Submission.DifferentialGeometry.Topology.integralZeroChainClass_eq_iff

/-- The ORIGINAL induced H0 map sends a zero-chain class to the class
of the SAME original image chain. -/
theorem integralZeroChainClass_map (f : C(X, Y)) (c : (integralSingularChains X).X 0) :
    integralSingularHomologyMap 0 f (integralZeroChainClass c) =
      integralZeroChainClass ((integralSingularChainMap f).f 0 c) :=
  moduleHomologyClass_map
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0).map
      (integralSingularChainMap f)) (integralZeroCycleInclusion c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroChainClass_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroChainClass_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroChainClass_map ``Submission.DifferentialGeometry.Topology.integralZeroChainClass_map

end DifferentialGeometry.Topology
