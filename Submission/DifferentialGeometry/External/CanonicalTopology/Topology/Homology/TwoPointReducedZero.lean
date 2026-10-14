import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ReducedZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The normalized actual reduced H0 of a two-point space -/

noncomputable section

open _root_.ContinuousMap _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X]

/-- Actual H0 coordinates indexed by a specified equivalence with two points. -/
def integralZeroTwoCoordinates (e : X ≃ Bool) :
    integralSingularHomology 0 X ≃ₗ[ℤ] (Bool → ℤ) :=
  integralTotallyDisconnectedZeroEquiv.trans
    ((Finsupp.domLCongr e).trans (Finsupp.linearEquivFunOnFinite ℤ ℤ Bool))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroTwoCoordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroTwoCoordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroTwoCoordinates ``Submission.DifferentialGeometry.Topology.integralZeroTwoCoordinates

/-- The actual original vertex supplies one in its own coordinate. -/
theorem integralZeroTwoCoordinates_vertex (e : X ≃ Bool) (x : X) (b : Bool) :
    integralZeroTwoCoordinates e (integralZeroChainClass (integralVertexChain x)) b =
      if e x = b then 1 else 0 := by
  change (Finsupp.domLCongr (R := ℤ) (M := ℤ) e
    (integralTotallyDisconnectedZeroEquiv (integralZeroChainClass (integralVertexChain x)))) b = _
  rw [integralTotallyDisconnectedZeroEquiv_vertex, Finsupp.domLCongr_single]
  exact Finsupp.single_apply

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroTwoCoordinates_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroTwoCoordinates_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroTwoCoordinates_vertex ``Submission.DifferentialGeometry.Topology.integralZeroTwoCoordinates_vertex

/-- The actual normalized augmentation is the sum of those two coordinates. -/
theorem integralZeroAugmentation_twoCoordinates (e : X ≃ Bool)
    (a : integralSingularHomology 0 X) :
    integralZeroAugmentation a = integralZeroTwoCoordinates e a _root_.Bool.false +
      integralZeroTwoCoordinates e a true := by
  let s : (Bool → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj _root_.Bool.false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj _root_.Bool.true : (Bool → ℤ) →ₗ[ℤ] ℤ)
  have h : integralZeroAugmentation.comp integralZeroChainClass =
      (s.comp (integralZeroTwoCoordinates e).toLinearMap).comp integralZeroChainClass := by
    apply (integralSingularChainBasis 0 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
    rw [integralSimplexChain_zero_vertex, integralZeroAugmentation_vertex]
    change 1 = integralZeroTwoCoordinates e
      (integralZeroChainClass (integralVertexChain (TopCat.toSSetObj₀Equiv σ))) _root_.Bool.false +
        integralZeroTwoCoordinates e
          (integralZeroChainClass (integralVertexChain (TopCat.toSSetObj₀Equiv σ))) _root_.Bool.true
    rw [integralZeroTwoCoordinates_vertex, integralZeroTwoCoordinates_vertex]
    cases e (TopCat.toSSetObj₀Equiv σ) <;> norm_num
  obtain ⟨c, rfl⟩ := integralZeroChainClass_surjective a
  exact LinearMap.congr_fun h c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroAugmentation_twoCoordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroAugmentation_twoCoordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroAugmentation_twoCoordinates ``Submission.DifferentialGeometry.Topology.integralZeroAugmentation_twoCoordinates

/-- The kernel of the sum map is parametrized by (-z,z). -/
def twoCoordinateSumKernelEquiv :
    LinearMap.ker ((LinearMap.proj _root_.Bool.false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj _root_.Bool.true : (Bool → ℤ) →ₗ[ℤ] ℤ) : (Bool → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] ℤ where
  toFun a := a.val _root_.Bool.true
  invFun z := ⟨fun b => if b then z else -z, by change -z + z = 0; exact neg_add_cancel z⟩
  left_inv a := by
    apply Subtype.ext
    funext b
    have h : a.val _root_.Bool.false + a.val _root_.Bool.true = 0 := a.property
    cases b
    · change -a.val _root_.Bool.true = a.val _root_.Bool.false
      omega
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.twoCoordinateSumKernelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.twoCoordinateSumKernelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.twoCoordinateSumKernelEquiv ``Submission.DifferentialGeometry.Topology.twoCoordinateSumKernelEquiv

/-- Original reduced H0 of the actual two-point space is Z; no generator
or augmentation equation is assumed. -/
def integralTwoPointReducedZeroEquiv (e : X ≃ Bool) :
    integralReducedHomologyZero X ≃ₗ[ℤ] ℤ := by
  let s : (Bool → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj _root_.Bool.false : (Bool → ℤ) →ₗ[ℤ] ℤ) + (LinearMap.proj _root_.Bool.true : (Bool → ℤ) →ₗ[ℤ] ℤ)
  have h : integralReducedHomologyZero X =
      (LinearMap.ker s).comap (integralZeroTwoCoordinates e).toLinearMap := by
    ext a
    change integralZeroAugmentation a = 0 ↔
      integralZeroTwoCoordinates e a _root_.Bool.false + integralZeroTwoCoordinates e a _root_.Bool.true = 0
    rw [integralZeroAugmentation_twoCoordinates e]
  exact ((LinearEquiv.ofEq _ _ h).trans
    ((integralZeroTwoCoordinates e).ofSubmodule' (LinearMap.ker s))).trans
      twoCoordinateSumKernelEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralTwoPointReducedZeroEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralTwoPointReducedZeroEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralTwoPointReducedZeroEquiv ``Submission.DifferentialGeometry.Topology.integralTwoPointReducedZeroEquiv

end DifferentialGeometry.Topology
