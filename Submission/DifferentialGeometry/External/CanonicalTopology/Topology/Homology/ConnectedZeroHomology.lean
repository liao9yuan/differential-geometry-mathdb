import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ZeroHomologyMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual H0 maps between path-connected spaces are isomorphisms -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y]

/-- The SAME original H0 map is an isomorphism for any continuous map
between actual path-connected spaces. Its inverse is induced by a constant
map, and the inverse identities are proved from actual paths on vertices. -/
def integralSingularHomologyZeroMapEquiv (f : C(X, Y)) :
    integralSingularHomology 0 X ≃ₗ[ℤ] integralSingularHomology 0 Y where
  toLinearMap := integralSingularHomologyMap 0 f
  invFun := integralSingularHomologyMap 0 (ContinuousMap.const Y (Classical.arbitrary X))
  left_inv a := by
    let g := ContinuousMap.const Y (Classical.arbitrary X)
    have he := (integralSingularHomologyMap_comp 0 f g).symm.trans
      ((integralSingularHomologyMap_zero_eq_of_joined (g.comp f) (ContinuousMap.id X)
        (fun x => ⟨PathConnectedSpace.somePath _ _⟩)).trans (integralSingularHomologyMap_id 0))
    exact LinearMap.congr_fun he a
  right_inv a := by
    let g := ContinuousMap.const Y (Classical.arbitrary X)
    have he := (integralSingularHomologyMap_comp 0 g f).symm.trans
      ((integralSingularHomologyMap_zero_eq_of_joined (f.comp g) (ContinuousMap.id Y)
        (fun y => ⟨PathConnectedSpace.somePath _ _⟩)).trans (integralSingularHomologyMap_id 0))
    exact LinearMap.congr_fun he a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyZeroMapEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyZeroMapEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyZeroMapEquiv ``Submission.DifferentialGeometry.Topology.integralSingularHomologyZeroMapEquiv

/-- This proves invertibility of the ORIGINAL categorical homology map
of the SAME original chain map. -/
theorem integralSingularHomologyZeroMap_isIso (f : C(X, Y)) :
    IsIso (HomologicalComplex.homologyMap (integralSingularChainMap f) 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (integralSingularHomologyZeroMapEquiv f).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyZeroMap_isIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyZeroMap_isIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyZeroMap_isIso ``Submission.DifferentialGeometry.Topology.integralSingularHomologyZeroMap_isIso

end DifferentialGeometry.Topology
