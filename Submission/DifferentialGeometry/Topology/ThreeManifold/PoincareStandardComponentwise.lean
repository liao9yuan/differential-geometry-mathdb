import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.toClosedOrientedManifold)
    (h : isStandardFactor M) : isStandardFactor N := by
  rcases h with ⟨G, ⟨e⟩⟩ | ⟨φ, hφ⟩
  · exact Or.inl ⟨G, ⟨f.symm.trans e⟩⟩
  · exact Or.inr ⟨f.symm.1.trans φ,
      Diffeomorph.preservesOrientation_trans f.symm.2 hφ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.isStandardFactor_of_orientedDiffeomorph

theorem isStandardFactor_iff_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.toClosedOrientedManifold) :
    isStandardFactor M ↔ isStandardFactor N :=
  ⟨isStandardFactor_of_orientedDiffeomorph f,
    isStandardFactor_of_orientedDiffeomorph f.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_iff_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_iff_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_iff_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.isStandardFactor_iff_of_orientedDiffeomorph

namespace ClosedOrientedManifold

variable (D : ClosedOrientedManifold.{u} 3)

noncomputable def componentInclusionDiffeomorph [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    ↥(D.componentOpen C) ≃ₘ⟮𝓡 3, 𝓡 3⟯ D.Carrier where
  toFun := Subtype.val
  invFun := fun x => ⟨x, by rw [componentOpen_eq_top_of_preconnectedSpace D C]; trivial⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    intro x
    exact codRestr_contMDiffAt (V := D.componentOpen C) (f := id)
      (fun _ => by rw [componentOpen_eq_top_of_preconnectedSpace D C]; trivial) contMDiffAt_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph

theorem componentInclusionDiffeomorph_preservesOrientation [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    (D.componentInclusionDiffeomorph C).preservesOrientation
      (D.component C).toClosedOrientedManifold.orientation D.orientation := by
  intro x
  have htangent : ((D.componentInclusionDiffeomorph C).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv = D.componentInclusionTangentEquiv C x := by
    ext v
    rfl
  rw [htangent]
  exact D.componentInclusion_preservesOrientation C x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentInclusionDiffeomorph_preservesOrientation

noncomputable def componentOrientedDiffeomorph [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    ClosedOrientedManifold.OrientedDiffeomorph (D.component C).toClosedOrientedManifold D :=
  ⟨D.componentInclusionDiffeomorph C, D.componentInclusionDiffeomorph_preservesOrientation C⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientedDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentOrientedDiffeomorph

theorem componentwiseStandardFactor_iff :
    D.componentwiseStandardFactor ↔ ∀ C : ConnectedComponents D.Carrier,
      isStandardFactor (D.component C) := by
  constructor
  · intro h C
    obtain ⟨N, hN, ⟨e⟩⟩ := h C
    exact isStandardFactor_of_orientedDiffeomorph e.symm hN
  · intro h C
    exact ⟨D.component C, h C, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactor_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactor_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactor_iff ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactor_iff

theorem componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard :
    D.componentwiseConnectedSumStandardFactor ↔
      ∀ C : ConnectedComponents D.Carrier,
        isOrientedPoincareStandard (D.component C).toClosedOrientedManifold := by
  constructor
  · intro h C
    obtain ⟨L, hL, ⟨e⟩⟩ := h C
    exact ⟨⟨L, hL, e⟩⟩
  · intro h C
    obtain ⟨p⟩ := h C
    exact ⟨p.factors, p.standard, ⟨p.diffeomorph⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard

theorem componentwiseConnectedSumStandardFactor_of_orientationRefinement
    (h : poincareStandardOrientationRefinement.{u})
    (hD : ∀ C : ConnectedComponents D.Carrier,
      isPoincareStandard (D.component C).Carrier) :
    D.componentwiseConnectedSumStandardFactor :=
  (D.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard).mpr fun C =>
    h (D.component C) (hD C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_of_orientationRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_of_orientationRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_of_orientationRefinement ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseConnectedSumStandardFactor_of_orientationRefinement

end ClosedOrientedManifold

namespace ConnectedClosedOrientedManifold

theorem componentwiseStandardFactor_of_isStandardFactor
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : isStandardFactor M) :
    M.toClosedOrientedManifold.componentwiseStandardFactor := fun C =>
  ⟨M, h, ⟨M.toClosedOrientedManifold.componentOrientedDiffeomorph C⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.componentwiseStandardFactor_of_isStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.componentwiseStandardFactor_of_isStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.componentwiseStandardFactor_of_isStandardFactor ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.componentwiseStandardFactor_of_isStandardFactor

end ConnectedClosedOrientedManifold

theorem sphereTwoTimesCircleLift_componentwiseStandardFactor :
    sphereTwoTimesCircleLift.toClosedOrientedManifold.componentwiseStandardFactor :=
  sphereTwoTimesCircleLift.componentwiseStandardFactor_of_isStandardFactor
    isStandardFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_componentwiseStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLift_componentwiseStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_componentwiseStandardFactor ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLift_componentwiseStandardFactor

theorem exists_componentwiseStandardFactor_nonemptyComponent :
    ∃ D : ClosedOrientedManifold.{u} 3, D.componentwiseStandardFactor ∧
      Nonempty (ConnectedComponents D.Carrier) :=
  ⟨standardThreeSphereLift.{u}.toClosedOrientedManifold,
    standardThreeSphereLift.componentwiseStandardFactor_of_isStandardFactor
      isStandardFactor_standardThreeSphereLift,
    ⟨ConnectedComponents.mk (standardThreeSphereLiftDiffeomorph.{u}
      ⟨EuclideanSpace.single 0 1, by simp⟩)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_componentwiseStandardFactor_nonemptyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_componentwiseStandardFactor_nonemptyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_componentwiseStandardFactor_nonemptyComponent ``Submission.DifferentialGeometry.Topology.exists_componentwiseStandardFactor_nonemptyComponent

end DifferentialGeometry.Topology
