import Submission.DifferentialGeometry.Topology.StandardModel
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import Submission.DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

private theorem finrank_euclideanSpace_three :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.finrank_euclideanSpace_three
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.finrank_euclideanSpace_three target :: scope.openDecls } }

private abbrev sumArrowProdContinuousLinearEquiv :
    ((Fin 2 → ℝ) × (Fin 1 → ℝ)) ≃L[ℝ] (Fin 2 ⊕ Fin 1 → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℝ ℝ).symm.toContinuousLinearEquiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sumArrowProdContinuousLinearEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sumArrowProdContinuousLinearEquiv target :: scope.openDecls } }

private abbrev arrowFinContinuousLinearEquiv :
    (Fin 2 ⊕ Fin 1 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.arrowFinContinuousLinearEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.arrowFinContinuousLinearEquiv target :: scope.openDecls } }

def sphereTwoTimesCircleModelEquiv :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).prodCongr (EuclideanSpace.equiv (Fin 1) ℝ)).trans
    (sumArrowProdContinuousLinearEquiv.trans
      (arrowFinContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 3) ℝ).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleModelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleModelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleModelEquiv ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleModelEquiv

abbrev sphereTwoTimesCircleModelCopy :
    DifferentialGeometry.Geometry.Topology.StandardModelCopy ((𝓡 2).prod (𝓡 1))
      SphereTwoTimesCircle (EuclideanSpace ℝ (Fin 3)) :=
  DifferentialGeometry.Geometry.Topology.standardModelCopy (I := (𝓡 2).prod (𝓡 1))
    (M := SphereTwoTimesCircle) sphereTwoTimesCircleModelEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy

private theorem sphereTwoTimesCircleModelCopy_compactSpace :
    CompactSpace sphereTwoTimesCircleModelCopy.Q :=
  isCompact_univ_iff.mp (by
    simpa using (sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.isCompact_image
      (s := Set.univ)).mpr isCompact_univ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy_compactSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy_compactSpace target :: scope.openDecls } }

theorem connectedSpace_sphereTwoTimesCircle : ConnectedSpace SphereTwoTimesCircle :=
  @instConnectedSpaceProd _ _ _ _
    (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num)))
    (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSpace_sphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSpace_sphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSpace_sphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.connectedSpace_sphereTwoTimesCircle

private theorem sphereTwoTimesCircleModelCopy_connectedSpace :
    ConnectedSpace sphereTwoTimesCircleModelCopy.Q :=
  (sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.connectedSpace_iff).mp
    connectedSpace_sphereTwoTimesCircle

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy_connectedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereTwoTimesCircleModelCopy_connectedSpace target :: scope.openDecls } }

noncomputable def sphereTwoTimesCircleSmoothOrientation :
    Manifold.SmoothOrientation ((𝓡 2).prod (𝓡 1)) SphereTwoTimesCircle :=
  Manifold.smoothOrientationOfManifoldOrientation ((𝓡 2).prod (𝓡 1))
    (OrientationAssembly.reindexManifoldOrientation ((𝓡 2).prod (𝓡 1))
      (finCongr sphereTwoTimesCircleOrientation.dimension_eq.symm)
      sphereTwoTimesCircleOrientation)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleSmoothOrientation ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleSmoothOrientation

noncomputable def sphereTwoTimesCircleLiftSmoothOrientation :
    Manifold.SmoothOrientation (𝓡 3) sphereTwoTimesCircleModelCopy.Q :=
  Manifold.pullbackSmoothOrientation (𝓡 3) ((𝓡 2).prod (𝓡 1))
    sphereTwoTimesCircleModelCopy.equiv.symm
    sphereTwoTimesCircleModelCopy.equiv.symm.contMDiff
    (fun x => (sphereTwoTimesCircleModelCopy.equiv.symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective)
    sphereTwoTimesCircleSmoothOrientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLiftSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftSmoothOrientation ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLiftSmoothOrientation

noncomputable def sphereTwoTimesCircleLiftOrientation :
    ManifoldOrientation (𝓡 3) sphereTwoTimesCircleModelCopy.Q 3 :=
  OrientationAssembly.reindexManifoldOrientation (𝓡 3)
    (finCongr finrank_euclideanSpace_three)
    (Classical.choose
      (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
        (𝓡 3) sphereTwoTimesCircleLiftSmoothOrientation))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation

noncomputable def sphereTwoTimesCircleLift : ConnectedClosedOrientedManifold.{0} 3 where
  Carrier := sphereTwoTimesCircleModelCopy.Q
  topology := sphereTwoTimesCircleModelCopy.topos
  charts := sphereTwoTimesCircleModelCopy.charted
  smooth := sphereTwoTimesCircleModelCopy.mfld
  hausdorff := sphereTwoTimesCircleModelCopy.t2
  compact := sphereTwoTimesCircleModelCopy_compactSpace
  orientation := sphereTwoTimesCircleLiftOrientation
  connected := sphereTwoTimesCircleModelCopy_connectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLift

@[simp]
theorem sphereTwoTimesCircleLift_carrier :
    sphereTwoTimesCircleLift.Carrier = ULift SphereTwoTimesCircle := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLift_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_carrier ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLift_carrier

theorem sphereTwoTimesCircleLiftOrientation_orientation
    (x : sphereTwoTimesCircleModelCopy.Q) :
    sphereTwoTimesCircleLiftOrientation.orientation x =
      Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
        (finCongr sphereTwoTimesCircleLiftOrientation.dimension_eq)
        (sphereTwoTimesCircleLiftSmoothOrientation.val x) := by
  simp only [sphereTwoTimesCircleLiftOrientation, OrientationAssembly.reindexManifoldOrientation]
  rw [Classical.choose_spec
    (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) sphereTwoTimesCircleLiftSmoothOrientation)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation_orientation ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLiftOrientation_orientation

theorem sphereTwoTimesCircleLift_preservesOrientation :
    sphereTwoTimesCircleModelCopy.equiv.symm.preservesOrientation
      sphereTwoTimesCircleLiftOrientation sphereTwoTimesCircleOrientation := by
  refine Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    (f := sphereTwoTimesCircleModelCopy.equiv.symm)
    sphereTwoTimesCircleModelCopy.equiv.symm.contMDiff
    (fun x => (sphereTwoTimesCircleModelCopy.equiv.symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective)
    sphereTwoTimesCircleSmoothOrientation
    sphereTwoTimesCircleLiftOrientation sphereTwoTimesCircleOrientation ?_ ?_
  · intro y
    rfl
  · intro x
    rw [sphereTwoTimesCircleLiftOrientation_orientation x]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereTwoTimesCircleLift_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereTwoTimesCircleLift_preservesOrientation ``Submission.DifferentialGeometry.Topology.sphereTwoTimesCircleLift_preservesOrientation

theorem isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift :
    isSphereTwoTimesCircleFactor sphereTwoTimesCircleLift :=
  ⟨sphereTwoTimesCircleModelCopy.equiv.symm, sphereTwoTimesCircleLift_preservesOrientation⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

end DifferentialGeometry.Topology
