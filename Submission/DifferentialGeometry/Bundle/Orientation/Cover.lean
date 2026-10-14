import Submission.DifferentialGeometry.Bundle.Orientation.Transport
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Covering.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section
open _root_.Set _root_.Bundle
open scoped _root_.Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {B F J : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

attribute [local instance] orientationTopology
local instance _root_.Submission.DifferentialGeometry.VectorBundle.instDiscreteTopologyOrientationRealFin_differentialGeometry_1 : DiscreteTopology (Orientation ℝ F (Fin n)) := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.instDiscreteTopologyOrientationRealFin_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.instDiscreteTopologyOrientationRealFin_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.instDiscreteTopologyOrientationRealFin_differentialGeometry_1 ``Submission.DifferentialGeometry.VectorBundle.instDiscreteTopologyOrientationRealFin_differentialGeometry_1

omit [FiniteDimensional ℝ F] in
theorem map_orientation_trans (A B : F ≃ₗ[ℝ] F) (o : Orientation ℝ F (Fin n)) :
    Orientation.map (Fin n) B (Orientation.map (Fin n) A o) =
      Orientation.map (Fin n) (A.trans B) o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.map_orientation_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.map_orientation_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.map_orientation_trans ``Submission.DifferentialGeometry.VectorBundle.map_orientation_trans

def orientationChange (Z : VectorBundleCore ℝ B F J) (i j : J) (x : B) :
    Orientation ℝ F (Fin n) ≃ Orientation ℝ F (Fin n) :=
  Orientation.map (Fin n) ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.orientationChange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.orientationChange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.orientationChange ``Submission.DifferentialGeometry.VectorBundle.orientationChange


def orientationCore (Z : VectorBundleCore ℝ B F J) (hdim : Module.finrank ℝ F = n) :
    FiberBundleCore J B (Orientation ℝ F (Fin n)) where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := orientationChange Z i j x
  coordChange_self i x hx o := by
    have hid : ((Z.localTriv i).coordChangeL ℝ (Z.localTriv i) x).toLinearEquiv =
        LinearEquiv.refl ℝ F := by
      ext v
      change (Z.localTriv i).coordChangeL ℝ (Z.localTriv i) x v = v
      rw [Z.localTriv_coordChange_eq i i ⟨hx, hx⟩, Z.coordChange_self i x hx]
    simp [orientationChange, hid]
  coordChange_comp i j k x hx o := by
    have hcomp :
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).toLinearEquiv.trans
          ((Z.localTriv j).coordChangeL ℝ (Z.localTriv k) x).toLinearEquiv =
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv k) x).toLinearEquiv := by
      ext v
      change (Z.localTriv j).coordChangeL ℝ (Z.localTriv k) x
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x v) =
        (Z.localTriv i).coordChangeL ℝ (Z.localTriv k) x v
      rw [Z.localTriv_coordChange_eq i j ⟨hx.1.1, hx.1.2⟩,
        Z.localTriv_coordChange_eq j k ⟨hx.1.2, hx.2⟩,
        Z.localTriv_coordChange_eq i k ⟨hx.1.1, hx.2⟩]
      exact Z.coordChange_comp i j k x hx v
    change Orientation.map (Fin n) _ (Orientation.map (Fin n) _ o) = _
    rw [map_orientation_trans, hcomp]
    rfl
  continuousOn_coordChange i j := by
    apply continuousOn_orientation_transport hdim
    apply (Z.continuousOn_coordChange i j).congr
    intro x hx
    exact ContinuousLinearMap.ext (fun v => Z.localTriv_coordChange_eq i j hx v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.orientationCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.orientationCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.orientationCore ``Submission.DifferentialGeometry.VectorBundle.orientationCore


theorem orientationCore_isCoveringMap (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) : IsCoveringMap (orientationCore Z hdim).proj :=
  FiberBundle.isCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.orientationCore_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.orientationCore_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.orientationCore_isCoveringMap ``Submission.DifferentialGeometry.VectorBundle.orientationCore_isCoveringMap


theorem orientationChange_locallyConstant (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (i j : J) (o : Orientation ℝ F (Fin n)) :
    IsLocallyConstant (fun x : ↥(Z.baseSet i ∩ Z.baseSet j) => orientationChange Z i j x o) := by
  have hAon : ContinuousOn (fun x =>
      ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x : F →L[ℝ] F))
      (Z.baseSet i ∩ Z.baseSet j) := by
    apply (Z.continuousOn_coordChange i j).congr
    intro x hx
    exact ContinuousLinearMap.ext (fun v => Z.localTriv_coordChange_eq i j hx v)
  apply (IsLocallyConstant.iff_continuous _).mpr
  have hA := continuousOn_iff_continuous_domRestrict.mp hAon
  convert (continuous_orientation_transport hdim
    (fun x : ↥(Z.baseSet i ∩ Z.baseSet j) => (Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x)
    hA).comp (continuous_id.prodMk (continuous_const (y := o))) using 1
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.orientationChange_locallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.orientationChange_locallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.orientationChange_locallyConstant ``Submission.DifferentialGeometry.VectorBundle.orientationChange_locallyConstant

theorem orientationChange_isLocallyConstant (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (i j : J) (o : Orientation ℝ F (Fin n)) :
    IsLocallyConstant (fun x : ↥(Z.baseSet i ∩ Z.baseSet j) => orientationChange Z i j x o) :=
  orientationChange_locallyConstant Z hdim i j o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.orientationChange_isLocallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.orientationChange_isLocallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.orientationChange_isLocallyConstant ``Submission.DifferentialGeometry.VectorBundle.orientationChange_isLocallyConstant

end DifferentialGeometry.VectorBundle
