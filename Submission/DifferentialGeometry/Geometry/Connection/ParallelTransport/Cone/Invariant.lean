import Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperConeFace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Analysis.InnerProductSpace

namespace DifferentialGeometry.Geometry.Connection

variable {X : Type*} (V : X → Type*)
  [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)]

structure LinearIsometricTransport where
  transport : ∀ x y, V x ≃ₗᵢ[ℝ] V y
  transport_refl : ∀ x, transport x x = LinearIsometryEquiv.refl ℝ (V x)
  transport_trans : ∀ x y z, (transport x y).trans (transport y z) = transport x z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport

def ProperConeFamily := ∀ x, ProperCone ℝ (V x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.ProperConeFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.ProperConeFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.ProperConeFamily ``Submission.DifferentialGeometry.Geometry.Connection.ProperConeFamily

def IsParallelProperConeFamily
    (P : LinearIsometricTransport V) (C : ProperConeFamily V) : Prop :=
  ∀ x y, (C x).map
    (P.transport x y).toContinuousLinearEquiv.toContinuousLinearMap = C y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily

namespace LinearIsometricTransport

def transportSectionTo
    (P : LinearIsometricTransport V) (y : X) (u : ∀ x, V x) : X → V y :=
  fun x ↦ P.transport x y (u x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo

@[simp]
theorem transportSectionTo_apply
    (P : LinearIsometricTransport V) (y : X) (u : ∀ x, V x) (x : X) :
    P.transportSectionTo V y u x = P.transport x y (u x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo_apply ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transportSectionTo_apply

def ofBasepoint (x₀ : X) (e : ∀ x, V x₀ ≃ₗᵢ[ℝ] V x) :
    LinearIsometricTransport V where
  transport x y := (e x).symm.trans (e y)
  transport_refl x := by
    apply LinearIsometryEquiv.ext
    intro v
    simp
  transport_trans x y z := by
    apply LinearIsometryEquiv.ext
    intro v
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint

@[simp]
theorem ofBasepoint_transport_apply
    (x₀ : X) (e : ∀ x, V x₀ ≃ₗᵢ[ℝ] V x) (x y : X) (v : V x) :
    (ofBasepoint V x₀ e).transport x y v = e y ((e x).symm v) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint_transport_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint_transport_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint_transport_apply ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.ofBasepoint_transport_apply

@[simp]
theorem transport_self (P : LinearIsometricTransport V) (x : X) :
    P.transport x x = LinearIsometryEquiv.refl ℝ (V x) :=
  P.transport_refl x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_self ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_self

@[simp]
theorem transport_trans_apply (P : LinearIsometricTransport V) (x y z : X) (v : V x) :
    P.transport y z (P.transport x y v) = P.transport x z v := by
  simpa using congrArg (fun e : V x ≃ₗᵢ[ℝ] V z ↦ e v) (P.transport_trans x y z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_trans_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_trans_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_trans_apply ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_trans_apply

@[simp]
theorem transport_symm (P : LinearIsometricTransport V) (x y : X) :
    (P.transport x y).symm = P.transport y x := by
  apply LinearIsometryEquiv.ext
  intro v
  calc
    (P.transport x y).symm v =
        (P.transport x y).symm (P.transport x y (P.transport y x v)) := by
      rw [P.transport_trans_apply V y x y]
      simp
    _ = P.transport y x v :=
      (P.transport x y).symm_apply_apply (P.transport y x v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_symm ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometricTransport.transport_symm

end LinearIsometricTransport

namespace ProperConeFamily

variable [∀ x, CompleteSpace (V x)]

noncomputable def innerDual (C : ProperConeFamily V) : ProperConeFamily V :=
  fun x ↦ ProperCone.innerDual (C x : Set (V x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.ProperConeFamily.innerDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.ProperConeFamily.innerDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.ProperConeFamily.innerDual ``Submission.DifferentialGeometry.Geometry.Connection.ProperConeFamily.innerDual

end ProperConeFamily

theorem IsParallelProperConeFamily.image_transport
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X) :
    P.transport x y '' (C x : Set (V x)) = (C y : Set (V y)) := by
  calc
    P.transport x y '' (C x : Set (V x)) =
        ((C x).map
          (P.transport x y).toContinuousLinearEquiv.toContinuousLinearMap : Set (V y)) :=
      (DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.coe_map_continuousLinearEquiv
        (C x) (P.transport x y).toContinuousLinearEquiv).symm
    _ = (C y : Set (V y)) := congrArg SetLike.coe (h x y)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.image_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.image_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.image_transport ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.image_transport

theorem IsParallelProperConeFamily.transport_mem_iff
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X) (v : V x) :
    P.transport x y v ∈ C y ↔ v ∈ C x := by
  rw [← h x y]
  rw [DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_iff

theorem IsParallelProperConeFamily.mapsTo_transport
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X) :
    MapsTo (P.transport x y) (C x) (C y) := by
  intro v hv
  exact (h.transport_mem_iff V x y v).2 hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.mapsTo_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.mapsTo_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.mapsTo_transport ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.mapsTo_transport

theorem IsParallelProperConeFamily.innerDual
    [∀ x, CompleteSpace (V x)]
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) :
    IsParallelProperConeFamily V P (C.innerDual V) := by
  intro x y
  change (ProperCone.innerDual (C x : Set (V x))).map
      (P.transport x y).toContinuousLinearEquiv.toContinuousLinearMap =
    ProperCone.innerDual (C y : Set (V y))
  rw [← DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDual_map_linearIsometryEquiv]
  rw [h x y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDual ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDual

theorem IsParallelProperConeFamily.innerDualZeroFace_map_transport
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X) (v : V x) :
    (ProperCone.innerDualZeroFace (C x) v).map
        (P.transport x y).toContinuousLinearEquiv.toContinuousLinearMap =
      ProperCone.innerDualZeroFace (C y) (P.transport x y v) := by
  rw [ProperCone.innerDualZeroFace_map_linearIsometryEquiv, h x y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDualZeroFace_map_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDualZeroFace_map_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDualZeroFace_map_transport ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.innerDualZeroFace_map_transport

theorem IsParallelProperConeFamily.transport_mem_innerDualZeroFace_iff
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X) (v w : V x) :
    P.transport x y w ∈
        ProperCone.innerDualZeroFace (C y) (P.transport x y v) ↔
      w ∈ ProperCone.innerDualZeroFace (C x) v := by
  rw [← h.innerDualZeroFace_map_transport V x y v]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_innerDualZeroFace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_innerDualZeroFace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_innerDualZeroFace_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_innerDualZeroFace_iff

theorem IsParallelProperConeFamily.dualZeroFace_map_transport
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X)
    (phi : StrongDual ℝ (V x)) :
    (ProperCone.dualZeroFace (C x) phi).map
        (P.transport x y).toContinuousLinearEquiv.toContinuousLinearMap =
      ProperCone.dualZeroFace (C y)
        (phi.comp
          (P.transport x y).toContinuousLinearEquiv.symm.toContinuousLinearMap) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv, h x y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.dualZeroFace_map_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.dualZeroFace_map_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.dualZeroFace_map_transport ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.dualZeroFace_map_transport

theorem IsParallelProperConeFamily.transport_mem_dualZeroFace_iff
    {P : LinearIsometricTransport V} {C : ProperConeFamily V}
    (h : IsParallelProperConeFamily V P C) (x y : X)
    (phi : StrongDual ℝ (V x)) (v : V x) :
    P.transport x y v ∈ ProperCone.dualZeroFace (C y)
        (phi.comp
          (P.transport x y).toContinuousLinearEquiv.symm.toContinuousLinearMap) ↔
      v ∈ ProperCone.dualZeroFace (C x) phi := by
  rw [← h.dualZeroFace_map_transport V x y phi]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_dualZeroFace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_dualZeroFace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_dualZeroFace_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelProperConeFamily.transport_mem_dualZeroFace_iff

end DifferentialGeometry.Geometry.Connection
