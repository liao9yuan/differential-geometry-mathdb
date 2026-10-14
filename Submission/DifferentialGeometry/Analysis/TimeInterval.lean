import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.Topology

namespace DifferentialGeometry.Geometry.Curvature

inductive TimeEndpoint where
  | negInf
  | finite (t : Real)
  | posInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint

namespace TimeEndpoint

def lowerLt (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s < t
  | posInf => False

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt

def lowerLe (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s <= t
  | posInf => False

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLe ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLe

def upperLt (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t < s
  | posInf => True

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt

def upperLe (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t <= s
  | posInf => True

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLe ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLe

def lowerMem (closed : Bool) (a : TimeEndpoint) (t : Real) : Prop :=
  match closed, a with
  | _, negInf => True
  | true, finite s => s <= t
  | false, finite s => s < t
  | _, posInf => False

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerMem ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerMem

def upperMem (closed : Bool) (t : Real) (b : TimeEndpoint) : Prop :=
  match closed, b with
  | _, negInf => False
  | true, finite s => t <= s
  | false, finite s => t < s
  | _, posInf => True

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperMem ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperMem

theorem lowerLt_to_mem (closed : Bool) {a : TimeEndpoint} {t : Real}
    (h : lowerLt a t) :
  lowerMem closed a t := by
  cases closed
  · cases a with
    | negInf => simp [lowerMem]
    | finite s => exact h
    | posInf => simp [lowerLt] at h
  · cases a with
    | negInf => simp [lowerMem]
    | finite s =>
        exact le_of_lt h
    | posInf => simp [lowerLt] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt_to_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt_to_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt_to_mem ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.lowerLt_to_mem

theorem upperLt_to_mem (closed : Bool) {b : TimeEndpoint} {t : Real}
    (h : upperLt t b) :
  upperMem closed t b := by
  cases closed
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s => exact h
    | posInf => simp [upperMem]
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s =>
        exact le_of_lt h
    | posInf => simp [upperMem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt_to_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt_to_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt_to_mem ``Submission.DifferentialGeometry.Geometry.Curvature.TimeEndpoint.upperLt_to_mem

end TimeEndpoint

structure RealTimeInterval where
  carrier : Set Real
  regular : Set Real
  initial : Real
  initial_mem : initial ∈ carrier
  regular_subset : regular ⊆ carrier
  regular_isOpen : IsOpen regular
  regular_mem_nhds : ∀ {t : Real}, t ∈ regular -> carrier ∈ 𝓝 t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval

namespace RealTimeInterval

private theorem endpointCarrier_mem_nhds
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool) {t : Real}
    (ht : TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b) :
    {s : Real |
      TimeEndpoint.lowerMem lowerClosed a s ∧
        TimeEndpoint.upperMem upperClosed s b} ∈ 𝓝 t := by
  have hstrict :
      {s : Real | TimeEndpoint.lowerLt a s ∧ TimeEndpoint.upperLt s b} ∈ 𝓝 t := by
    cases a with
    | negInf =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            refine Filter.mem_of_superset (Iio_mem_nhds ht.2) ?_
            intro s hs
            exact ⟨trivial, hs⟩
        | posInf =>
            simp [TimeEndpoint.lowerLt, TimeEndpoint.upperLt]
    | finite a =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            change Set.Ioo a b ∈ 𝓝 t
            exact Ioo_mem_nhds ht.1 ht.2
        | posInf =>
            refine Filter.mem_of_superset (Ioi_mem_nhds ht.1) ?_
            intro s hs
            exact ⟨hs, trivial⟩
    | posInf =>
        simp [TimeEndpoint.lowerLt] at ht
  exact
    Filter.mem_of_superset hstrict (by
      intro s hs
      exact
        ⟨TimeEndpoint.lowerLt_to_mem lowerClosed hs.1,
          TimeEndpoint.upperLt_to_mem upperClosed hs.2⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.endpointCarrier_mem_nhds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.endpointCarrier_mem_nhds target :: scope.openDecls } }

abbrev FlowTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.carrier}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime

abbrev RegularTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.regular}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime

def initialTime (D : RealTimeInterval) : D.FlowTime :=
  ⟨D.initial, D.initial_mem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime

def regularToFlow {D : RealTimeInterval} (t : D.RegularTime) : D.FlowTime :=
  ⟨t.1, D.regular_subset t.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow

@[simp] theorem initialTime_val (D : RealTimeInterval) :
    (D.initialTime : Real) = D.initial := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime_val ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initialTime_val

@[simp] theorem regularToFlow_val {D : RealTimeInterval} (t : D.RegularTime) :
    (D.regularToFlow t : Real) = (t : Real) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow_val ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow_val

theorem exists_Icc_regular (D : RealTimeInterval) {t : Real}
    (ht : t ∈ D.regular) :
    ∃ a b : Real, t ∈ Set.Ioo a b ∧ Set.Icc a b ⊆ D.regular := by
  obtain ⟨a, b, _htIcc, hIcc, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (D.regular_isOpen.mem_nhds ht)
  exact ⟨a, b, Icc_mem_nhds_iff.mp hIcc, hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_Icc_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_Icc_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_Icc_regular ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_Icc_regular

def timeShift (D : RealTimeInterval) (τ : Real) : RealTimeInterval where
  carrier := {s : Real | s + τ ∈ D.carrier}
  regular := {s : Real | s + τ ∈ D.regular}
  initial := D.initial - τ
  initial_mem := by
    simpa [sub_add_cancel] using D.initial_mem
  regular_subset := by
    intro s hs
    exact D.regular_subset hs
  regular_isOpen := by
    exact D.regular_isOpen.preimage (continuous_id.add continuous_const)
  regular_mem_nhds := by
    intro s hs
    simpa [Set.preimage] using
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (D.regular_mem_nhds hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift

@[simp] theorem timeShift_carrier (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).carrier = {s : Real | s + τ ∈ D.carrier} := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_carrier ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_carrier

@[simp] theorem timeShift_regular (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).regular = {s : Real | s + τ ∈ D.regular} := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_regular ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_regular

@[simp] theorem timeShift_initial (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).initial = D.initial - τ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_initial ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_initial

def ofEndpoints
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool)
    (initial : Real)
    (hinit :
      TimeEndpoint.lowerMem lowerClosed a initial ∧
        TimeEndpoint.upperMem upperClosed initial b) : RealTimeInterval where
  carrier := {t : Real |
    TimeEndpoint.lowerMem lowerClosed a t ∧
      TimeEndpoint.upperMem upperClosed t b}
  regular := {t : Real | TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b}
  initial := initial
  initial_mem := hinit
  regular_subset := by
    intro t ht
    exact
      ⟨TimeEndpoint.lowerLt_to_mem lowerClosed ht.1,
        TimeEndpoint.upperLt_to_mem upperClosed ht.2⟩
  regular_isOpen := by
    have h1 : IsOpen {t : Real | TimeEndpoint.lowerLt a t} := by
      cases a with
      | negInf => simp [TimeEndpoint.lowerLt]
      | finite s =>
          change IsOpen (Set.Ioi s)
          exact isOpen_Ioi
      | posInf => simp [TimeEndpoint.lowerLt]
    have h2 : IsOpen {t : Real | TimeEndpoint.upperLt t b} := by
      cases b with
      | negInf => simp [TimeEndpoint.upperLt]
      | finite s =>
          change IsOpen (Set.Iio s)
          exact isOpen_Iio
      | posInf => simp [TimeEndpoint.upperLt]
    exact h1.inter h2
  regular_mem_nhds := by
    intro t ht
    exact endpointCarrier_mem_nhds a b lowerClosed upperClosed ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ofEndpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ofEndpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ofEndpoints ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ofEndpoints

def closed (a b : Real) (hab : a ≤ b) : RealTimeInterval where
  carrier := Set.Icc a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Icc_mem_nhds ht.1 ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed

def closedOpen (a b : Real) (hab : a < b) : RealTimeInterval where
  carrier := Set.Ico a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ico_mem_nhds ht.1 ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen

theorem timeShift_closedOpen_carrier
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).carrier = Set.Ico 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_carrier ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_carrier

theorem timeShift_closedOpen_regular
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).regular = Set.Ioo 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_regular ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.timeShift_closedOpen_regular

def openInterval (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioo a b) : RealTimeInterval where
  carrier := Set.Ioo a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioo_mem_nhds ht.1 ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval

def ancient (T : Real) : RealTimeInterval :=
  ofEndpoints TimeEndpoint.negInf (TimeEndpoint.finite T) _root_.Bool.false _root_.Bool.false (T - 1) (by
    simp [TimeEndpoint.lowerMem, TimeEndpoint.upperMem])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient

@[simp] theorem ancient_carrier (T : Real) :
    (ancient T).carrier = Set.Iio T := by
  ext t
  simp [ancient, ofEndpoints, TimeEndpoint.lowerMem, TimeEndpoint.upperMem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_carrier ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_carrier

@[simp] theorem ancient_regular (T : Real) :
    (ancient T).regular = Set.Iio T := by
  ext t
  simp [ancient, ofEndpoints, TimeEndpoint.lowerLt, TimeEndpoint.upperLt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_regular ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_regular

@[simp] theorem ancient_initial (T : Real) :
    (ancient T).initial = T - 1 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_initial ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.ancient_initial

noncomputable def openWindowLeft (a t₀ : Real) (n : Nat) : Real :=
  a + (t₀ - a) / ((n : Real) + 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowLeft ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowLeft

noncomputable def openWindowRight (b t₀ : Real) (n : Nat) : Real :=
  b - (b - t₀) / ((n : Real) + 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowRight ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindowRight

def openWindow (a b t₀ : Real) (n : Nat) : Set Real :=
  Set.Icc (openWindowLeft a t₀ n) (openWindowRight b t₀ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow

theorem openWindow_subset {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) (n : Nat) :
    openWindow a b t₀ n ⊆ Set.Ioo a b := by
  intro t ht
  have hden : (0 : Real) < (n : Real) + 2 := by positivity
  have hleft : a < openWindowLeft a t₀ n := by
    have hfrac : 0 < (t₀ - a) / ((n : Real) + 2) :=
      div_pos (sub_pos.mpr ht₀.1) hden
    simp only [openWindowLeft]
    linarith
  have hright : openWindowRight b t₀ n < b := by
    have hfrac : 0 < (b - t₀) / ((n : Real) + 2) :=
      div_pos (sub_pos.mpr ht₀.2) hden
    simp only [openWindowRight]
    linarith
  exact ⟨hleft.trans_le ht.1, ht.2.trans_lt hright⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_subset ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_subset

theorem initial_mem_window {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) (n : Nat) :
    t₀ ∈ openWindow a b t₀ n := by
  have hden : (0 : Real) < (n : Real) + 2 := by positivity
  have hden_ge : (1 : Real) ≤ (n : Real) + 2 := by
    have hn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have hleft : openWindowLeft a t₀ n ≤ t₀ := by
    have hfrac : (t₀ - a) / ((n : Real) + 2) ≤ t₀ - a := by
      rw [div_le_iff₀ hden]
      calc
        t₀ - a = (t₀ - a) * 1 := (mul_one _).symm
        _ ≤ (t₀ - a) * ((n : Real) + 2) :=
          mul_le_mul_of_nonneg_left hden_ge (sub_nonneg.mpr ht₀.1.le)
    simp only [openWindowLeft]
    linarith
  have hright : t₀ ≤ openWindowRight b t₀ n := by
    have hfrac : (b - t₀) / ((n : Real) + 2) ≤ b - t₀ := by
      rw [div_le_iff₀ hden]
      calc
        b - t₀ = (b - t₀) * 1 := (mul_one _).symm
        _ ≤ (b - t₀) * ((n : Real) + 2) :=
          mul_le_mul_of_nonneg_left hden_ge (sub_nonneg.mpr ht₀.2.le)
    simp only [openWindowRight]
    linarith
  exact ⟨hleft, hright⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initial_mem_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initial_mem_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initial_mem_window ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.initial_mem_window

theorem openWindow_mono {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    {n m : Nat} (hnm : n ≤ m) :
    openWindow a b t₀ n ⊆ openWindow a b t₀ m := by
  intro t ht
  have hnpos : (0 : Real) < (n : Real) + 2 := by positivity
  have hden : (n : Real) + 2 ≤ (m : Real) + 2 := by
    have hcast : (n : Real) ≤ (m : Real) := Nat.cast_le.mpr hnm
    linarith
  have hleft : openWindowLeft a t₀ m ≤ openWindowLeft a t₀ n := by
    have hfrac : (t₀ - a) / ((m : Real) + 2) ≤
        (t₀ - a) / ((n : Real) + 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr ht₀.1.le) hnpos hden
    simp only [openWindowLeft]
    linarith
  have hright : openWindowRight b t₀ n ≤ openWindowRight b t₀ m := by
    have hfrac : (b - t₀) / ((m : Real) + 2) ≤
        (b - t₀) / ((n : Real) + 2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr ht₀.2.le) hnpos hden
    simp only [openWindowRight]
    linarith
  exact ⟨hleft.trans ht.1, ht.2.trans hright⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_mono ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openWindow_mono

theorem mem_openWindow {a b t₀ t : Real} (ht : t ∈ Set.Ioo a b) :
    ∃ n : Nat, t ∈ openWindow a b t₀ n := by
  have hta : 0 < t - a := sub_pos.mpr ht.1
  have htb : 0 < b - t := sub_pos.mpr ht.2
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (_root_.Max.max ((t₀ - a) / (t - a)) ((b - t₀) / (b - t)))
  have hnleft : (t₀ - a) / (t - a) < (n : Real) :=
    (le_max_left _ _).trans_lt hn
  have hnright : (b - t₀) / (b - t) < (n : Real) :=
    (le_max_right _ _).trans_lt hn
  refine ⟨n, ?_, ?_⟩
  · have hden : (0 : Real) < (n : Real) + 2 := by positivity
    have hkey : (t₀ - a) / ((n : Real) + 2) < t - a := by
      rw [div_lt_iff₀ hden]
      have heq : t₀ - a = (t₀ - a) / (t - a) * (t - a) := by
        field_simp
      rw [heq, mul_comm (t - a) ((n : Real) + 2)]
      calc
        (t₀ - a) / (t - a) * (t - a) < (n : Real) * (t - a) :=
          mul_lt_mul_of_pos_right hnleft hta
        _ ≤ ((n : Real) + 2) * (t - a) :=
          mul_le_mul_of_nonneg_right (by linarith) hta.le
    simp only [openWindowLeft]
    linarith
  · have hden : (0 : Real) < (n : Real) + 2 := by positivity
    have hkey : (b - t₀) / ((n : Real) + 2) < b - t := by
      rw [div_lt_iff₀ hden]
      have heq : b - t₀ = (b - t₀) / (b - t) * (b - t) := by
        field_simp
      rw [heq, mul_comm (b - t) ((n : Real) + 2)]
      calc
        (b - t₀) / (b - t) * (b - t) < (n : Real) * (b - t) :=
          mul_lt_mul_of_pos_right hnright htb
        _ ≤ ((n : Real) + 2) * (b - t) :=
          mul_le_mul_of_nonneg_right (by linarith) htb.le
    simp only [openWindowRight]
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.mem_openWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.mem_openWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.mem_openWindow ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.mem_openWindow

theorem iUnion_openWindow {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b) :
    (⋃ n : Nat, openWindow a b t₀ n) = Set.Ioo a b := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact openWindow_subset ht₀ n hn
  · intro t ht
    obtain ⟨n, hn⟩ := mem_openWindow ht
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.iUnion_openWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.iUnion_openWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.iUnion_openWindow ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.iUnion_openWindow

theorem exists_window_superset {a b t₀ c d : Real}
    (ht₀ : t₀ ∈ Set.Ioo a b) (hcd : Set.Icc c d ⊆ Set.Ioo a b) :
    ∃ n : Nat, Set.Icc c d ⊆ openWindow a b t₀ n := by
  by_cases hle : c ≤ d
  · have hc : c ∈ Set.Ioo a b := hcd ⟨le_rfl, hle⟩
    have hd : d ∈ Set.Ioo a b := hcd ⟨hle, le_rfl⟩
    obtain ⟨nc, hnc⟩ := mem_openWindow (t₀ := t₀) hc
    obtain ⟨nd, hnd⟩ := mem_openWindow (t₀ := t₀) hd
    refine ⟨max nc nd, ?_⟩
    have hnc' : c ∈ openWindow a b t₀ (_root_.Max.max nc nd) :=
      openWindow_mono ht₀ (Nat.le_max_left nc nd) hnc
    have hnd' : d ∈ openWindow a b t₀ (_root_.Max.max nc nd) :=
      openWindow_mono ht₀ (Nat.le_max_right nc nd) hnd
    intro t ht
    exact ⟨hnc'.1.trans ht.1, ht.2.trans hnd'.2⟩
  · refine ⟨0, ?_⟩
    intro t ht
    exact (hle (ht.1.trans ht.2)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_superset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_superset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_superset ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_superset

theorem exists_window_nhds {a b t₀ t : Real}
    (ht₀ : t₀ ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    ∃ n : Nat, openWindow a b t₀ n ∈ 𝓝 t := by
  obtain ⟨c, d, _htIcc, hmem, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
  obtain ⟨n, hn⟩ := exists_window_superset ht₀ hsub
  exact ⟨n, Filter.mem_of_superset hmem hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_nhds ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.exists_window_nhds

def openClosed (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioc a b) : RealTimeInterval where
  carrier := Set.Ioc a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioc_mem_nhds ht.1 ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openClosed ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openClosed

def closedInfinite (a : Real) : RealTimeInterval where
  carrier := Set.Ici a
  regular := Set.Ioi a
  initial := a
  initial_mem := by
    exact Set.mem_Ici.mpr le_rfl
  regular_subset := by
    intro t ht
    exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ici_mem_nhds (Set.mem_Ioi.mp ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedInfinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedInfinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedInfinite ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedInfinite

def openInfinite (a t₀ : Real) (ht₀ : a < t₀) : RealTimeInterval where
  carrier := Set.Ioi a
  regular := Set.Ioi a
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ioi_mem_nhds ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInfinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInfinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInfinite ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInfinite

def infiniteClosed (b t₀ : Real) (ht₀ : t₀ ≤ b) : RealTimeInterval where
  carrier := Set.Iic b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp ht))
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iic_mem_nhds (Set.mem_Iio.mp ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteClosed ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteClosed

def infiniteOpen (b t₀ : Real) (ht₀ : t₀ < b) : RealTimeInterval where
  carrier := Set.Iio b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iio_mem_nhds ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteOpen ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteOpen

def univ (t₀ : Real) : RealTimeInterval where
  carrier := Set.univ
  regular := Set.univ
  initial := t₀
  initial_mem := trivial
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_univ
  regular_mem_nhds := by
    intro t ht
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ ``Submission.DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ

end RealTimeInterval

end DifferentialGeometry.Geometry.Curvature
