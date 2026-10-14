import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The parameter disk and its boundary component

The closed disk is the actual Euclidean unit disk in `ℂ ≃ ℝ²`; the
period-one boundary parametrization is `θ ↦ exp (2πiθ)`.

This proves the topological clauses of `master03:lem-plateau-component`:
loops, spanning disks (also with changed boundary parameter), and contractions
corestrict to the same connected component. The differential and area clauses
of that source lemma are not asserted in this file.
-/

noncomputable section

open _root_.ContinuousMap _root_.Set

namespace DifferentialGeometry.Topology

/-- The closed Euclidean unit disk. -/
abbrev closedDisk := Metric.closedBall (0 : ℂ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedDisk ``Submission.DifferentialGeometry.Topology.closedDisk

instance _root_.Submission.DifferentialGeometry.Topology.instContractibleSpaceElemComplexClosedDisk : ContractibleSpace closedDisk :=
  Metric.contractibleSpace_closedBall (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instContractibleSpaceElemComplexClosedDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instContractibleSpaceElemComplexClosedDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instContractibleSpaceElemComplexClosedDisk ``Submission.DifferentialGeometry.Topology.instContractibleSpaceElemComplexClosedDisk

instance _root_.Submission.DifferentialGeometry.Topology.instCompactSpaceElemComplexClosedDisk : CompactSpace closedDisk := isCompact_iff_compactSpace.mp (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instCompactSpaceElemComplexClosedDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instCompactSpaceElemComplexClosedDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instCompactSpaceElemComplexClosedDisk ``Submission.DifferentialGeometry.Topology.instCompactSpaceElemComplexClosedDisk

/-- The positively parametrized boundary with period one. -/
def diskBoundary : C(loopCircle, closedDisk) :=
  ⟨fun θ => ⟨(AddCircle.toCircle θ : ℂ), by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        (AddCircle.toCircle θ).property.le⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp AddCircle.continuous_toCircle⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskBoundary ``Submission.DifferentialGeometry.Topology.diskBoundary

@[simp] theorem diskBoundary_coe (θ : ℝ) :
    (diskBoundary (θ : loopCircle) : ℂ) = Complex.exp ((2 * Real.pi * θ : ℝ) * Complex.I) := by
  simp [diskBoundary, AddCircle.toCircle_apply_mk, Circle.coe_exp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskBoundary_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskBoundary_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskBoundary_coe ``Submission.DifferentialGeometry.Topology.diskBoundary_coe

/-- The exact trace of a continuous disk, still with its given parametrization. -/
def diskTrace {Q : Type*} [TopologicalSpace Q] (u : C(closedDisk, Q)) : freeLoop Q :=
  u.comp diskBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskTrace ``Submission.DifferentialGeometry.Topology.diskTrace

/-- A continuous disk supplies an actual nullhomotopy of its trace. -/
theorem diskTrace_nullhomotopic {Q : Type*} [TopologicalSpace Q] (u : C(closedDisk, Q)) :
    (diskTrace u).Nullhomotopic :=
  ((id_nullhomotopic closedDisk).comp_right u).comp_left diskBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskTrace_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskTrace_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskTrace_nullhomotopic ``Submission.DifferentialGeometry.Topology.diskTrace_nullhomotopic

section Component

variable {X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]

/-- A connected-domain map meeting a component stays in that component. -/
theorem map_mem_connectedComponent [PreconnectedSpace X] (f : C(X, Q))
    (x₀ : X) (q : Q) (h : f x₀ ∈ connectedComponent q) (x : X) :
    f x ∈ connectedComponent q := by
  have hx := f.continuous.mapsTo_connectedComponent x₀
  rw [PreconnectedSpace.connectedComponent_eq_univ] at hx
  rw [connectedComponent_eq h]
  exact hx (_root_.Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.map_mem_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.map_mem_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.map_mem_connectedComponent ``Submission.DifferentialGeometry.Topology.map_mem_connectedComponent

/-- The actual connected component of the boundary loop. -/
abbrev loopComponent (γ : freeLoop Q) := connectedComponent (γ 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponent ``Submission.DifferentialGeometry.Topology.loopComponent

theorem loop_mem_component (γ : freeLoop Q) (θ : loopCircle) : γ θ ∈ loopComponent γ :=
  map_mem_connectedComponent γ 0 (γ 0) mem_connectedComponent θ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loop_mem_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loop_mem_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loop_mem_component ``Submission.DifferentialGeometry.Topology.loop_mem_component

/-- Corestriction keeps the values and the parameter of the original loop. -/
def loopInComponent (γ : freeLoop Q) : freeLoop (loopComponent γ) :=
  ⟨fun θ => ⟨γ θ, loop_mem_component γ θ⟩, γ.continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopInComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopInComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopInComponent ``Submission.DifferentialGeometry.Topology.loopInComponent

@[simp] theorem loopInComponent_coe (γ : freeLoop Q) (θ : loopCircle) :
    (loopInComponent γ θ : Q) = γ θ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopInComponent_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopInComponent_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopInComponent_coe ``Submission.DifferentialGeometry.Topology.loopInComponent_coe

/-- Every disk with this boundary lies in the boundary component.
Only continuity of the boundary change is needed for this topological assertion. -/
theorem disk_mem_loopComponent (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) (z : closedDisk) :
    u z ∈ loopComponent γ := by
  apply map_mem_connectedComponent u (diskBoundary 0) (γ 0) _ z
  have h := congrArg (fun η : freeLoop Q => η 0) htrace
  change u (diskBoundary 0) = γ (ψ 0) at h
  rw [h]
  exact loop_mem_component γ (ψ 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.disk_mem_loopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.disk_mem_loopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.disk_mem_loopComponent ``Submission.DifferentialGeometry.Topology.disk_mem_loopComponent

/-- The selected disk itself, corestricted to the boundary component. -/
def diskInLoopComponent (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) :
    C(closedDisk, loopComponent γ) :=
  ⟨fun z => ⟨u z, disk_mem_loopComponent γ ψ u htrace z⟩, u.continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskInLoopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskInLoopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskInLoopComponent ``Submission.DifferentialGeometry.Topology.diskInLoopComponent

@[simp] theorem diskInLoopComponent_coe (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) (z : closedDisk) :
    (diskInLoopComponent γ ψ u htrace z : Q) = u z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskInLoopComponent_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskInLoopComponent_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskInLoopComponent_coe ``Submission.DifferentialGeometry.Topology.diskInLoopComponent_coe

theorem diskInLoopComponent_trace (γ : freeLoop Q) (ψ : C(loopCircle, loopCircle))
    (u : C(closedDisk, Q)) (htrace : diskTrace u = γ.comp ψ) :
    diskTrace (diskInLoopComponent γ ψ u htrace) = (loopInComponent γ).comp ψ := by
  ext θ
  exact congrArg (fun η : freeLoop Q => η θ) htrace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.diskInLoopComponent_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.diskInLoopComponent_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.diskInLoopComponent_trace ``Submission.DifferentialGeometry.Topology.diskInLoopComponent_trace

/-- Corestrict a given contraction, with no choice of a new disk or homotopy. -/
theorem loopInComponent_nullhomotopic (γ : freeLoop Q) (hγ : γ.Nullhomotopic) :
    (loopInComponent γ).Nullhomotopic := by
  obtain ⟨q, ⟨H⟩⟩ := hγ
  have hH (p : unitInterval × loopCircle) : H p ∈ loopComponent γ := by
    apply map_mem_connectedComponent H.toContinuousMap (0, 0) (γ 0) _ p
    simpa using (mem_connectedComponent (x := γ 0))
  have hq : q ∈ loopComponent γ := by simpa using hH (1, 0)
  refine ⟨⟨q, hq⟩, ⟨{
    toFun := fun p => ⟨H p, hH p⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro θ
    apply Subtype.ext
    exact H.apply_zero θ
  · intro θ
    apply Subtype.ext
    exact H.apply_one θ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopInComponent_nullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopInComponent_nullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopInComponent_nullhomotopic ``Submission.DifferentialGeometry.Topology.loopInComponent_nullhomotopic

theorem loopComponent_eq_of_contains (γ : freeLoop Q) (q : Q)
    (h : ∀ θ, γ θ ∈ connectedComponent q) : loopComponent γ = connectedComponent q :=
  (connectedComponent_eq (h 0)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopComponent_eq_of_contains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopComponent_eq_of_contains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopComponent_eq_of_contains ``Submission.DifferentialGeometry.Topology.loopComponent_eq_of_contains

theorem isClosed_loopComponent (γ : freeLoop Q) : IsClosed (loopComponent γ) :=
  isClosed_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosed_loopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosed_loopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosed_loopComponent ``Submission.DifferentialGeometry.Topology.isClosed_loopComponent

theorem isOpen_loopComponent [LocallyConnectedSpace Q] (γ : freeLoop Q) :
    IsOpen (loopComponent γ) := isOpen_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_loopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_loopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_loopComponent ``Submission.DifferentialGeometry.Topology.isOpen_loopComponent

instance _root_.Submission.DifferentialGeometry.Topology.instConnectedSpaceElemLoopComponent (γ : freeLoop Q) : ConnectedSpace (loopComponent γ) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instConnectedSpaceElemLoopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instConnectedSpaceElemLoopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instConnectedSpaceElemLoopComponent ``Submission.DifferentialGeometry.Topology.instConnectedSpaceElemLoopComponent

instance _root_.Submission.DifferentialGeometry.Topology.instCompactSpaceElemLoopComponent [CompactSpace Q] (γ : freeLoop Q) : CompactSpace (loopComponent γ) :=
  isCompact_iff_compactSpace.mp (isClosed_loopComponent γ).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instCompactSpaceElemLoopComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instCompactSpaceElemLoopComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instCompactSpaceElemLoopComponent ``Submission.DifferentialGeometry.Topology.instCompactSpaceElemLoopComponent

end Component

end DifferentialGeometry.Topology
