import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.Range
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Cone.Invariant
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Endpoint
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Alternating
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Alternating.Contraction
import Submission.DifferentialGeometry.Tensor.Alternating.ContractionSubbundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace LinearEquiv
open _root_.LinearEquiv

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {source : V →ₗ[ℝ] V} {target : W →ₗ[ℝ] W}

open _root_.LinearEquiv in
private theorem map_ker_eq_ker_of_intertwining (e : V ≃ₗ[ℝ] W)
    (h : e.toLinearMap.comp source =
      target.comp e.toLinearMap) :
    Submodule.map e.toLinearMap source.ker = target.ker := by
  apply le_antisymm
  · rintro y ⟨v, hv, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L v) h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hv] at hz
    simpa using hz.symm
  · intro y hy
    let v : V := e.symm y
    have hv : source v = 0 := by
      apply e.injective
      have hmapv : e v = y := by simp [v]
      calc
        e (source v) = target (e v) := by
          simpa [LinearMap.comp_apply] using
            congrArg (fun L : V →ₗ[ℝ] W => L v) h
        _ = target y := by rw [hmapv]
        _ = 0 := LinearMap.mem_ker.mp hy
        _ = e 0 := by simp
    exact ⟨v, hv, by simp [v]⟩

run_cmd do
  let target := ``Submission.LinearEquiv.map_ker_eq_ker_of_intertwining
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LinearEquiv.map_ker_eq_ker_of_intertwining target :: scope.openDecls } }

open _root_.LinearEquiv in
private theorem map_range_eq_range_of_intertwining (e : V ≃ₗ[ℝ] W)
    (h : e.toLinearMap.comp source =
      target.comp e.toLinearMap) :
    Submodule.map e.toLinearMap source.range = target.range := by
  apply le_antisymm
  · rintro y ⟨v, ⟨z, rfl⟩, rfl⟩
    refine ⟨e z, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h
    simpa [LinearMap.comp_apply] using hz.symm
  · intro y hy
    rcases hy with ⟨w, rfl⟩
    let z : V := e.symm w
    refine ⟨source z, ⟨z, rfl⟩, ?_⟩
    have hz := congrArg (fun L : V →ₗ[ℝ] W => L z) h
    simpa [z, LinearMap.comp_apply] using hz

run_cmd do
  let target := ``Submission.LinearEquiv.map_range_eq_range_of_intertwining
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `LinearEquiv.map_range_eq_range_of_intertwining target :: scope.openDecls } }

end LinearEquiv

namespace DifferentialGeometry.Geometry.Connection

structure LinearIsometryKernelIntertwining
    (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (source : V →L[ℝ] V) (target : W →L[ℝ] W) where
  map : V ≃ₗᵢ[ℝ] W
  intertwining :
    map.toLinearMap.comp source.toLinearMap =
      target.toLinearMap.comp map.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining

namespace LinearIsometryKernelIntertwining

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {source : V →L[ℝ] V} {target : W →L[ℝ] W}

theorem map_ker_eq_ker (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.ker = target.ker := by
  exact h.map.toLinearEquiv.map_ker_eq_ker_of_intertwining h.intertwining

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_ker_eq_ker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_ker_eq_ker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_ker_eq_ker ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_ker_eq_ker

theorem finrank_ker_eq (h : LinearIsometryKernelIntertwining V W source target) :
    Module.finrank ℝ source.ker = Module.finrank ℝ target.ker := by
  rw [← h.map_ker_eq_ker]
  exact (Submodule.equivMapOfInjective h.map.toLinearMap h.map.injective source.ker).finrank_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.finrank_ker_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.finrank_ker_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.finrank_ker_eq ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.finrank_ker_eq

theorem map_range_eq_range (h : LinearIsometryKernelIntertwining V W source target) :
    Submodule.map h.map.toLinearMap source.range = target.range := by
  exact h.map.toLinearEquiv.map_range_eq_range_of_intertwining h.intertwining

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_range_eq_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_range_eq_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_range_eq_range ``Submission.DifferentialGeometry.Geometry.Connection.LinearIsometryKernelIntertwining.map_range_eq_range

end LinearIsometryKernelIntertwining

universe uX uF

variable {X : Type uX} (V : X → Type uF)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def IsTransportInvariantSubmoduleFamily
    (P : LinearIsometricTransport V)
    (S : ∀ x, Submodule ℝ (V x)) : Prop :=
  ∀ x y, Submodule.map (P.transport x y).toLinearMap (S x) = S y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily

namespace IsTransportInvariantSubmoduleFamily

variable {P : LinearIsometricTransport V} {S : ∀ x, Submodule ℝ (V x)}

theorem map_transport (h : IsTransportInvariantSubmoduleFamily V P S) (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (S x) = S y :=
  h x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.map_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.map_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.map_transport ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.map_transport

theorem transport_mem_iff (h : IsTransportInvariantSubmoduleFamily V P S)
    (x y : X) (v : V x) : P.transport x y v ∈ S y ↔ v ∈ S x := by
  rw [← h x y]
  constructor
  · rintro ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport x y).injective
      change P.transport x y w = P.transport x y v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.transport_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.transport_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.transport_mem_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.transport_mem_iff

theorem orthogonal (h : IsTransportInvariantSubmoduleFamily V P S) :
    IsTransportInvariantSubmoduleFamily V P
      (fun x => Submodule.orthogonal (S x)) := by
  intro x y
  calc
    Submodule.map (P.transport x y).toLinearMap
        (Submodule.orthogonal (S x)) =
      Submodule.orthogonal
        (Submodule.map (P.transport x y).toLinearMap (S x)) := by
          exact Submodule.map_orthogonal_equiv (S x) (P.transport x y)
    _ = Submodule.orthogonal (S y) :=
      congrArg Submodule.orthogonal (h x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.orthogonal ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.orthogonal

theorem range_of_isSymmetric
    [∀ x, FiniteDimensional ℝ (V x)]
    {A : ∀ x, V x →L[ℝ] V x}
    (hker : IsTransportInvariantSubmoduleFamily V P (fun x => (A x).ker))
    (hA : ∀ x, (A x : V x →ₗ[ℝ] V x).IsSymmetric) :
    IsTransportInvariantSubmoduleFamily V P (fun x => (A x).range) := by
  have hrange (x : X) :
      (A x).range = Submodule.orthogonal (A x).ker := by
    rw [← (hA x).orthogonal_range]
    exact (A x).range.orthogonal_orthogonal.symm
  intro x y
  change Submodule.map (P.transport x y).toLinearMap (A x).range =
    (A y).range
  rw [hrange x, hrange y]
  exact orthogonal (V := V) hker x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.range_of_isSymmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.range_of_isSymmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.range_of_isSymmetric ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantSubmoduleFamily.range_of_isSymmetric

end IsTransportInvariantSubmoduleFamily

def IsTransportInvariantAlternatingSubmoduleFamily
    (P : LinearIsometricTransport V)
    (K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)) : Prop :=
  ∀ x y,
    Submodule.map
      (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ
        (P.transport x y).toLinearEquiv).toLinearMap (K x) = K y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily

namespace IsTransportInvariantAlternatingSubmoduleFamily

variable {P : LinearIsometricTransport V}
  {K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→ₗ[ℝ] ℝ)}

theorem contractionAnnihilator
    (h : IsTransportInvariantAlternatingSubmoduleFamily V P K) :
    IsTransportInvariantSubmoduleFamily V P
      (fun x => AlternatingMap.contractionAnnihilator (K x)) := by
  intro x y
  have hback :
      Submodule.map
          (AlternatingMap.domLCongr ℝ ℝ (Fin 2) ℝ
            (P.transport x y).symm.toLinearEquiv).toLinearMap (K y) =
        K x := by
    simpa [P.transport_symm V x y] using h y x
  change Submodule.map (P.transport x y).toLinearMap
      (AlternatingMap.contractionAnnihilator (K x)) =
    AlternatingMap.contractionAnnihilator (K y)
  rw [← hback]
  exact AlternatingMap.map_contractionAnnihilator_compLinearEquiv
    (K y) (P.transport x y).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily.contractionAnnihilator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily.contractionAnnihilator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily.contractionAnnihilator ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantAlternatingSubmoduleFamily.contractionAnnihilator

end IsTransportInvariantAlternatingSubmoduleFamily

def IsTransportInvariantContinuousAlternatingSubmoduleFamily
    (P : LinearIsometricTransport V)
    (K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→L[ℝ] ℝ)) : Prop :=
  ∀ x y,
    Submodule.map
      ((P.transport x y).toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
        (ι := Fin 2)).toLinearMap (K x) = K y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily

namespace IsTransportInvariantContinuousAlternatingSubmoduleFamily

variable {P : LinearIsometricTransport V}
  {K : ∀ x, Submodule ℝ (V x [⋀^Fin 2]→L[ℝ] ℝ)}

theorem contractionAnnihilator
    (h : IsTransportInvariantContinuousAlternatingSubmoduleFamily V P K) :
    IsTransportInvariantSubmoduleFamily V P
      (fun x => ContinuousAlternatingMap.contractionAnnihilator (K x)) := by
  intro x y
  have hback :
      Submodule.map
          ((P.transport x y).symm.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
            (ι := Fin 2)).toLinearMap (K y) =
        K x := by
    simpa [P.transport_symm V x y] using h y x
  change Submodule.map (P.transport x y).toLinearMap
      (ContinuousAlternatingMap.contractionAnnihilator (K x)) =
    ContinuousAlternatingMap.contractionAnnihilator (K y)
  rw [← hback]
  exact ContinuousAlternatingMap.map_contractionAnnihilator_compContinuousLinearEquiv
    (K y) (P.transport x y).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily.contractionAnnihilator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily.contractionAnnihilator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily.contractionAnnihilator ``Submission.DifferentialGeometry.Geometry.Connection.IsTransportInvariantContinuousAlternatingSubmoduleFamily.contractionAnnihilator

end IsTransportInvariantContinuousAlternatingSubmoduleFamily

structure UhlenbeckKernelTransfer (base : X)
    (fixedOperator : V base →L[ℝ] V base)
    (physicalOperator : ∀ x, V x →L[ℝ] V x)
    (P : LinearIsometricTransport V) where
  baseIntertwining : ∀ x,
    (P.transport base x).toLinearMap.comp fixedOperator.toLinearMap =
      (physicalOperator x).toLinearMap.comp (P.transport base x).toLinearMap
  pathIntertwining : ∀ x y,
    (P.transport x y).toLinearMap.comp (physicalOperator x).toLinearMap =
      (physicalOperator y).toLinearMap.comp (P.transport x y).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer

namespace UhlenbeckKernelTransfer

variable {base : X} {fixedOperator : V base →L[ℝ] V base}
  {physicalOperator : ∀ x, V x →L[ℝ] V x} {P : LinearIsometricTransport V}

theorem fixed_kernel_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Submodule.map (P.transport base x).toLinearMap fixedOperator.ker =
      (physicalOperator x).ker := by
  exact (P.transport base x).toLinearEquiv.map_ker_eq_ker_of_intertwining
    (h.baseIntertwining x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_transport ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_transport

theorem physical_kernel_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).ker =
      (physicalOperator y).ker := by
  exact (P.transport x y).toLinearEquiv.map_ker_eq_ker_of_intertwining
    (h.pathIntertwining x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_transport ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_transport

theorem fixed_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Submodule.map (P.transport base x).toLinearMap fixedOperator.range =
      (physicalOperator x).range := by
  exact (P.transport base x).toLinearEquiv.map_range_eq_range_of_intertwining
    (h.baseIntertwining x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_transport ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_transport

theorem physical_range_transport (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x y : X) :
    Submodule.map (P.transport x y).toLinearMap (physicalOperator x).range =
      (physicalOperator y).range := by
  exact (P.transport x y).toLinearEquiv.map_range_eq_range_of_intertwining
    (h.pathIntertwining x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_transport ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_transport

theorem physical_kernel_finrank_eq (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Module.finrank ℝ fixedOperator.ker = Module.finrank ℝ (physicalOperator x).ker := by
  calc
    Module.finrank ℝ fixedOperator.ker =
        Module.finrank ℝ (Submodule.map (P.transport base x).toLinearMap fixedOperator.ker) := by
      exact (Submodule.equivMapOfInjective (P.transport base x).toLinearMap
        (P.transport base x).injective fixedOperator.ker).finrank_eq
    _ = Module.finrank ℝ (physicalOperator x).ker := by
      exact congrArg (fun S : Submodule ℝ (V x) => Module.finrank ℝ S)
        (fixed_kernel_transport (V := V) h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_finrank_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_finrank_eq ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_finrank_eq

theorem physical_range_finrank_eq (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) :
    Module.finrank ℝ fixedOperator.range =
      Module.finrank ℝ (physicalOperator x).range := by
  calc
    Module.finrank ℝ fixedOperator.range =
        Module.finrank ℝ (Submodule.map (P.transport base x).toLinearMap fixedOperator.range) := by
      exact (Submodule.equivMapOfInjective (P.transport base x).toLinearMap
        (P.transport base x).injective fixedOperator.range).finrank_eq
    _ = Module.finrank ℝ (physicalOperator x).range := by
      exact congrArg (fun S : Submodule ℝ (V x) => Module.finrank ℝ S)
        (fixed_range_transport (V := V) h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_finrank_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_finrank_eq ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_range_finrank_eq

theorem physical_kernel_is_transport_invariant
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P) :
    IsTransportInvariantSubmoduleFamily V P (fun x => (physicalOperator x).ker) := by
  intro x y
  exact physical_kernel_transport (V := V) h x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_is_transport_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_is_transport_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_is_transport_invariant ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.physical_kernel_is_transport_invariant

theorem fixed_kernel_mem_iff_physical
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) (v : V base) :
    P.transport base x v ∈ (physicalOperator x).ker ↔ v ∈ fixedOperator.ker := by
  constructor
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.ker := by
      rw [fixed_kernel_transport (V := V) h x]
      exact hv
    rcases hv' with ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport base x).injective
      change P.transport base x w = P.transport base x v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.ker :=
      ⟨v, hv, rfl⟩
    rw [fixed_kernel_transport (V := V) h x] at hv'
    exact hv'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_mem_iff_physical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_mem_iff_physical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_mem_iff_physical ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_kernel_mem_iff_physical

theorem fixed_range_mem_iff_physical
    (h : UhlenbeckKernelTransfer V base fixedOperator physicalOperator P)
    (x : X) (v : V base) :
    P.transport base x v ∈ (physicalOperator x).range ↔
      v ∈ fixedOperator.range := by
  constructor
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.range := by
      rw [fixed_range_transport (V := V) h x]
      exact hv
    rcases hv' with ⟨w, hw, hwy⟩
    have : w = v := by
      apply (P.transport base x).injective
      change P.transport base x w = P.transport base x v at hwy
      exact hwy
    simpa [this] using hw
  · intro hv
    have hv' : P.transport base x v ∈
        Submodule.map (P.transport base x).toLinearMap fixedOperator.range :=
      ⟨v, hv, rfl⟩
    rw [fixed_range_transport (V := V) h x] at hv'
    exact hv'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_mem_iff_physical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_mem_iff_physical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_mem_iff_physical ``Submission.DifferentialGeometry.Geometry.Connection.UhlenbeckKernelTransfer.fixed_range_mem_iff_physical

end UhlenbeckKernelTransfer

universe uE uH uM

section LeviCivitaParallel

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

local instance tangentT2Space (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (TangentSpace I) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentT2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentT2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentT2Space ``Submission.DifferentialGeometry.Geometry.Connection.tangentT2Space

local instance tangentFiberBundle :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentFiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentFiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentFiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tangentFiberBundle

local instance tangentVectorBundle :
    VectorBundle ℝ E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tangentVectorBundle

local instance tangentSmoothVectorBundle :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have h : IsManifold I ∞ M := inferInstance
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentSmoothVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentSmoothVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentSmoothVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tangentSmoothVectorBundle

def IsParallelSubmoduleFamily [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ∀ x : M, Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b),
    Submodule.map
      (Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab).toLinearMap (S (γ a)) = S (γ b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily

namespace IsParallelSubmoduleFamily

theorem map_parallelTransportBetween [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    Submodule.map
      (Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab).toLinearMap (S (γ a)) = S (γ b) :=
  h γ hγ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.map_parallelTransportBetween then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.map_parallelTransportBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.map_parallelTransportBetween ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.map_parallelTransportBetween

theorem parallelTransportBetween_mem_iff [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) {v : TangentSpace I (γ a)} :
    Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab v ∈ S (γ b) ↔ v ∈ S (γ a) := by
  rw [← h γ hγ hab]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportBetween_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportBetween_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportBetween_mem_iff ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportBetween_mem_iff

theorem parallelTransportSectionOnIcc_mem [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) {v : TangentSpace I (γ 0)} (hv : v ∈ S (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    Riemannian.Variation.parallelTransportSectionOnIcc
        (I := I) g γ hγ hL v t ∈ S (γ t) := by
  rcases ht.1.eq_or_lt with rfl | ht_pos
  · simpa using hv
  · have hmem := (h.parallelTransportBetween_mem_iff hγ ht_pos).mpr hv
    rw [Riemannian.Variation.parallelTransportLinearEquivBetween_zero_apply] at hmem
    rw [Riemannian.Variation.parallelTransportSectionOnIcc_eq_of_mem
      (I := I) g γ hγ ht_pos hL v (t := t) ⟨ht.1, le_rfl⟩ ht] at hmem
    exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportSectionOnIcc_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportSectionOnIcc_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportSectionOnIcc_mem ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.parallelTransportSectionOnIcc_mem

theorem orthogonal [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {S : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (h : IsParallelSubmoduleFamily g S) :
    IsParallelSubmoduleFamily g
      (fun x =>
        (Tensor0SBundle.tangentMetricData (I := I) g x).metric.orthogonal (S x)) := by
  intro γ hγ a b hab
  let e := Riemannian.Variation.parallelTransportLinearEquivBetween
    (I := I) g γ hγ hab
  calc
    Submodule.map e.toLinearMap
        ((Tensor0SBundle.tangentMetricData (I := I) g (γ a)).metric.orthogonal
          (S (γ a))) =
      (Tensor0SBundle.tangentMetricData (I := I) g (γ b)).metric.orthogonal
        (Submodule.map e.toLinearMap (S (γ a))) := by
          apply Tensor0SBundle.MetricFiberData.map_orthogonal_of_inner_eq
          intro v w
          rw [Tensor0SBundle.TangentMetricData.inner_eq,
            Tensor0SBundle.TangentMetricData.inner_eq]
          exact Riemannian.Variation.parallelTransportLinearEquivBetween_inner
            (I := I) g γ hγ hab v w
    _ = (Tensor0SBundle.tangentMetricData (I := I) g (γ b)).metric.orthogonal
        (S (γ b)) := by rw [h γ hγ hab]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.orthogonal ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelSubmoduleFamily.orthogonal

end IsParallelSubmoduleFamily

def IsParallelContinuousAlternatingSubmoduleFamily [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (K : ∀ x : M,
      Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)) : Prop :=
  ∀ (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b),
    let e := (Riemannian.Variation.parallelTransportLinearEquivBetween
      (I := I) g γ hγ hab).toContinuousLinearEquiv
    Submodule.map
      (e.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap
        (K (γ a)) = K (γ b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily

namespace IsParallelContinuousAlternatingSubmoduleFamily

theorem contractionAnnihilator [I.Boundaryless]
    {g : SmoothRiemannianMetric I M}
    {K : ∀ x : M,
      Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)}
    (h : IsParallelContinuousAlternatingSubmoduleFamily g K) :
    IsParallelSubmoduleFamily g
      (fun x => ContinuousAlternatingMap.contractionAnnihilator (K x)) := by
  intro γ hγ a b hab
  let e := (Riemannian.Variation.parallelTransportLinearEquivBetween
    (I := I) g γ hγ hab).toContinuousLinearEquiv
  change Submodule.map e.toLinearMap
      (ContinuousAlternatingMap.contractionAnnihilator (K (γ a))) =
    ContinuousAlternatingMap.contractionAnnihilator (K (γ b))
  exact ContinuousAlternatingMap.map_contractionAnnihilator_of_map_eq
    (K (γ a)) (K (γ b)) e (h γ hγ hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily.contractionAnnihilator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily.contractionAnnihilator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily.contractionAnnihilator ``Submission.DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily.contractionAnnihilator

end IsParallelContinuousAlternatingSubmoduleFamily

theorem exists_smooth_parallel_contractionAnnihilator [I.Boundaryless]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (K : ContMDiffVectorSubbundle
      (I := I) (F := E [⋀^Fin 2]→L[ℝ] ℝ)
      (V := fun x => TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)
      (n := (∞ : WithTop ℕ∞)))
    (hK : K.rank = 1)
    (hparallel : IsParallelContinuousAlternatingSubmoduleFamily g K.fiber) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      (∀ x, S.fiber x =
        ContinuousAlternatingMap.contractionAnnihilator (K.fiber x)) ∧
      IsParallelSubmoduleFamily g S.fiber := by
  obtain ⟨S, hSrank, hSfiber⟩ :=
    ContinuousAlternatingMap.exists_smooth_contractionAnnihilator
      (I := I) (M := M) (F := E) (V := TangentSpace I)
      (fiberBundle := tangentFiberBundle (I := I) (M := M))
      (vectorBundle := tangentVectorBundle (I := I) (M := M))
      (smoothVectorBundle := tangentSmoothVectorBundle (I := I) (M := M))
      hE K hK
  refine ⟨S, hSrank, hSfiber, ?_⟩
  intro γ hγ a b hab
  rw [hSfiber (γ a), hSfiber (γ b)]
  exact hparallel.contractionAnnihilator γ hγ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator ``Submission.DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator

theorem exists_smooth_parallel_contractionAnnihilator_range [I.Boundaryless]
    (hE : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : ∀ x : M,
      (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
        TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)
    (hA : ContMDiff I
      (I.prod 𝓘(ℝ,
        (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun x => Bundle.TotalSpace.mk'
        ((E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) x (A x)))
    (hrange : ∀ x, Module.finrank ℝ (A x).range = 1)
    (hparallel : IsParallelContinuousAlternatingSubmoduleFamily
      g (fun x => (A x).range)) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      (∀ x, S.fiber x =
        ContinuousAlternatingMap.contractionAnnihilator (A x).range) ∧
      IsParallelSubmoduleFamily g S.fiber := by
  let basis := Module.finBasis ℝ E
  let _ : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) basis)
      |>.finiteDimensional_of_finite
  let R := ContMDiffVectorSubbundle.range A hA 1 hrange
  apply exists_smooth_parallel_contractionAnnihilator hE g R rfl
  intro γ hγ a b hab
  change Submodule.map
      (((Riemannian.Variation.parallelTransportLinearEquivBetween
        (I := I) g γ hγ hab).toContinuousLinearEquiv
          |>.continuousAlternatingMapCongrLeft (ι := Fin 2)).toLinearMap)
      (A (γ a)).range = (A (γ b)).range
  exact hparallel γ hγ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator_range ``Submission.DifferentialGeometry.Geometry.Connection.exists_smooth_parallel_contractionAnnihilator_range

end LeviCivitaParallel

end DifferentialGeometry.Geometry.Connection


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.ContDiff

namespace ContMDiffVectorSubbundle

open _root_.Submission.DifferentialGeometry (SmoothRiemannianMetric)
open _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless]

theorem isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant
    (S : ContMDiffVectorSubbundle (I := I) (F := E [⋀^Fin 2]→L[ℝ] ℝ)
      (V := Bundle.continuousAlternatingMap ℝ (Fin 2) E (TangentSpace I : M → Type _) ℝ
        (Bundle.Trivial M ℝ)) (n := ∞))
    (g : SmoothRiemannianMetric I M)
    (hS : IsCovariantlyInvariantSubmoduleFamily (CovariantDerivative.alternating (LeviCivita g) 2) S.fiber) :
    IsParallelContinuousAlternatingSubmoduleFamily g S.fiber := by
  intro γ hγ a b hab
  exact S.map_parallelTransportLinearEquivBetween_alternating 2 g hS γ hγ hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant ``Submission.ContMDiffVectorSubbundle.isParallelContinuousAlternatingSubmoduleFamily_of_covariantly_invariant

end ContMDiffVectorSubbundle
