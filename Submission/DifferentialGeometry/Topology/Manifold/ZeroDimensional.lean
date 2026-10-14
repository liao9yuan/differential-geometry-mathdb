import Batteries.Tactic.Alias
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Connected
import Submission.DifferentialGeometry.Topology.Homology.EulerCharacteristic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Manifold

namespace DifferentialGeometry

variable {E H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]

theorem discrete_topology_of_finrank_eq_zero
    (I : ModelWithCorners ℝ E H) (hdim : Module.finrank ℝ E = 0) :
    DiscreteTopology N := by
  let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
  let _ : Subsingleton H :=
    ⟨fun x y ↦ I.toPartialEquiv.injOn
      (by simp only [ModelWithCorners.source_eq, Set.mem_univ])
      (by simp only [ModelWithCorners.source_eq, Set.mem_univ])
      (Subsingleton.elim (I x) (I y))⟩
  let _ : DiscreteTopology H := Subsingleton.discreteTopology
  exact ChartedSpace.discreteTopology H N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.discrete_topology_of_finrank_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.discrete_topology_of_finrank_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.discrete_topology_of_finrank_eq_zero ``Submission.DifferentialGeometry.discrete_topology_of_finrank_eq_zero

theorem subsingleton_of_preconnected_of_finrank_eq_zero
    [PreconnectedSpace N]
    (I : ModelWithCorners ℝ E H) (hdim : Module.finrank ℝ E = 0) :
    Subsingleton N := by
  let _ : DiscreteTopology N :=
    discrete_topology_of_finrank_eq_zero I hdim
  exact PreconnectedSpace.trivial_of_discrete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero ``Submission.DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero

theorem discrete_topology_of_subsingleton_model
    [Subsingleton E] (I : ModelWithCorners ℝ E H) :
    DiscreteTopology N :=
  discrete_topology_of_finrank_eq_zero I (Module.finrank_zero_iff.mpr inferInstance)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.discrete_topology_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.discrete_topology_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.discrete_topology_of_subsingleton_model ``Submission.DifferentialGeometry.discrete_topology_of_subsingleton_model

theorem finite_of_compact_subsingleton_model
    [Subsingleton E] [CompactSpace N] (I : ModelWithCorners ℝ E H) :
    Finite N := by
  let _ : DiscreteTopology N := discrete_topology_of_subsingleton_model I
  exact finite_of_compact_of_discrete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.finite_of_compact_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.finite_of_compact_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.finite_of_compact_subsingleton_model ``Submission.DifferentialGeometry.finite_of_compact_subsingleton_model

omit [FiniteDimensional ℝ E] in
theorem boundary_eq_empty_of_subsingleton_model
    [Subsingleton E] (I : ModelWithCorners ℝ E H) : I.boundary N = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hi : I.IsInteriorPoint x := by
    change extChartAt I x x ∈ interior (Set.range I)
    rw [interior_eq_iff_isOpen.mpr (isOpen_discrete _)]
    exact Set.mem_range_self _
  exact (I.isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.boundary_eq_empty_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.boundary_eq_empty_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.boundary_eq_empty_of_subsingleton_model ``Submission.DifferentialGeometry.boundary_eq_empty_of_subsingleton_model

omit [FiniteDimensional ℝ E] in
theorem boundaryless_manifold_of_subsingleton_model
    [Subsingleton E] (I : ModelWithCorners ℝ E H) : BoundarylessManifold I N :=
  ModelWithCorners.Boundaryless.of_boundary_eq_empty
    (boundary_eq_empty_of_subsingleton_model I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.boundaryless_manifold_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.boundaryless_manifold_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.boundaryless_manifold_of_subsingleton_model ``Submission.DifferentialGeometry.boundaryless_manifold_of_subsingleton_model

end DifferentialGeometry

namespace DifferentialGeometry.Homology

universe u

variable (k : Type u) [Field k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Subsingleton E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u)
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

include I

theorem finiteHomologyType_of_subsingleton_model :
    finiteHomologyType k (TopCat.of M) := by
  let _ : DiscreteTopology M :=
    DifferentialGeometry.discrete_topology_of_subsingleton_model I
  let _ : Finite M :=
    DifferentialGeometry.finite_of_compact_subsingleton_model I
  exact finiteHomologyType_of_finite_totallyDisconnected k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton_model ``Submission.DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton_model

theorem eulerChar_of_subsingleton_model :
    eulerChar k (TopCat.of M) = Nat.card M := by
  let _ : DiscreteTopology M :=
    DifferentialGeometry.discrete_topology_of_subsingleton_model I
  let _ : Finite M :=
    DifferentialGeometry.finite_of_compact_subsingleton_model I
  exact eulerChar_of_finite_totallyDisconnected k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_of_subsingleton_model ``Submission.DifferentialGeometry.Homology.eulerChar_of_subsingleton_model

end DifferentialGeometry.Homology

namespace DifferentialGeometry.VectorField

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Subsingleton E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
theorem eq_zero_of_subsingleton_model
    (V : ∀ x : M, TangentSpace I x) (x : M) : V x = 0 :=
  Subsingleton.elim (α := E) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.eq_zero_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.eq_zero_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.eq_zero_of_subsingleton_model ``Submission.DifferentialGeometry.VectorField.eq_zero_of_subsingleton_model

theorem sum_one_zeroSet_eq_eulerChar_of_subsingleton_model [CompactSpace M]
    (k : Type u) [Field k] (V : ∀ x : M, TangentSpace I x) :
    ∑ᶠ _ : {x : M | V x = 0}, (1 : ℤ) =
      DifferentialGeometry.Homology.eulerChar k (TopCat.of M) := by
  let _ : Finite M :=
    DifferentialGeometry.finite_of_compact_subsingleton_model I
  have he : {x : M | V x = 0} ≃ M :=
    Equiv.subtypeUnivEquiv (fun x => eq_zero_of_subsingleton_model V x)
  rw [DifferentialGeometry.Homology.eulerChar_of_subsingleton_model k I M]
  classical
  let _ : Fintype {x : M | V x = 0} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hc := Nat.card_congr he
  rw [Nat.card_eq_fintype_card] at hc
  exact_mod_cast hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.sum_one_zeroSet_eq_eulerChar_of_subsingleton_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.sum_one_zeroSet_eq_eulerChar_of_subsingleton_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.sum_one_zeroSet_eq_eulerChar_of_subsingleton_model ``Submission.DifferentialGeometry.VectorField.sum_one_zeroSet_eq_eulerChar_of_subsingleton_model

end DifferentialGeometry.VectorField

namespace DifferentialGeometry.Geometry

alias discrete_topology_of_finrank_eq_zero := DifferentialGeometry.discrete_topology_of_finrank_eq_zero
alias subsingleton_of_preconnected_of_finrank_eq_zero := DifferentialGeometry.subsingleton_of_preconnected_of_finrank_eq_zero

end DifferentialGeometry.Geometry
