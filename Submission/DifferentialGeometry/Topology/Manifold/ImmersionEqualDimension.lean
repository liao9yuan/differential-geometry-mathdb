import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem isImmersionAtOfComplement_unit_of_equalDimension (f : M → N) (x : M)
    (h : _root_.Manifold.IsImmersionAt I J ∞ f x) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsImmersionAtOfComplement Unit I J ∞ f x := by
  let C := h.complement
  let L : C →ₗ[ℝ] F := h.equiv.toLinearMap.comp (LinearMap.inr ℝ E C)
  have hL : _root_.Function.Injective L := by
    intro c d he
    exact congrArg (fun p : E × C => p.2) (h.equiv.injective he)
  let : FiniteDimensional ℝ C := FiniteDimensional.of_injective L hL
  have heq := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at heq
  change Module.finrank ℝ E + Module.finrank ℝ C = Module.finrank ℝ F at heq
  have hzero : Module.finrank ℝ C = 0 := by omega
  let e : C ≃L[ℝ] Unit :=
    (LinearEquiv.ofFinrankEq (R := ℝ) C Unit (by rw [hzero]; exact (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Unit)).symm)).toContinuousLinearEquiv
  exact h.isImmersionAtOfComplement_complement.trans_F e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isImmersionAtOfComplement_unit_of_equalDimension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isImmersionAtOfComplement_unit_of_equalDimension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isImmersionAtOfComplement_unit_of_equalDimension ``Submission.DifferentialGeometry.Topology.Manifold.isImmersionAtOfComplement_unit_of_equalDimension
end DifferentialGeometry.Topology.Manifold
