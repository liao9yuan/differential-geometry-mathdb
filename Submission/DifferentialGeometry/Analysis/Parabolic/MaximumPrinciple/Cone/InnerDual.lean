import Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperConeIsometry
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Cone.Dual

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

def innerScalarization (u : Real → M → F) (y : F) : Real → M → Real :=
  fun t x ↦ ⟪u t x, y⟫

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.innerScalarization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.innerScalarization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.innerScalarization ``Submission.DifferentialGeometry.Analysis.Parabolic.innerScalarization

abbrev innerDualScalarization (u : Real → M → F) (y : F) : Real → M → Real :=
  innerScalarization u y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.innerDualScalarization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.innerDualScalarization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.innerDualScalarization ``Submission.DifferentialGeometry.Analysis.Parabolic.innerDualScalarization

def IsInnerDualHeatPotSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  ∀ y : F, y ∈ ProperCone.innerDual (C : Set F) →
    IsHeatPotSupersolutionOn D G potential (innerScalarization u y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatPotSupersolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatPotSupersolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatPotSupersolutionOn ``Submission.DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatPotSupersolutionOn

abbrev IsInnerDualHeatSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  IsInnerDualHeatPotSupersolutionOn D G (fun _ _ ↦ 0) C u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatSupersolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatSupersolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatSupersolutionOn ``Submission.DifferentialGeometry.Analysis.Parabolic.IsInnerDualHeatSupersolutionOn

omit [CompleteSpace E] in
theorem properCone_heat_pot_supersolution_mem_of_potential_le
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsInnerDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential C u)
    (B : Real)
    (hpotential : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, potential t x ≤ B)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  have hsol' : IsDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential C u := by
    intro phi hphi
    let y : F := (InnerProductSpace.toDual Real F).symm phi
    have hy : y ∈ ProperCone.innerDual (C : Set F) := by
      rw [ProperCone.mem_innerDual]
      intro x hx
      change 0 ≤ ⟪x, (InnerProductSpace.toDual Real F).symm phi⟫
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
      exact hphi x hx
    have heq : innerScalarization u y = dualScalarization u phi := by
      funext t x
      change ⟪u t x, (InnerProductSpace.toDual Real F).symm phi⟫ = phi (u t x)
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [← heq]
    exact hsol y hy
  exact properCone_mem_of_dual_heat_pot_supersolution_of_potential_le
    (I := I) G hT potential C u hsol' B hpotential hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.properCone_heat_pot_supersolution_mem_of_potential_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.properCone_heat_pot_supersolution_mem_of_potential_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.properCone_heat_pot_supersolution_mem_of_potential_le ``Submission.DifferentialGeometry.Analysis.Parabolic.properCone_heat_pot_supersolution_mem_of_potential_le

omit [CompleteSpace E] in
theorem properCone_heat_supersolution_mem
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsInnerDualHeatSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G C u)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  exact properCone_heat_pot_supersolution_mem_of_potential_le
    (I := I) G hT (fun _ _ ↦ 0) C u hsol 0 (by simp) hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.properCone_heat_supersolution_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.properCone_heat_supersolution_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.properCone_heat_supersolution_mem ``Submission.DifferentialGeometry.Analysis.Parabolic.properCone_heat_supersolution_mem

end

end DifferentialGeometry.Analysis.Parabolic
