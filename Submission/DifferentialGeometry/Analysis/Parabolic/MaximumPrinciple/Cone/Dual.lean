import Submission.DifferentialGeometry.Analysis.Convex.ProperConeFace
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.HeatPotential.Weak

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace Real F]

def dualScalarization
    (u : Real → M → F) (phi : StrongDual Real F) : Real → M → Real :=
  fun t x ↦ phi (u t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.dualScalarization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.dualScalarization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.dualScalarization ``Submission.DifferentialGeometry.Analysis.Parabolic.dualScalarization

def IsDualHeatPotSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  ∀ phi : StrongDual Real F,
    ProperCone.IsDualElement C phi →
      IsHeatPotSupersolutionOn D G potential (dualScalarization u phi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsDualHeatPotSupersolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsDualHeatPotSupersolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsDualHeatPotSupersolutionOn ``Submission.DifferentialGeometry.Analysis.Parabolic.IsDualHeatPotSupersolutionOn

abbrev IsDualHeatSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  IsDualHeatPotSupersolutionOn D G (fun _ _ ↦ 0) C u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsDualHeatSupersolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsDualHeatSupersolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsDualHeatSupersolutionOn ``Submission.DifferentialGeometry.Analysis.Parabolic.IsDualHeatSupersolutionOn

omit [CompleteSpace E] in
theorem properCone_mem_of_dual_heat_pot_supersolution_of_potential_le
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential C u)
    (B : Real)
    (hpotential : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, potential t x ≤ B)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  intro t ht x
  by_contra hmem
  obtain ⟨phi, hphi, hnegative⟩ := C.hyperplane_separation_point hmem
  have hnonnegative :
      ∀ q : Real, q ∈ Set.Icc 0 T → ∀ y : M,
        0 ≤ dualScalarization u phi q y := by
    apply heat_pot_supersolution_nonneg
      (I := I) G hT potential (dualScalarization u phi)
        (hsol phi hphi) B hpotential
    intro y
    exact hphi (u 0 y) (hinit y)
  exact (not_lt_of_ge (hnonnegative t ht x)) hnegative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_pot_supersolution_of_potential_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_pot_supersolution_of_potential_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_pot_supersolution_of_potential_le ``Submission.DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_pot_supersolution_of_potential_le

omit [CompleteSpace E] in
theorem properCone_mem_of_dual_heat_supersolution
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsDualHeatSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G C u)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  exact properCone_mem_of_dual_heat_pot_supersolution_of_potential_le
    (I := I) G hT (fun _ _ ↦ 0) C u hsol 0 (by simp) hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_supersolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_supersolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_supersolution ``Submission.DifferentialGeometry.Analysis.Parabolic.properCone_mem_of_dual_heat_supersolution

end

end DifferentialGeometry.Analysis.Parabolic
