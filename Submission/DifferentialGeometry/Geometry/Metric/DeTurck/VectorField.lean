import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.Smoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def deTurckVF (g g' : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => deTurckFun (I := I) g g' x, deTurckFun_contMDiff_total (I := I) g g'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckVF then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckVF"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckVF ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckVF

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp]
theorem deTurckVF_apply (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      deTurckFun (I := I) g g' x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckVF_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckVF_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckVF_apply ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckVF_apply

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_self (g : SmoothRiemannianMetric I M) :
    deTurckVF (I := I) g g = 0 := by
  ext x
  rw [deTurckVF_apply, deTurckFun_self_apply (I := I) g x]
  rw [ContMDiffSection.coe_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckVF_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckVF_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckVF_self ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckVF_self

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_apply_eq (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x j k •
          connectionDifference (I := I) g g' x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x j x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x k x) := by
  rw [deTurckVF_apply, deTurckFun_def, deTurckChartLocal_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckVF_apply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckVF_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckVF_apply_eq ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckVF_apply_eq

end DeTurck
end PDE
end DifferentialGeometry
