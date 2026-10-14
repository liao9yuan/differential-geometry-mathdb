import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.MildSolutionExistence
import Submission.DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.PrincipalSymbol
import Mathlib.Geometry.Manifold.MFDeriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry
namespace PDE

universe u v

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def IsQuasilinearMetricParabolicSolution
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M) (T : ℝ)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  0 < T ∧ g_fam 0 = g₀ ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
                  (F (g_fam t) x v w) (Set.Ici 0) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.IsQuasilinearMetricParabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.IsQuasilinearMetricParabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.IsQuasilinearMetricParabolicSolution ``Submission.DifferentialGeometry.PDE.IsQuasilinearMetricParabolicSolution

def IsStrictlyParabolicMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
    DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol F g σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.IsStrictlyParabolicMetricRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.IsStrictlyParabolicMetricRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.IsStrictlyParabolicMetricRHS ``Submission.DifferentialGeometry.PDE.IsStrictlyParabolicMetricRHS

def IsSmoothQuasilinearMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) : Prop :=
  (∀ (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x => F g x
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E j)))
        (chartAt H α).source)
    ∧ ∀ g : SmoothRiemannianMetric I M, IsStrictlyParabolicMetricRHS F g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS ``Submission.DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS

def IsLinearTensorParabolicMildSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (T : ℝ) (u : ℝ → X) : Prop :=
  0 < T ∧ u 0 = u₀ ∧
    ContinuousOn u (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (F τ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution ``Submission.DifferentialGeometry.PDE.IsLinearTensorParabolicMildSolution

omit [SigmaCompactSpace M] [T2Space M] in
theorem exists_linear_tensor_parabolic_mild_solution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ → X,
      IsLinearTensorParabolicMildSolution S u₀ F T u := by
  refine ⟨1, Analysis.Parabolic.QuasiLinear.duhamel S u₀ F, ?_, ?_, ?_, ?_⟩
  · exact zero_lt_one
  · exact Analysis.Parabolic.QuasiLinear.duhamel_zero S u₀ F
  · have h_cont :
        ContinuousOn (Analysis.Parabolic.QuasiLinear.duhamel S u₀ F)
          (Set.Ici (0 : ℝ)) :=
      Analysis.Parabolic.QuasiLinear.duhamel_continuousOn S u₀ hF
    exact h_cont.mono (Set.Icc_subset_Ici_self)
  · intro t _
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.exists_linear_tensor_parabolic_mild_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.exists_linear_tensor_parabolic_mild_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.exists_linear_tensor_parabolic_mild_solution ``Submission.DifferentialGeometry.PDE.exists_linear_tensor_parabolic_mild_solution

end PDE
end DifferentialGeometry
