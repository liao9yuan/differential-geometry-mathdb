import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CurvatureExpression
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CanonicalCurvatureEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def CurvatureExpression.sumFin {s : ℕ} : (n : ℕ) →
    (Fin n → CurvatureExpression s) → CurvatureExpression s
  | 0, _ => .zero s
  | n + 1, A => .add (A 0) (CurvatureExpression.sumFin n (fun q => A q.succ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.sumFin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.sumFin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.sumFin ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.sumFin

def CurvatureExpression.binaryContraction (k a b : ℕ)
    (e : Fin ((4 + a) + (4 + b)) ≃ Fin ((4 + k) + 4)) : CurvatureExpression (4 + k) :=
  .trace (.trace (.perm e (.product (.curvature a) (.curvature b))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.binaryContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.binaryContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.binaryContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.binaryContraction

def CurvatureExpression.gamma (k : ℕ) : CurvatureExpression (4 + (k + 1)) :=
  .add (.add
    (.smul (-1) (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic1 k q))))
    (.smul (-1) (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic2 k q)))))
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaRic3 k q)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.gamma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.gamma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.gamma ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.gamma

def CurvatureExpression.comm (k : ℕ) : CurvatureExpression (4 + (k + 1)) :=
  .smul (-1) (.add (.add
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 1 k (sigmaDiffA k q)))
    (sumFin (4 + k) (fun q => binaryContraction (k + 1) 0 (k + 1) (sigmaDiffB k q))))
    (sumFin (4 + (k + 1)) (fun q =>
      if hq : q.val = 0 then binaryContraction (k + 1) (k + 1) 0 (sigmaCurv0 k)
      else binaryContraction (k + 1) (k + 1) 0 (sigmaCurvPos k q hq))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.comm ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.comm

def CurvatureExpression.residual : (k : ℕ) → CurvatureExpression (4 + k)
  | 0 => baseResidual
  | k + 1 => .add (.add (residual k).spatialDerivative (.smul (-1) (comm k)))
      (.smul (-1) (gamma k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.residual ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.residual

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem CurvatureExpression.eval_sumFin {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) {s : ℕ} (n : ℕ)
    (A : Fin n → CurvatureExpression s) :
    (sumFin n A).eval S t = ∑ q : Fin n, (A q).eval S t := by
  induction n with
  | zero => simp only [sumFin, eval, Fin.sum_univ_zero]
  | succ n ih =>
      change (A 0).eval S t + (sumFin n (fun q => A q.succ)).eval S t = _
      rw [ih, Fin.sum_univ_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_sumFin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_sumFin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_sumFin ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_sumFin

variable [CompleteSpace E]

theorem CurvatureExpression.eval_binaryContraction {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (k a b : ℕ)
    (e : Fin ((4 + a) + (4 + b)) ≃ Fin ((4 + k) + 4)) :
    (binaryContraction k a b e).eval S t = starBaseField S t k a b 0 e := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_binaryContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_binaryContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_binaryContraction ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_binaryContraction

theorem CurvatureExpression.eval_gamma {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (k : ℕ) :
    (gamma k).eval S t = gammaStarField S t k := by
  simp only [gamma, eval, eval_sumFin, eval_binaryContraction, gammaStarField]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_gamma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_gamma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_gamma ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_gamma

theorem CurvatureExpression.eval_comm {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : RealTimeInterval.RegularTime D) (k : ℕ) :
    (comm k).eval S (t : ℝ) = commStarField S t k := by
  simp only [comm, eval, eval_sumFin, eval_binaryContraction, commStarField]
  congr 2
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.val = 0
  · simp only [dif_pos hq, eval_binaryContraction]
  · simp only [dif_neg hq, eval_binaryContraction]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_comm ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_comm

theorem CurvatureExpression.eval_residual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : RealTimeInterval.RegularTime D) (k : ℕ) :
    (residual k).eval S (t : ℝ) = rmResidualField S t k := by
  induction k with
  | zero => exact eval_baseResidual S (t : ℝ)
  | succ k ih =>
      simp only [residual, eval, eval_spatialDerivative, eval_comm, eval_gamma,
        rmResidualField, resStarNext, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_residual ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureExpression.eval_residual

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]

theorem covariantTimeDerivWithin_curvature_fixed_expression {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    covariantTimeDerivWithin S.base.metric (fun r => nablaKRm04Field S r k x) D.carrier (t : ℝ) =
      metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + (CurvatureExpression.residual k).eval S (t : ℝ) x +
      ricciTimeCorrection (S.base.metric (t : ℝ)) (nablaKRm04Field S (t : ℝ) k x) := by
  rw [CurvatureExpression.eval_residual]
  exact covariantTimeDerivWithin_curvature_canonical_residual S hS k t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_curvature_fixed_expression then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_curvature_fixed_expression"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_curvature_fixed_expression ``Submission.DifferentialGeometry.PDE.RicciFlow.covariantTimeDerivWithin_curvature_fixed_expression
end DifferentialGeometry.PDE.RicciFlow
