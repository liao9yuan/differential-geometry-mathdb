import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarHessian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private theorem ricciTower_eq_totalNabla
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    ricCovTower (I := I) (S.base.metric t) (S.base.metric t) 1 x =
      totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
        (S.ricci t) x := by
  change totalNabla0S (𝕜 := ℝ) (I := I) 2
      (leviCivitaConnectionOfMetric (I := I) (S.base.metric t))
      (metricRicci (I := I) (S.base.metric t)) _ x =
    totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
      (S.ricci t) x
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTower_eq_totalNabla
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.ricciTower_eq_totalNabla target :: scope.openDecls } }

theorem sqrt_nablaRicci_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 1 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 3
      (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
        (S.ricci t) x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * B := by
  have hsq := ricTower_normSq_le (I := I) S t 1 x
  rw [ricciTower_eq_totalNabla (I := I) S t x] at hsq
  have hsq' :
      Real.sqrt (normSq0S (I := I) (S.base.metric t) x 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
          (S.ricci t) x)) ≤
        Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 *
          nablaKRm04NormSqIntrinsic S 1 t x) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity)] at hsq'
  have hjet' : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) ≤ B := by
    have heq := curvNormSq_eq (I := I) S 1 t x
    change Real.sqrt (curvDerivNormSq (I := I) (M := M) 1 (S.base.metric t) x) ≤ B at hjet
    rw [heq] at hjet
    exact hjet
  exact hsq'.trans (mul_le_mul_of_nonneg_left hjet' (Real.sqrt_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrt_nablaRicci_le_of_curvDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrt_nablaRicci_le_of_curvDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrt_nablaRicci_le_of_curvDerivNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrt_nablaRicci_le_of_curvDerivNorm

theorem sqrt_scalarHess_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 2 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 2
      (hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth (I := I) (S.base.metric t))
        (S.scalar t) (scalarSmoothOfSolution S t) x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 5 * B := by
  have hbase := sqrt_normSq_scalarHess_le_second_curvature (I := I) S t x
  have hjet' : Real.sqrt (nablaKRm04NormSqIntrinsic S 2 t x) ≤ B := by
    have heq := curvNormSq_eq (I := I) S 2 t x
    change Real.sqrt (curvDerivNormSq (I := I) (M := M) 2 (S.base.metric t) x) ≤ B at hjet
    rw [heq] at hjet
    exact hjet
  exact hbase.trans (mul_le_mul_of_nonneg_left hjet' (by positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrt_scalarHess_le_of_curvDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrt_scalarHess_le_of_curvDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrt_scalarHess_le_of_curvDerivNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrt_scalarHess_le_of_curvDerivNorm

theorem sqrt_rm04_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 0 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ B := by
  have heq := curvNormSq_eq (I := I) S 0 t x
  change Real.sqrt (curvDerivNormSq (I := I) (M := M) 0 (S.base.metric t) x) ≤ B at hjet
  rw [heq] at hjet
  simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero] using hjet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrt_rm04_le_of_curvDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrt_rm04_le_of_curvDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrt_rm04_le_of_curvDerivNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrt_rm04_le_of_curvDerivNorm

end DifferentialGeometry.PDE.RicciFlow
