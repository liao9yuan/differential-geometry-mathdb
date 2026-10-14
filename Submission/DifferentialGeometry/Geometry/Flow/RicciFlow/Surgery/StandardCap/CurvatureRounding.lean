import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ScalarRounding
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompatibleEnd
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalLeastImprovement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }

theorem exists_curvature_rounding_collar {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 10000) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ q : S2 × ℝ, q.2 ∈ _root_.Set.Ico (-2 * A) 0 → ∀ u v : E3,
        metric.inner (conformalChart q : E3) u u *
          metric.inner (conformalChart q : E3) v v -
          (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0 →
        0 < sectionalCurvature metric (conformalChart q : E3) u v) ∧
      (∀ z ∈ _root_.Set.Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            η * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < η ∧
      ∀ h : SmoothRiemannianMetric IC (roundingCollar A),
        metricDerivENormSupOn _root_.Set.univ 2 h (roundingReference A) (roundingReference A) <
          ENNReal.ofReal (1 / 100000000 : ℝ) →
        ∀ x : roundingCollar A,
          metricScalarAt h x + (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) / 2 ≤
              metricScalarAt (roundingMetric A h) x ∧
            2 * leastCurvatureOperatorEigenvalueAt h x (metricAlgebraicCurvatureTensorAt h x) +
                (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) / 2 ≤
              2 * leastCurvatureOperatorEigenvalueAt (roundingMetric A h) x
                (metricAlgebraicCurvatureTensorAt (roundingMetric A h) x) := by
  obtain ⟨A, hA, hAsmall, hprofile, hnorm, hscalar⟩ :=
    exists_scalar_rounding_collar hη (hηsmall.trans (by norm_num))
  refine ⟨A, hA, hAsmall, (fun q hq u v hplane =>
    sectionalCurvature_conformalChart_pos q hq.2 u v hplane), hprofile, hnorm, ?_⟩
  intro h hclose x
  have hj (k : ℕ) (hk : k ≤ 2) :
      metricDerivNorm k h (roundingReference A) (roundingReference A) x ≤ 1 / 100000000 :=
    (metricDerivNorm_lt_of_sup_lt _root_.Set.univ 2 h (roundingReference A) (roundingReference A)
      hclose hk (_root_.Set.mem_univ x)).le
  obtain ⟨hF, hp, hd, hrel⟩ := hprofile (x : S2 × ℝ).2 x.property
  have hD : 0 ≤ -deriv (deriv conformalFactor) (x : S2 × ℝ).2 := neg_nonneg.mpr hd.le
  have hsmall (k : ℕ) (hk : k ≤ 2) :
      |iteratedDeriv k conformalFactor (x : S2 × ℝ).2| ≤ 1 / 10000 := by
    have hh := norm_iteratedDeriv_le_intervalDerivativeNorm contDiff_conformalFactor hk
      (show (x : S2 × ℝ).2 ∈ _root_.Set.Icc (-A) 0 from ⟨x.property.1.le, x.property.2.le⟩)
    rw [Real.norm_eq_abs] at hh
    exact (hh.trans hnorm.le).trans hηsmall
  have hrel' : _root_.Max.max |conformalFactor (x : S2 × ℝ).2| |deriv conformalFactor (x : S2 × ℝ).2| ≤
      -deriv (deriv conformalFactor) (x : S2 × ℝ).2 / 10000 := by
    have hh := hrel.trans (mul_le_mul_of_nonneg_right hηsmall hD)
    calc
      _ ≤ (1 / 10000 : ℝ) * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) := hh
      _ = _ := by ring
  constructor
  · have hh := hscalar h
      (hclose.trans_le (ENNReal.ofReal_le_ofReal (by norm_num :
        (1 / 100000000 : ℝ) ≤ 1 / 10000))) x
    linarith
  · exact least_curvature_conformal_improvement_of_roundCylinder_metric_jets
      (roundingCollar A) h x (1 / 100000000) le_rfl hj conformalFactor contDiff_conformalFactor
      hF.le (by simpa only [iteratedDeriv_zero] using hsmall 0 (by norm_num))
      ((le_max_left _ _).trans hrel') hp.le
      (by simpa only [iteratedDeriv_one, abs_of_pos hp] using hsmall 1 (by norm_num))
      (by simpa only [abs_of_pos hp] using (le_max_right _ _).trans hrel')
      (by simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero, abs_of_neg hd] using hsmall 2 (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_curvature_rounding_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_curvature_rounding_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_curvature_rounding_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_curvature_rounding_collar

end DifferentialGeometry.PDE.RicciFlow.StandardCap
