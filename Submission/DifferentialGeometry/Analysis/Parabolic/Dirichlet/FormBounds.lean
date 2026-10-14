import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem abs_dirichletMassVariation_le_norm
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    (u v : SmoothScalarDirichlet (g t)) :
    |dirichletMassVariation g t u v| ≤
      (1 / 2) * _root_.Max.max B 0 * ‖u‖ * ‖v‖ := by
  let fu : M → ℝ := fun x => |u.toFun x|
  let fv : M → ℝ := fun x => |v.toFun x|
  have hfu : _root_.MeasureTheory.MemLp fu 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    simpa only [fu, Real.norm_eq_abs] using u.memLp_two.norm
  have hfv : _root_.MeasureTheory.MemLp fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    simpa only [fv, Real.norm_eq_abs] using v.memLp_two.norm
  have hprod : _root_.MeasureTheory.Integrable
      (fun x => (1 / 2) * _root_.Max.max B 0 * (fu x * fv x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    have hbase' : _root_.MeasureTheory.Integrable (fun x => fu x * fv x)
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
      change _root_.MeasureTheory.Integrable (fu * fv)
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))
      exact hfu.integrable_mul hfv
    exact hbase'.const_mul _
  have hholder : (∫ x, fu x * fv x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))) ≤
      (_root_.MeasureTheory.eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal *
      (_root_.MeasureTheory.eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal := by
    have h := DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two hfu hfv
    rw [abs_of_nonneg (_root_.MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))] at h
    exact h
  have hfunorm : (_root_.MeasureTheory.eLpNorm fu 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal ≤ ‖u‖ := by
    rw [show _root_.MeasureTheory.eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) =
      _root_.MeasureTheory.eLpNorm u.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) by
      simpa only [fu, Real.norm_eq_abs] using
        (_root_.MeasureTheory.eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) u.toFun)]
    have hnorm := u.norm_smoothToLp_le
    change ‖u.memLp_two.toLp u.toFun‖ ≤ ‖u‖ at hnorm
    rwa [Lp.norm_toLp] at hnorm
  have hfvnorm : (_root_.MeasureTheory.eLpNorm fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal ≤ ‖v‖ := by
    rw [show _root_.MeasureTheory.eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) =
      _root_.MeasureTheory.eLpNorm v.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) by
      simpa only [fv, Real.norm_eq_abs] using
        (_root_.MeasureTheory.eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) v.toFun)]
    have hnorm := v.norm_smoothToLp_le
    change ‖v.memLp_two.toLp v.toFun‖ ≤ ‖v‖ at hnorm
    rwa [Lp.norm_toLp] at hnorm
  unfold dirichletMassVariation
  calc
    |∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
        (u.toFun x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))| ≤
      ∫ x, |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
        (u.toFun x * v.toFun x)|
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) :=
      _root_.MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 / 2) * _root_.Max.max B 0 * (fu x * fv x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
      exact _root_.MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hprod
        (Filter.Eventually.of_forall fun x => by
          change |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
              (u.toFun x * v.toFun x)| ≤
            (1 / 2) * _root_.Max.max B 0 * (fu x * fv x)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              ((htrace x).trans (le_max_left B 0)) (by norm_num))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = (1 / 2) * _root_.Max.max B 0 * (∫ x, fu x * fv x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))) := by
      rw [_root_.MeasureTheory.integral_const_mul]
    _ ≤ (1 / 2) * _root_.Max.max B 0 *
        ((_root_.MeasureTheory.eLpNorm fu 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal *
        (_root_.MeasureTheory.eLpNorm fv 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal) :=
      mul_le_mul_of_nonneg_left hholder
        (mul_nonneg (by norm_num) (le_max_right B 0))
    _ ≤ (1 / 2) * _root_.Max.max B 0 * (‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hfunorm hfvnorm ENNReal.toReal_nonneg (norm_nonneg u))
        (mul_nonneg (by norm_num) (le_max_right B 0))
    _ = (1 / 2) * _root_.Max.max B 0 * ‖u‖ * ‖v‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_norm

theorem abs_dirichletMassVariation_le_of_metric_and_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
        (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    |dirichletMassVariation g t u v| ≤
      (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by
  let uh : SmoothScalarDirichlet (g t) := ⟨u.toFun, u.smooth, u.interior_support⟩
  let vh : SmoothScalarDirichlet (g t) := ⟨v.toFun, v.smooth, v.interior_support⟩
  have hsame := abs_dirichletMassVariation_le_norm g t B htrace uh vh
  have hu := norm_smoothScalarDirichlet_le_of_metric_and_volume (g t) hCg hequiv
    Cv hCv0 hCvtop hvol u uh rfl
  have hv := norm_smoothScalarDirichlet_le_of_metric_and_volume (g t) hCg hequiv
    Cv hCv0 hCvtop hvol v vh rfl
  have hA : 0 ≤ Cv.toReal * Cg :=
    mul_nonneg ENNReal.toReal_nonneg (le_trans zero_le_one hCg)
  have hnorm : ‖uh‖ * ‖vh‖ ≤ Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
    calc
      ‖uh‖ * ‖vh‖ ≤ (Real.sqrt (Cv.toReal * Cg) * ‖u‖) *
          (Real.sqrt (Cv.toReal * Cg) * ‖v‖) :=
        mul_le_mul hu hv (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ = Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
        rw [show Real.sqrt (Cv.toReal * Cg) * ‖u‖ *
            (Real.sqrt (Cv.toReal * Cg) * ‖v‖) =
          Real.sqrt (Cv.toReal * Cg) ^ 2 * ‖u‖ * ‖v‖ by ring, Real.sq_sqrt hA]
  calc
    |dirichletMassVariation g t u v| =
        |dirichletMassVariation g t uh vh| := by
      rfl
    _ ≤ (1 / 2) * _root_.Max.max B 0 * ‖uh‖ * ‖vh‖ := hsame
    _ ≤ (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg * ‖u‖ * ‖v‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_right B 0))
    _ = (1 / 2) * _root_.Max.max B 0 * (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_of_metric_and_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_of_metric_and_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_of_metric_and_volume ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.abs_dirichletMassVariation_le_of_metric_and_volume

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
