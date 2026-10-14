import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.KineticEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Interval

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem lKinetic_eq_chart_integral
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (p : M) (a b : Real) (hab : a ≤ b)
    (us : timeH1 E (b - a))
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hslice : _root_.Set.EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (_root_.Set.Icc (0 : Real) (b - a))) :
    (∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      ∫ r in (0 : Real)..b - a,
        _root_.Inner.inner Real
          (((1 / 2 : Real) •
            chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, us.toFun r)) (us.deriv r))
          (us.deriv r) := by
  simpa only [lVelocity, SolutionOn.family_metric, smul_apply, real_inner_smul_left] using
    integral_mul_inner_mfderiv_eq_integral_chartGramOp_of_timeH1 S.family
      (fun s => T - s ^ 2) (fun _ => (1 / 2 : ℝ)) alpha p a b hab us hsrc hslice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_integral

theorem lKinetic_eq_chart_slice_integral
    (S : SolutionOn (I := I) (M := M) D) (T R : Real)
    (alpha : Real → M) (p : M) (u : timeH1 E R)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R)
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ alpha) (_root_.Set.Icc a b)) :
    (∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      ∫ r in (0 : Real)..b - a,
        _root_.Inner.inner Real
          (((1 / 2 : Real) • chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, (timeH1.slice u a b ha hbR).toFun r))
            ((timeH1.slice u a b ha hbR).deriv r))
          ((timeH1.slice u a b ha hbR).deriv r) := by
  let us : timeH1 E (b - a) := timeH1.slice u a b ha hbR
  have hslice : _root_.Set.EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (_root_.Set.Icc (0 : Real) (b - a)) := by
    intro r hr
    rw [show us.toFun r = u.toFun (a + r) from
      timeH1.slice_toFun u a b ha hbR hr]
    exact hrep ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  simpa only [us] using
    lKinetic_eq_chart_integral S T alpha p a b hab us hsrc hslice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_slice_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_slice_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_slice_integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lKinetic_eq_chart_slice_integral

theorem intervalIntegrable_lKinetic_of_chartH1
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T : Real) (alpha : Real → M) (p : M)
    (a b : Real) (hab : a ≤ b) (us : timeH1 E (b - a))
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hslice : _root_.Set.EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (_root_.Set.Icc (0 : Real) (b - a)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
  let L : Real := b - a
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L) := by
    exact continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  let K : Set E := us.toFun '' _root_.Set.Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn us.continuousOn_toFun
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    apply hreg (a + r)
    exact ⟨le_add_of_nonneg_right hr.1, by dsimp only [L] at hr; linarith [hr.2]⟩
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro z ⟨r, hr, rfl⟩
    rw [hslice hr, (isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc ⟨le_add_of_nonneg_right hr.1,
        by dsimp only [L] at hr; linarith [hr.2]⟩)
  let A : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) S.family p (τ r, us.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, us.toFun r)) (_root_.Set.Icc (0 : Real) L) :=
    hτc.prodMk us.continuousOn_toFun
  have hAcont : ContinuousOn A (_root_.Set.Icc (0 : Real) L) := by
    dsimp only [A]
    exact ((chartGramOp_cont (I := I) hS hJreg p hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩).const_smul (1 / 2 : Real)
  have hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using
      hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hS hJreg hJc p hKchart hKc
  have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (τ r, us.toFun r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hquad := timeQuad_int A hA C hC hL us.deriv
  have hpoint := chartGramOp_inner_deriv_ae_of_timeH1 S.family
    (fun s => T - s ^ 2) alpha p a b us hsrc hslice
  have hpoint' :
      (fun r ↦ (1 / 2 : Real) *
        (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
          (lVelocity (I := I) alpha (r + a))
          (lVelocity (I := I) alpha (r + a))) =ᵐ[volume.restrict (Ι (0 : Real) L)]
        fun r ↦ _root_.Inner.inner Real (A r (us.deriv r)) (us.deriv r) := by
    rw [_root_.Set.uIoc_of_le hL, _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    filter_upwards [hpoint] with r hr
    rw [add_comm r a]
    simpa only [A, τ, lVelocity, SolutionOn.family_metric, smul_apply,
      real_inner_smul_left] using
        congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) hr.symm
  have hshift : IntervalIntegrable (fun r ↦ (1 / 2 : Real) *
      (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
        (lVelocity (I := I) alpha (r + a))
        (lVelocity (I := I) alpha (r + a))) _root_.MeasureTheory.MeasureSpace.volume 0 L :=
    hquad.congr_ae hpoint'.symm
  have horig := (IntervalIntegrable.comp_add_right_iff
    (f := fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
    (a := 0) (b := L) (c := a)).mp hshift
  simpa only [zero_add, L, sub_add_cancel] using horig

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_chartH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_chartH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_chartH1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_chartH1

theorem intervalIntegrable_lKinetic_of_timeH1
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T R : Real) (alpha : Real → M) (p : M) (u : timeH1 E R)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R)
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun ((extChartAt I p) ∘ alpha) (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
  let us : timeH1 E (b - a) := timeH1.slice u a b ha hbR
  have hslice : _root_.Set.EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (_root_.Set.Icc (0 : Real) (b - a)) := by
    intro r hr
    rw [show us.toFun r = u.toFun (a + r) from
      timeH1.slice_toFun u a b ha hbR hr]
    exact hrep ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  exact intervalIntegrable_lKinetic_of_chartH1 S hS T alpha p a b hab us hsrc hslice hreg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_timeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_timeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_timeH1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lKinetic_of_timeH1

end DifferentialGeometry.PDE.RicciFlow.Perelman
