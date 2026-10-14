import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.C1Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.ForceRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.VelocityRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartAction_minimizer_momentum_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAction S T a p) (sameTimeEnds u) u) :
    ∃ q P : Real → E,
      ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) ∧
      ContDiffOn Real 1 P (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn P
        (fun r ↦ (2 : Real) •
          chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u.toFun r) (q r))
        (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin P (_root_.Set.Icc (0 : Real) L))
        (fun r ↦ (2 : Real) •
          lChartForceRepresentative (I := I) S T a p u q r)
        (_root_.Set.Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  have hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L) := by
    exact (continuous_const.sub
      ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτregularity : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.regular := hreg
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K := by
    intro r hr
    exact ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := exists_chartGramOp_ae_bound hS.smoothMetric p τ hτc hτregularity
    hKc hKchart u huK
  obtain ⟨q, hq, hqae, huc1, huderiv⟩ :=
    lChartAction_minimizer_contDiffOn_one (I := I) S hS T a p hL u hreg hchart hmin
  obtain ⟨hForce, hWeak⟩ :=
    lChartAction_weak_euler_lagrange_of_isLocalMinOn (I := I) S hS T a p hL u hreg hchart hmin
  have hForceRep : ContinuousOn
      (lChartForceRepresentative (I := I) S T a p u q) (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_lChartForceRepresentative (I := I) S hS T a p u q hreg hchart hq
  have hForceAE : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartForceRepresentative (I := I) S T a p u q :=
    lChartForce_ae_eq_lChartForceRepresentative (I := I) S hS T a p u q hreg hchart hqae
  let F : Real → E := fun r ↦
    (2 : Real) • lChartForceRepresentative (I := I) S T a p u q r
  have hF : ContinuousOn F (_root_.Set.Icc (0 : Real) L) := by
    exact (hForceRep.const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv +
        ∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r) = 0 := by
    intro v hv0 hvL
    have hvmeas : _root_.MeasureTheory.AEStronglyMeasurable v.toFun
        (volume.restrict (_root_.Set.Icc (0 : Real) L)) :=
      v.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
    obtain ⟨V, hV⟩ := IsCompact.exists_bound_of_continuousOn
      _root_.CompactIccSpace.isCompact_Icc v.continuousOn_toFun
    have hForcePair : _root_.MeasureTheory.IntegrableOn
        (fun r ↦ _root_.Inner.inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        (_root_.Set.Icc (0 : Real) L) volume := by
      refine Integrable.mono' (hForce.norm.const_mul V)
        (hForce.aestronglyMeasurable.inner hvmeas) ?_
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
      calc
        ‖inner Real (lChartForce (I := I) S T a p u r) (v.toFun r)‖
            ≤ ‖lChartForce (I := I) S T a p u r‖ * ‖v.toFun r‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖lChartForce (I := I) S T a p u r‖ * V :=
          mul_le_mul_of_nonneg_left (hV r hr) (norm_nonneg _)
        _ = V * ‖lChartForce (I := I) S T a p u r‖ := mul_comm _ _
    have hForcePairI : IntervalIntegrable
        (fun r ↦ _root_.Inner.inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        volume 0 L := by
      apply IntegrableOn.intervalIntegrable
      simpa only [_root_.Set.uIcc_of_le hL.le] using hForcePair
    have hMomPairI : IntervalIntegrable
        (fun r ↦ _root_.Inner.inner Real
          (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
          (v.deriv r)) _root_.MeasureTheory.MeasureSpace.volume 0 L := by
      have hMom : _root_.MeasureTheory.Integrable
          (fun r ↦ _root_.Inner.inner Real
            (chartGramOp (I := I) S.family p
              (τ r, u.toFun r) (u.deriv r)) (v.deriv r))
          (timeMeasure L) := by
        refine (L2.integrable_inner
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv).congr ?_
        filter_upwards [timeOp_apply_ae
          (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
          hA C hC u.deriv] with r hr
        rw [hr]
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL.le]
      change _root_.MeasureTheory.Integrable
        (fun r ↦ _root_.Inner.inner Real
          (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
          (v.deriv r)) (volume.restrict (_root_.Set.Icc (0 : Real) L))
      simpa only [timeMeasure] using hMom
    have hWeak' := hWeak v hv0 hvL
    rw [intervalIntegral.integral_add hForcePairI hMomPairI] at hWeak'
    have hMomEq :
        _root_.Inner.inner Real
            (timeOp (fun r ↦ chartGramOp (I := I) S.family p
              (τ r, u.toFun r)) hA C hC u.deriv) v.deriv =
          ∫ r in (0 : Real)..L,
            _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (τ r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      rw [L2.inner_def, intervalIntegral.integral_of_le hL.le,
        ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
        hA C hC u.deriv] with r hr
      rw [hr]
    have hForceEq :
        (∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r)) =
          2 * ∫ r in (0 : Real)..L,
            inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
      calc
        (∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r)) =
            ∫ r in _root_.Set.Icc (0 : Real) L,
              2 * _root_.Inner.inner Real
                (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          apply _root_.MeasureTheory.integral_congr_ae
          have hForceAE' : lChartForce (I := I) S T a p u
              =ᵐ[volume.restrict (_root_.Set.Icc (0 : Real) L)]
                lChartForceRepresentative (I := I) S T a p u q := by
            simpa only [timeMeasure] using hForceAE
          filter_upwards [hForceAE'] with r hr
          change _root_.Inner.inner Real
            ((2 : Real) • lChartForceRepresentative (I := I) S T a p u q r)
              (v.toFun r) = _
          rw [← hr, real_inner_smul_left]
        _ = 2 * ∫ r in _root_.Set.Icc (0 : Real) L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [_root_.MeasureTheory.integral_const_mul]
        _ = 2 * ∫ r in (0 : Real)..L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [intervalIntegral.integral_of_le hL.le,
            _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hMomEq, hForceEq]
    linarith
  obtain ⟨c, hMomAE, hPc1, hPderiv⟩ := mom_rep_c1 hL
    (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
    hA C hC u F hF hEuler
  let P : Real → E := fun r ↦ c + ∫ s in (0 : Real)..r, F s
  let momQ : Real → E := fun r ↦ (2 : Real) •
    chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτregularity hr
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) := hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn
      (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) :=
    (chartGramOp_cont (I := I) hS.smoothMetric hJreg p hKchart).comp
      hpair fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hMomQcont : ContinuousOn momQ (_root_.Set.Icc (0 : Real) L) := by
    exact ((hAcont.clm_apply hq).const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hqIoo : u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc]
      using hqae
  have hPMomIoo : P =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] momQ := by
    filter_upwards [hMomAE, hqIoo] with r hrP hrq
    change c + ∫ s in (0 : Real)..r, F s =
      (2 : Real) •
        chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
    rw [← hrq]
    exact hrP.symm
  have hPMomIcc : P =ᵐ[volume.restrict (_root_.Set.Icc (0 : Real) L)] momQ := by
    simpa only [Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc] using hPMomIoo
  have hPeq : _root_.Set.EqOn P momQ (_root_.Set.Icc (0 : Real) L) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure Real) hL.ne hPMomIcc hPc1.continuousOn hMomQcont
  refine ⟨q, P, hq, hqae, huc1, huderiv, ?_, ?_, ?_⟩
  · simpa only [P] using hPc1
  · simpa only [momQ, τ] using hPeq
  · simpa only [P, F] using hPderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    {J : Set Real} (hJ : J ⊆ D.carrier)
    (htime : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ J)
    (hreg : ∀ r ∈ _root_.Set.Ioo (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hGramFd : ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hScalFd : ContinuousOn (fun z : Real × E => fderiv Real
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAction S T a p) (sameTimeEnds u) u) :
    ∃ q P : Real → E,
      ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) ∧
      ContDiffOn Real 1 P (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn P
        (fun r ↦ (2 : Real) •
          chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u.toFun r) (q r))
        (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin P (_root_.Set.Icc (0 : Real) L))
        (fun r ↦ (2 : Real) •
          lChartSpatialForceRepresentative (I := I) S T a p u q r)
        (_root_.Set.Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  have hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L) := by
    exact (continuous_const.sub
      ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier :=
    fun r hr => hJ (htime r hr)
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact interior_subset (hchart hr)
  have huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K := by
    intro r hr
    exact ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := exists_chartGramOp_ae_bound_of_carrier hS.smoothMetric p τ hτc hτcarrier
    hKc hKchart u huK
  obtain ⟨q, hq, hqae, huc1, huderiv⟩ :=
    lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives (I := I) S hS T a p hL u hJ htime hreg hGramFd hScalFd hchart hmin
  obtain ⟨hForce, hWeak⟩ :=
    lChartAction_weak_euler_lagrange_of_spatial_derivatives (I := I) S hS T a p hL u hJ htime hreg hGramFd hScalFd hchart hmin
  have hForceRep : ContinuousOn
      (lChartSpatialForceRepresentative (I := I) S T a p u q) (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_lChartSpatialForceRepresentative (I := I) S T a p u q htime hGramFd hScalFd hchart hq
  have hForceAE : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartSpatialForceRepresentative (I := I) S T a p u q :=
    lChartForce_ae_eq_lChartSpatialForceRepresentative (I := I) S hS T a p u q hreg hchart hqae
  let F : Real → E := fun r ↦
    (2 : Real) • lChartSpatialForceRepresentative (I := I) S T a p u q r
  have hF : ContinuousOn F (_root_.Set.Icc (0 : Real) L) := by
    exact (hForceRep.const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv +
        ∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r) = 0 := by
    intro v hv0 hvL
    have hvmeas : _root_.MeasureTheory.AEStronglyMeasurable v.toFun
        (volume.restrict (_root_.Set.Icc (0 : Real) L)) :=
      v.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
    obtain ⟨V, hV⟩ := IsCompact.exists_bound_of_continuousOn
      _root_.CompactIccSpace.isCompact_Icc v.continuousOn_toFun
    have hForcePair : _root_.MeasureTheory.IntegrableOn
        (fun r ↦ _root_.Inner.inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        (_root_.Set.Icc (0 : Real) L) volume := by
      refine Integrable.mono' (hForce.norm.const_mul V)
        (hForce.aestronglyMeasurable.inner hvmeas) ?_
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
      calc
        ‖inner Real (lChartForce (I := I) S T a p u r) (v.toFun r)‖
            ≤ ‖lChartForce (I := I) S T a p u r‖ * ‖v.toFun r‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖lChartForce (I := I) S T a p u r‖ * V :=
          mul_le_mul_of_nonneg_left (hV r hr) (norm_nonneg _)
        _ = V * ‖lChartForce (I := I) S T a p u r‖ := mul_comm _ _
    have hForcePairI : IntervalIntegrable
        (fun r ↦ _root_.Inner.inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        volume 0 L := by
      apply IntegrableOn.intervalIntegrable
      simpa only [_root_.Set.uIcc_of_le hL.le] using hForcePair
    have hMomPairI : IntervalIntegrable
        (fun r ↦ _root_.Inner.inner Real
          (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
          (v.deriv r)) _root_.MeasureTheory.MeasureSpace.volume 0 L := by
      have hMom : _root_.MeasureTheory.Integrable
          (fun r ↦ _root_.Inner.inner Real
            (chartGramOp (I := I) S.family p
              (τ r, u.toFun r) (u.deriv r)) (v.deriv r))
          (timeMeasure L) := by
        refine (L2.integrable_inner
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv).congr ?_
        filter_upwards [timeOp_apply_ae
          (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
          hA C hC u.deriv] with r hr
        rw [hr]
      apply IntegrableOn.intervalIntegrable
      simpa only [_root_.MeasureTheory.IntegrableOn, timeMeasure, _root_.Set.uIcc_of_le hL.le] using hMom
    have hWeak' := hWeak v hv0 hvL
    rw [intervalIntegral.integral_add hForcePairI hMomPairI] at hWeak'
    have hMomEq :
        _root_.Inner.inner Real
            (timeOp (fun r ↦ chartGramOp (I := I) S.family p
              (τ r, u.toFun r)) hA C hC u.deriv) v.deriv =
          ∫ r in (0 : Real)..L,
            _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (τ r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      rw [L2.inner_def, intervalIntegral.integral_of_le hL.le,
        ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
        hA C hC u.deriv] with r hr
      rw [hr]
    have hForceEq :
        (∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r)) =
          2 * ∫ r in (0 : Real)..L,
            inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
      calc
        (∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r)) =
            ∫ r in _root_.Set.Icc (0 : Real) L,
              2 * _root_.Inner.inner Real
                (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          apply _root_.MeasureTheory.integral_congr_ae
          have hForceAE' : lChartForce (I := I) S T a p u
              =ᵐ[volume.restrict (_root_.Set.Icc (0 : Real) L)]
                lChartSpatialForceRepresentative (I := I) S T a p u q := by
            simpa only [timeMeasure] using hForceAE
          filter_upwards [hForceAE'] with r hr
          change _root_.Inner.inner Real
            ((2 : Real) • lChartSpatialForceRepresentative (I := I) S T a p u q r)
              (v.toFun r) = _
          rw [← hr, real_inner_smul_left]
        _ = 2 * ∫ r in _root_.Set.Icc (0 : Real) L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [_root_.MeasureTheory.integral_const_mul]
        _ = 2 * ∫ r in (0 : Real)..L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [intervalIntegral.integral_of_le hL.le,
            _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hMomEq, hForceEq]
    linarith
  obtain ⟨c, hMomAE, hPc1, hPderiv⟩ := mom_rep_c1 hL
    (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
    hA C hC u F hF hEuler
  let P : Real → E := fun r ↦ c + ∫ s in (0 : Real)..r, F s
  let momQ : Real → E := fun r ↦ (2 : Real) •
    chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
  let Jtime : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJtime : Jtime ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hτcarrier hr
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) := hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn
      (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) :=
    (chartGramOp_continuousOn_of_carrier (I := I) hS.smoothMetric hJtime p hKchart).comp
      hpair fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hMomQcont : ContinuousOn momQ (_root_.Set.Icc (0 : Real) L) := by
    exact ((hAcont.clm_apply hq).const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hqIoo : u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc]
      using hqae
  have hPMomIoo : P =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] momQ := by
    filter_upwards [hMomAE, hqIoo] with r hrP hrq
    change c + ∫ s in (0 : Real)..r, F s =
      (2 : Real) •
        chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
    rw [← hrq]
    exact hrP.symm
  have hPMomIcc : P =ᵐ[volume.restrict (_root_.Set.Icc (0 : Real) L)] momQ := by
    simpa only [Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc] using hPMomIoo
  have hPeq : _root_.Set.EqOn P momQ (_root_.Set.Icc (0 : Real) L) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure Real) hL.ne hPMomIcc hPc1.continuousOn hMomQcont
  refine ⟨q, P, hq, hqae, huc1, huderiv, ?_, ?_, ?_⟩
  · simpa only [P] using hPc1
  · simpa only [momQ, τ] using hPeq
  · simpa only [P, F] using hPderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
