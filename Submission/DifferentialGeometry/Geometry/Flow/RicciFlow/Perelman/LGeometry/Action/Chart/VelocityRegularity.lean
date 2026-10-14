import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.C1Representative
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.MetricFamily.Velocity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.FirstVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.SpatialFirstVariation

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

theorem lChartAction_minimizer_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAction S T a p) (sameTimeEnds u) u) :
    ∃ q : Real → E,
      ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  have hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L) := by
    exact (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτregularity : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.regular := by
    exact hreg
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
  obtain ⟨hForce, hWeak⟩ :=
    lChartAction_weak_euler_lagrange_of_isLocalMinOn (I := I) S hS T a p hL u hreg hchart hmin
  let F : Real → E := fun r ↦ (2 : Real) • lChartForce (I := I) S T a p u r
  have hF : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : Real) L) volume := by
    change _root_.MeasureTheory.Integrable F (volume.restrict (_root_.Set.Icc (0 : Real) L))
    exact (Integrable.smul (2 : Real) hForce).congr
      (Eventually.of_forall fun _ ↦ rfl)
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
            (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
            (v.deriv r)) (timeMeasure L) := by
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
      rw [_root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hL.le,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      simp only [F, real_inner_smul_left]
    rw [hMomEq, hForceEq]
    linarith
  obtain ⟨q, hq, hqae⟩ := exists_continuous_velocity_representative_of_weak_euler hS.smoothMetric p hL τ
    hτc hτregularity hKchart u huK hA C hC F hF hEuler
  have hqtime : u.deriv =ᵐ[timeMeasure L] q := by
    have hae : _root_.MeasureTheory.ae (volume.restrict (_root_.Set.Ioo (0 : Real) L)) =
        ae (timeMeasure L) := by
      congr 1
      unfold timeMeasure
      exact _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc
    rw [← hae]
    exact hqae
  obtain ⟨hc1, hderiv⟩ := toFun_c1_of_rep hL u q hq hqtime
  exact ⟨q, hq, hqtime, hc1, hderiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one

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

theorem lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives
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
    ∃ q : Real → E,
      ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L) ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  have hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L) := by
    exact (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier := by
    intro r hr
    exact hJ (htime r hr)
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
  obtain ⟨hForce, hWeak⟩ :=
    lChartAction_weak_euler_lagrange_of_spatial_derivatives (I := I) S hS T a p hL u hJ htime hreg hGramFd hScalFd hchart hmin
  let F : Real → E := fun r ↦ (2 : Real) • lChartForce (I := I) S T a p u r
  have hF : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : Real) L) volume := by
    change _root_.MeasureTheory.Integrable F (volume.restrict (_root_.Set.Icc (0 : Real) L))
    exact (Integrable.smul (2 : Real) hForce).congr
      (Eventually.of_forall fun _ ↦ rfl)
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
            (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
            (v.deriv r)) (timeMeasure L) := by
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
      rw [_root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hL.le,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      simp only [F, real_inner_smul_left]
    rw [hMomEq, hForceEq]
    linarith
  exact exists_contDiffOn_one_of_weak_euler_of_carrier hS.smoothMetric p hL τ
    hτc hτcarrier hKchart u huK hA C hC F hF hEuler

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
