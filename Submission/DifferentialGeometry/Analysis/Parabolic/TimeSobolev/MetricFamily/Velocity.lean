import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Regularity
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.L1Regularity
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Inverse
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.C1Representative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Interval

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem exists_chartGramOp_ae_bound {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτregularity : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K) :
    ∃ (C : NNReal)
      (_ : _root_.MeasureTheory.AEStronglyMeasurable
        (fun r ↦ chartGramOp (I := I) G alpha (τ r, u.toFun r)) (timeMeasure L)),
      ∀ᵐ r ∂timeMeasure L,
        ‖chartGramOp (I := I) G alpha (τ r, u.toFun r)‖ ≤ (C : Real) := by
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτregularity hr
  let A : Real → E →L[Real] E := fun r ↦
    chartGramOp (I := I) G alpha (τ r, u.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r)) (_root_.Set.Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn A (_root_.Set.Icc (0 : Real) L) := by
    exact (chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hC⟩ := chartGramOp_bound (I := I) hG hJreg hJc alpha hKchart hKc
  refine ⟨C, hA, ?_⟩
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
  exact hC (τ r, u.toFun r) ⟨⟨r, hr, rfl⟩, huK hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound

theorem exists_continuous_velocity_representative_of_momentum {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτregularity : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (p : Real → E)
    (hp : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (τ t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] p)
    (hpcont : ContinuousOn p (_root_.Set.Icc (0 : Real) L)) :
    ∃ q : Real → E, ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτregularity hr
  have hpair : ContinuousOn (fun t ↦ (τ t, u.toFun t)) (_root_.Set.Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hinv : ContinuousOn
      (fun t ↦ Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)))
      (_root_.Set.Icc (0 : Real) L) := by
    exact (chartGramInv_cont (I := I) hG hJreg alpha hKchart).comp hpair
      fun t ht ↦ ⟨⟨t, ht, rfl⟩, huK ht⟩
  let q : Real → E := fun t ↦ (1 / 2 : Real) •
    Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)) (p t)
  refine ⟨q, (hinv.clm_apply hpcont).const_smul _, ?_⟩
  filter_upwards [hp, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htime
  dsimp only [q]
  rw [← ht]
  rw [ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit (I := I) hG hJreg alpha hKchart
    (τ t, u.toFun t) ⟨⟨t, ⟨htime.1.le, htime.2.le⟩, rfl⟩,
      huK ⟨htime.1.le, htime.2.le⟩⟩
  have hmul := congrArg (fun A : E →L[Real] E ↦ A (u.deriv t))
    (Ring.inverse_mul_cancel _ hunit)
  have hhalf : (1 / 2 : Real) * 2 = 1 := by norm_num
  rw [hhalf, one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using hmul.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum

theorem exists_continuous_velocity_representative_of_weak_euler {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτregularity : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (τ t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : Real) L) _root_.MeasureTheory.MeasureSpace.volume)
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t))
            hA C hC u.deriv) v.deriv +
        ∫ t in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E, ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
  obtain ⟨c, hmom, hcont⟩ := mom_rep_cont_l1 hL
    (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) hA C hC u F hF hEuler
  exact exists_continuous_velocity_representative_of_momentum hG alpha τ hτc hτregularity hKchart u huK
    (fun t ↦ c + ∫ r in (0 : Real)..t, F r) hmom hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Interval

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem exists_chartGramOp_ae_bound_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K) :
    ∃ (C : NNReal)
      (_ : _root_.MeasureTheory.AEStronglyMeasurable
        (fun r ↦ chartGramOp (I := I) G alpha (τ r, u.toFun r)) (timeMeasure L)),
      ∀ᵐ r ∂timeMeasure L,
        ‖chartGramOp (I := I) G alpha (τ r, u.toFun r)‖ ≤ (C : Real) := by
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hτcarrier hr
  let A : Real → E →L[Real] E := fun r ↦
    chartGramOp (I := I) G alpha (τ r, u.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r)) (_root_.Set.Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn A (_root_.Set.Icc (0 : Real) L) := by
    exact (chartGramOp_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hC⟩ := chartGramOp_bound_of_carrier (I := I) hG hJreg hJc alpha hKchart hKc
  refine ⟨C, hA, ?_⟩
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
  exact hC (τ r, u.toFun r) ⟨⟨r, hr, rfl⟩, huK hr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound_of_carrier ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_chartGramOp_ae_bound_of_carrier

theorem exists_continuous_velocity_representative_of_momentum_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (p : Real → E)
    (hp : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (τ t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] p)
    (hpcont : ContinuousOn p (_root_.Set.Icc (0 : Real) L)) :
    ∃ q : Real → E, ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
  let J : Set Real := τ '' _root_.Set.Icc (0 : Real) L
  have hJreg : J ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hτcarrier hr
  have hpair : ContinuousOn (fun t ↦ (τ t, u.toFun t)) (_root_.Set.Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hinv : ContinuousOn
      (fun t ↦ Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)))
      (_root_.Set.Icc (0 : Real) L) := by
    exact (chartGramInv_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart).comp hpair
      fun t ht ↦ ⟨⟨t, ht, rfl⟩, huK ht⟩
  let q : Real → E := fun t ↦ (1 / 2 : Real) •
    Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)) (p t)
  refine ⟨q, (hinv.clm_apply hpcont).const_smul _, ?_⟩
  filter_upwards [hp, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htime
  dsimp only [q]
  rw [← ht]
  rw [ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit_of_carrier (I := I) hG hJreg alpha hKchart
    (τ t, u.toFun t) ⟨⟨t, ⟨htime.1.le, htime.2.le⟩, rfl⟩,
      huK ⟨htime.1.le, htime.2.le⟩⟩
  have hmul := congrArg (fun A : E →L[Real] E ↦ A (u.deriv t))
    (Ring.inverse_mul_cancel _ hunit)
  have hhalf : (1 / 2 : Real) * 2 = 1 := by norm_num
  rw [hhalf, one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using hmul.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum_of_carrier ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_momentum_of_carrier

theorem exists_continuous_velocity_representative_of_weak_euler_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (τ t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : Real) L) _root_.MeasureTheory.MeasureSpace.volume)
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t))
            hA C hC u.deriv) v.deriv +
        ∫ t in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E, ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
  obtain ⟨c, hmom, hcont⟩ := mom_rep_cont_l1 hL
    (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) hA C hC u F hF hEuler
  exact exists_continuous_velocity_representative_of_momentum_of_carrier hG alpha τ hτc hτcarrier hKchart u huK
    (fun t ↦ c + ∫ r in (0 : Real)..t, F r) hmom hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler_of_carrier ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_continuous_velocity_representative_of_weak_euler_of_carrier

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Interval
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

theorem exists_contDiffOn_one_of_weak_euler_of_carrier
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (τ : Real → Real)
    (hτc : ContinuousOn τ (_root_.Set.Icc (0 : Real) L))
    (hτcarrier : _root_.Set.MapsTo τ (_root_.Set.Icc (0 : Real) L) D.carrier)
    {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (τ t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : Real) L) _root_.MeasureTheory.MeasureSpace.volume)
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real (timeOp (fun t ↦ chartGramOp (I := I) G alpha
        (τ t, u.toFun t)) hA C hC u.deriv) v.deriv +
        ∫ t in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E, ContinuousOn q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L) ∧
      EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q (_root_.Set.Icc (0 : Real) L) := by
  obtain ⟨q, hq, hqae⟩ := exists_continuous_velocity_representative_of_weak_euler_of_carrier
    hG alpha hL τ hτc hτcarrier hKchart u huK hA C hC F hF hEuler
  have hqtime : u.deriv =ᵐ[timeMeasure L] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc] using hqae
  obtain ⟨hc1, hderiv⟩ := toFun_c1_of_rep hL u q hq hqtime
  exact ⟨q, hq, hqtime, hc1, hderiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_of_weak_euler_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_of_weak_euler_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_of_weak_euler_of_carrier ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_of_weak_euler_of_carrier

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
end
