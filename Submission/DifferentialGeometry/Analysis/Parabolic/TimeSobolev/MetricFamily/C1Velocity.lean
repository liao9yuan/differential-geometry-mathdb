import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.C1Representative
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.C1Regularity
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.MetricFamily.Velocity
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Inverse

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

theorem exists_contDiffOn_one_velocity_representative_of_momentum {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (tau : Real → Real)
    (htau1 : ContDiffOn Real 1 tau (_root_.Set.Icc (0 : Real) L))
    (htaureg : _root_.Set.MapsTo tau (_root_.Set.Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (hu1 : ContDiffOn Real 1 u.toFun (_root_.Set.Icc (0 : Real) L))
    (p : Real → E)
    (hp : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (tau t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] p)
    (hp1 : ContDiffOn Real 1 p (_root_.Set.Icc (0 : Real) L)) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q := by
  let J : Set Real := tau '' _root_.Set.Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact htaureg hr
  have hpair1 : ContDiffOn Real 1 (fun t ↦ (tau t, u.toFun t))
      (_root_.Set.Icc (0 : Real) L) := htau1.prodMk hu1
  have hinv1 : ContDiffOn Real 1
      (fun t ↦ Ring.inverse
        (chartGramOp (I := I) G alpha (tau t, u.toFun t)))
      (_root_.Set.Icc (0 : Real) L) := by
    exact ((chartGramInv_smooth (I := I) hG hJreg alpha hKchart).of_le
      (by norm_num)).comp hpair1 fun t ht ↦
        ⟨⟨t, ht, rfl⟩, huK ht⟩
  let q : Real → E := fun t ↦ (1 / 2 : Real) •
    Ring.inverse (chartGramOp (I := I) G alpha (tau t, u.toFun t)) (p t)
  refine ⟨q, (hinv1.clm_apply hp1).const_smul _, ?_⟩
  filter_upwards [hp, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htime
  dsimp only [q]
  rw [← ht, ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit (I := I) hG hJreg alpha hKchart
    (tau t, u.toFun t) ⟨⟨t, ⟨htime.1.le, htime.2.le⟩, rfl⟩,
      huK ⟨htime.1.le, htime.2.le⟩⟩
  have hmul := congrArg (fun A : E →L[Real] E ↦ A (u.deriv t))
    (Ring.inverse_mul_cancel _ hunit)
  have hhalf : (1 / 2 : Real) * 2 = 1 := by norm_num
  rw [hhalf, one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self]
    using hmul.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_momentum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_momentum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_momentum ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_momentum

theorem exists_contDiffOn_one_velocity_representative_of_weak_euler {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (tau : Real → Real)
    (htau1 : ContDiffOn Real 1 tau (_root_.Set.Icc (0 : Real) L))
    (htaureg : _root_.Set.MapsTo tau (_root_.Set.Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (tau t, u.toFun t))
        (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (tau t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : ContinuousOn F (_root_.Set.Icc (0 : Real) L))
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun t ↦ chartGramOp (I := I) G alpha
            (tau t, u.toFun t)) hA C hC u.deriv) v.deriv +
        ∫ t in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) := by
  obtain ⟨c, hmom, hp1, _⟩ := mom_rep_c1 hL
    (fun t ↦ chartGramOp (I := I) G alpha (tau t, u.toFun t))
    hA C hC u F hF hEuler
  let p : Real → E := fun t ↦ c + ∫ r in (0 : Real)..t, F r
  have hmom' : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (tau t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] p := by
    simpa only [p] using hmom
  have hp1' : ContDiffOn Real 1 p (_root_.Set.Icc (0 : Real) L) := by
    simpa only [p] using hp1
  obtain ⟨q0, hq0cont, hq0ae⟩ := exists_continuous_velocity_representative_of_momentum hG alpha tau
    htau1.continuousOn htaureg hKchart u huK p hmom' hp1'.continuousOn
  have hq0time : u.deriv =ᵐ[timeMeasure L] q0 := by
    simpa only [timeMeasure, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc]
      using hq0ae
  obtain ⟨hu1, _⟩ := toFun_c1_of_rep hL u q0 hq0cont hq0time
  obtain ⟨q, hq1, hqae⟩ := exists_contDiffOn_one_velocity_representative_of_momentum hG alpha tau htau1
    htaureg hKchart u huK hu1 p hmom' hp1'
  have hqtime : u.deriv =ᵐ[timeMeasure L] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc]
      using hqae
  obtain ⟨_, hderiv⟩ := toFun_c1_of_rep hL u q hq1.continuousOn hqtime
  exact ⟨q, hq1, hqae, hderiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_weak_euler then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_weak_euler"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_weak_euler ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_contDiffOn_one_velocity_representative_of_weak_euler

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
