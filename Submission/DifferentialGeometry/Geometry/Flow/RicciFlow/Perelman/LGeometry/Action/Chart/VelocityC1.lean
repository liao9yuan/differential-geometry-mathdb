import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.ForceRegularity
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.MetricFamily.C1Velocity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.MomentumRegularity
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Interval _root_.Manifold _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartAction_minimizer_velocity_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (q0 : Real → E) (hq0 : ContinuousOn q0 (_root_.Set.Icc (0 : Real) L))
    (hq0ae : u.deriv =ᵐ[timeMeasure L] q0)
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
          _root_.Inner.inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            (v.deriv r)) = 0) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (_root_.Set.Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) L)] q ∧
      _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : Real) L)) q
        (_root_.Set.Icc (0 : Real) L) := by
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  have htau1 : ContDiffOn Real 1 tau (_root_.Set.Icc (0 : Real) L) := by
    exact (contDiff_const.sub ((contDiff_const.add contDiff_id).pow 2)).contDiffOn
  have htaureg : _root_.Set.MapsTo tau (_root_.Set.Icc (0 : Real) L) D.regular := hreg
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have huK : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L) K :=
    fun r hr ↦ ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := exists_chartGramOp_ae_bound hS.smoothMetric p tau
    htau1.continuousOn htaureg hKc hKchart u huK
  let F0 : Real → E := lChartForceRepresentative (I := I) S T a p u q0
  let F : Real → E := fun r ↦ (2 : Real) • F0 r
  have hF0 : ContinuousOn F0 (_root_.Set.Icc (0 : Real) L) := by
    simpa only [F0] using
      continuousOn_lChartForceRepresentative (I := I) S hS T a p u q0 hreg hchart hq0
  have hF : ContinuousOn F (_root_.Set.Icc (0 : Real) L) :=
    hF0.const_smul (2 : Real)
  have hraw : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L] F0 := by
    simpa only [F0] using
      lChartForce_ae_eq_lChartForceRepresentative (I := I) S hS T a p u q0 hreg hchart hq0ae
  have hEuler' : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * _root_.Inner.inner Real
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (tau r, u.toFun r)) hA C hC u.deriv) v.deriv +
        ∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r) = 0 := by
    intro v hv0 hvL
    have he := hEuler v hv0 hvL
    have hmom : _root_.Inner.inner Real
        (timeOp (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv) v.deriv =
        ∫ r in _root_.Set.Icc (0 : Real) L,
          _root_.Inner.inner Real
            (chartGramOp (I := I) S.family p
              (tau r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      rw [L2.inner_def]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv] with r hr
      rw [hr]
    have hkin : _root_.MeasureTheory.IntegrableOn
        (fun r ↦ _root_.Inner.inner Real
          (chartGramOp (I := I) S.family p
            (tau r, u.toFun r) (u.deriv r)) (v.deriv r))
        (_root_.Set.Icc (0 : Real) L) volume := by
      change _root_.MeasureTheory.Integrable
        (fun r ↦ _root_.Inner.inner Real
          (chartGramOp (I := I) S.family p
            (tau r, u.toFun r) (u.deriv r)) (v.deriv r))
        (timeMeasure L)
      refine (L2.integrable_inner
        (timeOp (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv) v.deriv).congr ?_
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv] with r hr
      rw [hr]
    have hforce : _root_.MeasureTheory.IntegrableOn
        (fun r ↦ _root_.Inner.inner Real (F0 r) (v.toFun r))
        (_root_.Set.Icc (0 : Real) L) volume :=
      (hF0.inner v.continuousOn_toFun).integrableOn_compact _root_.CompactIccSpace.isCompact_Icc
    have hFscale :
        (∫ r in _root_.Set.Icc (0 : Real) L, _root_.Inner.inner Real (F r) (v.toFun r)) =
          2 * ∫ r in _root_.Set.Icc (0 : Real) L,
            inner Real (F0 r) (v.toFun r) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with r
      simp only [F, real_inner_smul_left]
    have hsum :
        (∫ r in _root_.Set.Icc (0 : Real) L,
          _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r) +
            _root_.Inner.inner Real (F0 r) (v.toFun r)) =
          ∫ r in _root_.Set.Icc (0 : Real) L,
            inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
              _root_.Inner.inner Real
                (chartGramOp (I := I) S.family p
                  (tau r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hraw] with r hr
      rw [hr]
      ring
    have he' :
        (∫ r in _root_.Set.Icc (0 : Real) L,
          inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) = 0 := by
      simpa only [tau, intervalIntegral.integral_of_le hL.le,
        ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc] using he
    rw [hmom, hFscale]
    calc
      2 * (∫ r in _root_.Set.Icc (0 : Real) L,
          _root_.Inner.inner Real
            (chartGramOp (I := I) S.family p
              (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) +
          2 * ∫ r in _root_.Set.Icc (0 : Real) L,
            _root_.Inner.inner Real (F0 r) (v.toFun r) =
          2 * ((∫ r in _root_.Set.Icc (0 : Real) L,
            _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) +
              ∫ r in _root_.Set.Icc (0 : Real) L,
                inner Real (F0 r) (v.toFun r)) := by ring
      _ = 2 * ∫ r in _root_.Set.Icc (0 : Real) L,
          (_root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r) +
            inner Real (F0 r) (v.toFun r)) := by
          rw [MeasureTheory.integral_add hkin hforce]
      _ = 2 * ∫ r in _root_.Set.Icc (0 : Real) L,
          (_root_.Inner.inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            _root_.Inner.inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) := by
          rw [hsum]
      _ = 0 := by rw [he', _root_.MulZeroClass.mul_zero]
  exact exists_contDiffOn_one_velocity_representative_of_weak_euler hS.smoothMetric p hL tau htau1 htaureg
    hKchart u huK hA C hC F hF hEuler'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_velocity_contDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_velocity_contDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_velocity_contDiffOn_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_velocity_contDiffOn_one

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives
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
    ContDiffOn Real 2 u.toFun (_root_.Set.Ioo (0 : Real) L) := by
  obtain ⟨q, P, _, _, hu1, huder, hP1, hPeq, _⟩ :=
    lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives S hS T a p hL u
      hJ htime hreg hGramFd hScalFd hchart hmin
  have htau : ContDiffOn Real 1 (fun r : Real => T - (a + r) ^ 2)
      (_root_.Set.Ioo (0 : Real) L) :=
    (contDiff_const.sub ((contDiff_const.add contDiff_id).pow 2)).contDiffOn
  have hq1 : ContDiffOn Real 1 q (_root_.Set.Ioo (0 : Real) L) := by
    exact contDiffOn_chart_velocity_of_momentum hS.smoothMetric p
      (fun r : Real => T - (a + r) ^ 2) u.toFun q P htau (hu1.mono _root_.Set.Ioo_subset_Icc_self) (hP1.mono _root_.Set.Ioo_subset_Icc_self) hreg
      (fun r hr => hchart ⟨hr.1.le, hr.2.le⟩)
      (fun r hr => hPeq ⟨hr.1.le, hr.2.le⟩)
  have hderiv : ContDiffOn Real 1 (deriv u.toFun) (_root_.Set.Ioo (0 : Real) L) := by
    apply hq1.congr
    intro r hr
    have hIcc : _root_.Set.Icc (0 : Real) L ∈ nhds r :=
      _root_.Filter.mem_of_superset (Ioo_mem_nhds hr.1 hr.2) _root_.Set.Ioo_subset_Icc_self
    rw [← derivWithin_of_mem_nhds hIcc]
    exact huder ⟨hr.1.le, hr.2.le⟩
  change ContDiffOn Real ((1 : ℕ∞ω) + 1) u.toFun (_root_.Set.Ioo (0 : Real) L)
  exact (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
    ⟨(hu1.mono _root_.Set.Ioo_subset_Icc_self).differentiableOn (by norm_num), by simp, hderiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

end
