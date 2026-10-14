import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierKineticEnergy
import Submission.DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type u} [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (p : M) (gamma : Real → M)
    (u : timeH1 E (b - a))
    (hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun (fun r ↦ extChartAt I p (gamma (a + r)))
      (_root_.Set.Icc (0 : Real) (b - a)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hkin := intervalIntegrable_lKinetic_of_chartH1_of_carrier
    S hMet T gamma p a b hab u hsrc hrep hreg
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs)
  have hcont : ContinuousOn gamma (_root_.Set.uIcc a b) := by
    rw [_root_.Set.uIcc_of_le hab]
    exact curve_cont_local I p gamma u hab hsrc hrep
  have hpot := lScalar_int (I := I) S hSc T a b gamma hcarrier hcont
  exact hkin.add hpot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier

theorem intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hLag (i : Fin m) : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume
      (t i.castSucc) (t i.succ) := by
    apply intervalIntegrable_lRegularizedLagrangian_of_chartH1_of_carrier S hMet hSc T
      (t i.castSucc) (t i.succ) (htmono Fin.castSucc_lt_succ.le)
      (p i) gamma (u i) (hsrc i) (hrep i)
    intro s hs
    apply hreg s
    constructor
    · rw [← ht0]
      exact (htmono (Fin.zero_le _)).trans hs.1
    · rw [← htlast]
      exact hs.2.trans (htmono (Fin.le_last _))
  have hprefix (i : Fin (m + 1)) : IntervalIntegrable
      (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume (t 0) (t i) := by
    induction i using Fin.induction with
    | zero => exact IntervalIntegrable.refl
    | succ i ih => exact ih.trans (hLag i)
  simpa only [ht0, htlast] using hprefix (Fin.last m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_chartH1_partition_of_carrier

theorem intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b := by
  classical
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hchart⟩ :=
    DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hab halpha.continuousOn
  have hseg (n : Nat) : (t n : Real) ≤ t (n + 1) :=
    htmono (Nat.le_succ n)
  have hkinPiece (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume (t n) (t (n + 1)) := by
    obtain ⟨p, hsrc⟩ := hchart n
    have hshift : _root_.Set.MapsTo (fun r : Real ↦ (t n : Real) + r)
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) (_root_.Set.Icc a b) := by
      intro r hr
      exact ⟨by linarith [(t n).property.1, hr.1],
        by linarith [hr.2, (t (n + 1)).property.2]⟩
    have hshiftPiece : _root_.Set.MapsTo (fun r : Real ↦ (t n : Real) + r)
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (_root_.Set.Icc (t n : Real) (t (n + 1) : Real)) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hlocalMD : ContMDiffOn (modelWithCornersSelf Real Real) I 1
        (fun r : Real ↦ alpha ((t n : Real) + r))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) :=
      halpha.comp (contMDiff_const.add contMDiff_id).contMDiffOn hshift
    have hlocalSource : _root_.Set.MapsTo (fun r : Real ↦ alpha ((t n : Real) + r))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (chartAt H p).source :=
      hsrc.comp hshiftPiece
    let us : timeH1 E ((t (n + 1) : Real) - t n) :=
      chartTimeH1 I (sub_nonneg.mpr (hseg n)) p
        (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSource
    have hrep : _root_.Set.EqOn us.toFun
        (fun r ↦ extChartAt I p (alpha ((t n : Real) + r)))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) := by
      with_unfolding_all
        exact chartTimeH1_toFun I (sub_nonneg.mpr (hseg n)) p
          (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSource
    exact intervalIntegrable_lKinetic_of_chartH1_of_carrier S hMet T alpha p (t n) (t (n + 1))
      (hseg n) us hsrc hrep fun s hs ↦
        hreg s ⟨(t n).property.1.trans hs.1,
          hs.2.trans (t (n + 1)).property.2⟩
  have hkin : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
    have ht0' : (t 0 : Real) = a := by
      simpa only using congrArg Subtype.val ht0
    have htm' : (t m : Real) = b := by
      simpa only using congrArg Subtype.val (hm m le_rfl)
    have hchain := IntervalIntegrable.trans_iterate
      (n := m) fun k _hk ↦ hkinPiece k
    simpa only [ht0', htm'] using hchain
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs)
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [_root_.Set.uIcc_of_le hab] using halpha.continuousOn)
  with_unfolding_all exact hkin.add hpot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier


end DifferentialGeometry.PDE.RicciFlow.Perelman
