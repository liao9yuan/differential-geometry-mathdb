import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Sobolev
import Submission.DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.Partition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (alpha : ℝ → M)
    (hAC : let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace;
      AbsolutelyContinuousOnInterval alpha a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i, _root_.Set.MapsTo alpha (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, _root_.Set.EqOn (u i).toFun (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r)))
        (_root_.Set.Icc 0 (partitionIntervalLength t i))) ∧
      ∀ i, (u i).deriv =ᵐ[timeMeasure (partitionIntervalLength t i)]
        deriv (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r))) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hc : ContinuousOn alpha (_root_.Set.Icc a b) :=
    (uniformContinuousOn_of_absolutelyContinuousOnInterval hAC).continuousOn.mono _root_.Set.Icc_subset_uIcc
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ := Geometry.exists_chart_subdivision (H := H) hab hc
  let t : Fin (m + 1) → ℝ := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := congrArg Subtype.val (hqm m le_rfl)
  choose p hp using fun i : Fin m ↦ hpieces i
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := htmono Fin.castSucc_lt_succ.le
  have hsub (i : Fin m) : _root_.Set.Icc (t i.castSucc) (t i.succ) ⊆ _root_.Set.Icc a b := by
    intro s hs
    exact ⟨(q i.castSucc).property.1.trans hs.1, hs.2.trans (q i.succ).property.2⟩
  have hsrc (i : Fin m) : _root_.Set.MapsTo alpha
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    simpa only [t, Fin.val_castSucc, Fin.val_succ] using hp i
  have hACi (i : Fin m) : AbsolutelyContinuousOnInterval alpha (t i.castSucc) (t i.succ) :=
    hAC.mono (by simpa only [_root_.Set.uIcc_of_le (hseg i), _root_.Set.uIcc_of_le hab] using hsub i)
  choose u hu using fun i : Fin m ↦
    exists_timeH1_extChartAt_of_intervalIntegrable_lRegularizedLagrangian
      S hMet hSc T (t i.castSucc) (t i.succ) (hseg i) alpha (p i) (hACi i) (hsrc i)
      (hLag.mono_set (by simpa only [_root_.Set.uIcc_of_le (hseg i), _root_.Set.uIcc_of_le hab] using hsub i))
      (fun s hs ↦ hreg s (hsub i hs))
  exact ⟨m, t, p, u, ht0, htmono, htlast, hsrc, fun i ↦ (hu i).1, fun i ↦ (hu i).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_intervalIntegrable_lRegularizedLagrangian

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (alpha : ℝ → M)
    (hAC : Manifold.absolutelyContinuousOnInterval I alpha a b)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (p : Fin m → M)
      (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      t 0 = a ∧ Monotone t ∧ t (Fin.last m) = b ∧
      (∀ i, _root_.Set.MapsTo alpha (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, _root_.Set.EqOn (u i).toFun (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r)))
        (_root_.Set.Icc 0 (partitionIntervalLength t i))) ∧
      ∀ i, (u i).deriv =ᵐ[timeMeasure (partitionIntervalLength t i)]
        deriv (fun r ↦ extChartAt I (p i) (alpha (t i.castSucc + r))) := by
  have hc : ContinuousOn alpha (_root_.Set.Icc a b) :=
    hAC.1.mono _root_.Set.Icc_subset_uIcc
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ := Geometry.exists_chart_subdivision (H := H) hab hc
  let t : Fin (m + 1) → ℝ := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := congrArg Subtype.val (hqm m le_rfl)
  choose p hp using fun i : Fin m ↦ hpieces i
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := htmono Fin.castSucc_lt_succ.le
  have hsub (i : Fin m) : _root_.Set.Icc (t i.castSucc) (t i.succ) ⊆ _root_.Set.Icc a b := by
    intro s hs
    exact ⟨(q i.castSucc).property.1.trans hs.1, hs.2.trans (q i.succ).property.2⟩
  have hsrc (i : Fin m) : _root_.Set.MapsTo alpha
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    simpa only [t, Fin.val_castSucc, Fin.val_succ] using hp i
  have hACi (i : Fin m) : Manifold.absolutelyContinuousOnInterval I alpha (t i.castSucc) (t i.succ) :=
    Manifold.absolutelyContinuousOnInterval_mono hAC (by simpa only [_root_.Set.uIcc_of_le (hseg i), _root_.Set.uIcc_of_le hab] using hsub i)
  choose u hu using fun i : Fin m ↦
    exists_timeH1_extChartAt_of_absolutelyContinuousOnInterval
      S hMet hSc T (t i.castSucc) (t i.succ) (hseg i) alpha (p i) (hACi i) (hsrc i)
      (hLag.mono_set (by simpa only [_root_.Set.uIcc_of_le (hseg i), _root_.Set.uIcc_of_le hab] using hsub i))
      (fun s hs ↦ hreg s (hsub i hs))
  exact ⟨m, t, p, u, ht0, htmono, htlast, hsrc, fun i ↦ (hu i).1, fun i ↦ (hu i).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval

end DifferentialGeometry.PDE.RicciFlow.Perelman
