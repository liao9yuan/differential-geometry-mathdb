import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}
  (Φ : PointedCGHMaps X P subseq)

theorem FlowMetricConvergenceData.metric_hasDerivAt
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b : ℝ} (hwin : _root_.Set.Icc a b ⊆ X.D.regular)
    (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo a b) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ v w : TangentSpace I x,
      HasDerivAt (fun s : ℝ => (co.gInf s).inner x v w)
        (-2 * ricciTensor (I := I) (co.gInf t) x v w) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  intro v w
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hbasis (i j : Fin (Module.finrank Real E)) :
      HasDerivAt
        (fun s => chartGramOnE (I := I) (co.gInf s) x i j (extChartAt I x x))
        (-2 * chartRicciTensor (I := I) (co.gInf t) x i j (extChartAt I x x)) t := by
    have hpde := (FlowMetricConvergenceData.gramPDE (I := I) (Φ := Φ)
      hwin co x i j (Set.Ioo_subset_Icc_self ht) hy).hasDerivAt
        (Icc_mem_nhds_iff.mpr ht)
    let gt : SmoothRiemannianMetric I P.M := co.gInf t
    have hStatic : ContDiffOn Real ∞ (chartGramPi (I := I) gt x)
        (interior (extChartAt I x).target) := by
      refine contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => ?_
      exact (chartGramOnE_contDiffOn (I := I) gt x a b).mono interior_subset
    have hAt : ContDiffAt Real ∞ (chartGramPi (I := I) gt x) (extChartAt I x x) :=
      hStatic.contDiffAt (isOpen_interior.mem_nhds hy)
    have hG : DifferentiableAt Real (chartGramPi (I := I) gt x) (extChartAt I x x) :=
      hAt.differentiableAt (by simp)
    have hG1 : ∀ᶠ z in nhds (extChartAt I x x),
        DifferentiableAt Real (chartGramPi (I := I) gt x) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact (hStatic.contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt
        (by simp)
    have hG2 : DifferentiableAt Real
        (fun z => fderiv Real (chartGramPi (I := I) gt x) z) (extChartAt I x x) :=
      (hAt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
    have hjet := jetRicciFlow_chartGram (I := I) gt x hy hG hG1 hG2 i j
    simpa only [gt] using hpde.congr_deriv hjet
  exact metricPDE_of_gram (I := I) co.gInf x hbasis v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.metric_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.metric_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.metric_hasDerivAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.metric_hasDerivAt

theorem HalfLineMetricConvergenceData.metric_hasDerivAt
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular) {t : ℝ} (ht : t < 0) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ v w : TangentSpace I x,
      HasDerivAt (fun s : ℝ => (co.gInf s).inner x v w)
        (-2 * ricciTensor (I := I) (co.gInf t) x v w) t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-t)
  have hleft : -(n : ℝ) < t := by linarith
  have hmid : t < t / 2 := by linarith
  have hhalf : t / 2 < 0 := by linarith
  have hwin : _root_.Set.Icc (-(n : ℝ)) (t / 2) ⊆ X.D.regular :=
    fun s hs => hreg (lt_of_le_of_lt hs.2 hhalf)
  have hsub : _root_.Set.Icc (-(n : ℝ)) (t / 2) ⊆ _root_.Set.Icc (-(n : ℝ)) 0 :=
    fun s hs => ⟨hs.1, (hs.2.trans_lt hhalf).le⟩
  exact FlowMetricConvergenceData.metric_hasDerivAt Φ hwin
    (FlowMetricConvergenceData.restrict (Φ := Φ)
      (HalfLineMetricConvergenceData.atWindow Φ co n) hsub) ⟨hleft, hmid⟩ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_hasDerivAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_hasDerivAt

end DifferentialGeometry.CheegerGromovCompactness
