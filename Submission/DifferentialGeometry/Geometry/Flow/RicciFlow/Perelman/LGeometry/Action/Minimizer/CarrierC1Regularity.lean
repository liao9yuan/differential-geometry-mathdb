import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.Sobolev
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Regularity.CarrierC1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.StrictRefinement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lMinCurve_c1_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b) (p : Fin m → M)
    (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma (_root_.Set.Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (U : Set Real) (hU : U ⊆ D.carrier)
    (htime : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ U)
    (hreg : ∀ s ∈ _root_.Set.Ioo a b, T - s ^ 2 ∈ D.regular)
    (hGramFd : ∀ p : M, ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hScalFd : ∀ p : M, ContinuousOn (fun z : Real × E => fderiv Real
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (_root_.Set.Icc a b) := by
  classical
  obtain ⟨k, s, _q, p', u', hs, _hq, hs0, hslast, _hseg, _hp,
      hsrc', hrep'⟩ := exists_strict_chart_partition (I := I) t htmono p u gamma hsrc hrep
  have hs0a : s 0 = a := hs0.trans ht0
  have hslastb : s (Fin.last k) = b := hslast.trans htlast
  have hk : 0 < k := by
    cases k with
    | zero =>
        exfalso
        apply hab.ne
        exact hs0a.symm.trans ((congrArg s (Fin.ext (by simp))).trans hslastb)
    | succ k => omega
  have hpos : ∀ i : Fin k, s i.castSucc < s i.succ := by
    intro i
    exact hs Fin.castSucc_lt_succ
  exact lRegularizedAction_minimizer_contMDiffOn_one_of_chart_partition_of_spatial_derivatives (I := I) S hS T a b hk s hs0a hslastb p' gamma
    hgamma u' hpos hsrc' hrep' U hU htime hreg (fun i => hGramFd (p' i)) (fun i => hScalFd (p' i)) hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace.PseudoMetrizableSpace M] {D : RealTimeInterval}

theorem lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a < b) (gamma : ℝ → M)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ _root_.Set.Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ _root_.Set.Ioo a b, T - r ^ 2 ∈ D.regular)
    (hGramFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hScalFd : ∀ p : M, ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (U ×ˢ interior (extChartAt I p).target))
    (hmin : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b) := by
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  let f : C(_root_.Set.Icc a b, M) :=
    ⟨fun r => gamma r.val, (hgamma.1.mono _root_.Set.Icc_subset_uIcc).domRestrict⟩
  let eta : ℝ → M := _root_.Set.IccExtend hab.le f
  have heta : Continuous eta := (continuous_IccExtend_iff (h := hab.le)).mpr f.continuous
  have heq : _root_.Set.EqOn eta gamma (_root_.Set.Icc a b) := fun r hr => _root_.Set.IccExtend_of_mem hab.le f hr
  have hetaAC : Manifold.absolutelyContinuousOnInterval I eta a b :=
    Manifold.absolutelyContinuousOnInterval_congr hgamma (by
      simpa only [_root_.Set.uIcc_of_le hab.le] using heq.symm)
  have hlag : _root_.Set.EqOn (lRegularizedLagrangian S T gamma)
      (lRegularizedLagrangian S T eta) (_root_.Set.uIoo a b) := by
    intro r hr
    rw [_root_.Set.uIoo_of_le hab.le] at hr
    have hn : gamma =ᶠ[𝓝 r] eta := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
      exact (heq (_root_.Set.Ioo_subset_Icc_self hx)).symm
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
  have hetaInt := hint.congr_uIoo hlag
  obtain ⟨m, t, p, u, ht0, htmono, htlast, hsrc, hrep, _⟩ :=
    exists_timeH1_chart_partition_of_absolutelyContinuousOnInterval S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a b hab.le eta hetaAC hetaInt (fun r hr => hU (htime r hr))
  have hact : lRegularizedAction S T eta a b = lRegularizedAction S T gamma a b :=
    lRegularizedAction_congr S T eta gamma a b (by
      intro r hr
      exact heq (_root_.Set.Ioo_subset_Icc_self (by simpa only [_root_.Set.uIoo_of_le hab.le] using hr)))
  have hminEta : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta a = eta a → delta b = eta b →
      lRegularizedAction S T eta a b ≤ lRegularizedAction S T delta a b := by
    intro delta hdelta ha hb
    rw [hact]
    exact hmin delta hdelta (ha.trans (heq ⟨le_rfl, hab.le⟩))
      (hb.trans (heq ⟨hab.le, le_rfl⟩))
  exact (lMinCurve_c1_of_spatial_derivatives S hS T a b hab t htmono ht0 htlast p eta heta u
    hsrc hrep U hU htime hreg hGramFd hScalFd hminEta).congr heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
