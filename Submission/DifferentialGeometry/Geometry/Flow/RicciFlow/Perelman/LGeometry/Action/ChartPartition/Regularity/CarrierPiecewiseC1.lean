import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierLocalMinimality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.VelocityRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
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
theorem lRegularizedAction_minimizer_chart_piece_contDiffOn_one_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (J : Set Real) (hJ : J ⊆ D.carrier)
    (htime : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ J)
    (hreg : ∀ s ∈ _root_.Set.Ioo a b, T - s ^ 2 ∈ D.regular)
    (hGramFd : ∀ i, ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family (p i) (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I (p i)).target))
    (hScalFd : ∀ i, ContinuousOn (fun z : Real × E => fderiv Real
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) (p i) (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I (p i)).target))
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ∀ i, ContDiffOn Real 1 (u i).toFun
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) := by
  classical
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  intro i
  have hpos : t i.castSucc < t i.succ :=
    ht Fin.castSucc_lt_succ
  have hL : 0 < partitionIntervalLength t i := by
    simpa only [partitionIntervalLength] using sub_pos.mpr hpos
  have hleft : a ≤ t i.castSucc := by
    rw [← ht0]
    exact ht.monotone (Fin.zero_le _)
  have hright : t i.succ ≤ b := by
    rw [← htlast]
    exact ht.monotone (Fin.le_last _)
  have hshift : _root_.Set.MapsTo (fun r : Real ↦ t i.castSucc + r)
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have htimei : ∀ r ∈ _root_.Set.Icc (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ J := by
    intro r hr
    exact htime (t i.castSucc + r)
      ⟨hleft.trans (hshift hr).1, (hshift hr).2.trans hright⟩
  have hregi : ∀ r ∈ _root_.Set.Ioo (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg
    change r ∈ _root_.Set.Ioo (0 : Real) (t i.succ - t i.castSucc) at hr
    constructor <;> linarith [hr.1, hr.2]
  have hchart : _root_.Set.MapsTo (u i).toFun (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target) := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    intro r hr
    rw [hrep i hr]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hlocal : IsLocalMinOn
      (lChartAction S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) :=
    lChartAction_isLocalMinOn_of_lRegularizedAction_minimizer_of_carrier S hS.smoothMetric hSc T a b t ht.monotone
      ht0 htlast p gamma hgamma u hsrc hrep (fun s hs => hJ (htime s hs)) hmin i hpos
  exact (lChartAction_minimizer_contDiffOn_one_of_spatial_derivatives S hS T (t i.castSucc) (p i) hL
    (u i) hJ htimei hregi (hGramFd i) (hScalFd i) hchart hlocal).choose_spec.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_chart_piece_contDiffOn_one_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_chart_piece_contDiffOn_one_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_chart_piece_contDiffOn_one_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_chart_piece_contDiffOn_one_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
