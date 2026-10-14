import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.LocalMinimality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space M] in
omit [CompactSpace M] in
theorem lChartAction_pair_le_of_lRegularizedAction_minimizer
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : Real) (t : Fin 3 → Real) (htmono : Monotone t)
    (p : Fin 2 → M) (gamma : Real → M)
    (u : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ _root_.Set.Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta (t 0) = gamma (t 0) →
      delta (t (Fin.last 2)) = gamma (t (Fin.last 2)) →
      lRegularizedAction S T gamma (t 0) (t (Fin.last 2)) ≤
        lRegularizedAction S T delta (t 0) (t (Fin.last 2)))
    (v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (hvtar : ∀ i, _root_.Set.MapsTo (v i).toFun
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I (p i)).target)
    (hv0 : (extChartAt I (p 0)).symm ((v 0).toFun 0) = gamma (t 0))
    (hv2 : (extChartAt I (p 1)).symm
      ((v 1).toFun (partitionIntervalLength t 1)) = gamma (t (Fin.last 2)))
    (hvnode : (extChartAt I (p 0)).symm
        ((v 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0)) :
    (∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (u i)) ≤
      ∑ i : Fin 2, lChartAction S T (t i.castSucc) (p i) (v i) := by
  obtain ⟨gammaV, hgammaV, hsrcV, hrepV, hV0, hV2, alpha, _w,
      halpha, halpha0, halpha2, _hsrcA, _hrepA, _hw, _huniform, hact⟩ :=
    exists_contMDiff_one_lRegularizedAction_approximation_of_compatible_chartH1_pair (I := I) S hMet hSc T t htmono p v hvtar hvnode hreg
  have hneg : _root_.Filter.Tendsto
      (fun n ↦ -lRegularizedAction S T (alpha n) (t 0) (t (Fin.last 2))) _root_.Filter.atTop
      (nhds (-lRegularizedAction S T gammaV (t 0) (t (Fin.last 2)))) :=
    continuousAt_neg.tendsto.comp hact
  have hglobal : lRegularizedAction S T gamma (t 0) (t (Fin.last 2)) ≤
      lRegularizedAction S T gammaV (t 0) (t (Fin.last 2)) := by
    have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg
      (hmin (alpha n) (halpha n)
        ((halpha0 n).trans (hV0.trans hv0))
        ((halpha2 n).trans (hV2.trans hv2)))
    linarith
  rw [lRegularizedAction_eq_sum_lChartAction S hMet hSc T (t 0) (t (Fin.last 2))
    t htmono rfl rfl p gamma u hsrc hrep hreg] at hglobal
  rw [lRegularizedAction_eq_sum_lChartAction S hMet hSc T (t 0) (t (Fin.last 2))
    t htmono rfl rfl p gammaV v hsrcV hrepV hreg] at hglobal
  exact hglobal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_pair_le_of_lRegularizedAction_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_pair_le_of_lRegularizedAction_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_pair_le_of_lRegularizedAction_minimizer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartAction_pair_le_of_lRegularizedAction_minimizer

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
