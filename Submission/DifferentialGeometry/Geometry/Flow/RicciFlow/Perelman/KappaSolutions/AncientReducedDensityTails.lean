import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Estimates.GaussianTail
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance tailTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailTopology target :: scope.openDecls } }
private local instance tailCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailCharted target :: scope.openDecls } }
private local instance tailSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSmooth target :: scope.openDecls } }
private local instance tailT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailT2 target :: scope.openDecls } }
private local instance tailSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tailSigma target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM target :: scope.openDecls } }

theorem ancient_redDensity_tail_le_of_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau B : ℝ} (htau : 0 < tau)
    (hq : redLength F.S 0 p q tau ≤ B) (N : ℕ) :
    (∫⁻ x in {x : F.M | (N : ℝ) ≤
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal},
      ENNReal.ofReal (redDensity F.S 0 p x tau)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) ≤
    ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) *
      (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
        gaussianTail (Module.finrank ℝ E)
          ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) N) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  let g := F.S.base.metric (-tau)
  have htime : -tau ∈ ancientTimeInterval.carrier := by
    change -tau ≤ 0
    exact neg_nonpos.mpr htau.le
  have hcomplete : RiemannianMetricComplete (I := I) g := ⟨hF.complete (-tau) htime⟩
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro x v
    rw [_root_.MulZeroClass.zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric (-tau)) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-tau) htime x n c a b
  have hdecay : 0 < (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau := by
    positivity
  have hlower (x : F.M) :
      ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) *
        (riemannianEDistOf (I := I) g q x).toReal ^ 2 - (1 + B) ≤
      redLength F.S 0 p x tau := by
    have h := ancientKappa_reducedCost_two_point_between F hF p q x htau
    change _ - 1 - redLength F.S 0 p q tau ≤ redLength F.S 0 p x tau at h
    dsimp only [g]
    have heq : ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) *
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal ^ 2 =
      (1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) *
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal ^ 2 / tau := by ring
    rw [heq]
    linarith
  have hdensity (x : F.M) : redDensity F.S 0 p x tau =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      Real.exp (-redLength F.S 0 p x tau) := by
    rw [redDensity, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hdensity]
  exact lintegral_exp_neg_le_gaussianTail_of_quadratic_lower_bound
    g hcomplete hRic q hdecay (Real.exp_nonneg _) hlower N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_tail_le_of_redLength_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_tail_le_of_redLength_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_tail_le_of_redLength_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensity_tail_le_of_redLength_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section

noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance uniformTailTopology
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailTopology target :: scope.openDecls } }
private local instance uniformTailCharted
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailCharted target :: scope.openDecls } }
private local instance uniformTailSmooth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailSmooth target :: scope.openDecls } }
private local instance uniformTailT2
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailT2 target :: scope.openDecls } }
private local instance uniformTailSigma
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailSigma target :: scope.openDecls } }
private local instance uniformTailMeasurable
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailMeasurable target :: scope.openDecls } }
private local instance uniformTailBorel
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformTailBorel target :: scope.openDecls } }

theorem exists_uniform_ancient_redDensity_tail_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
      ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (p q : F.M) {tau : ℝ}, tau ∈ _root_.Set.Icc a b → redLength F.S 0 p q tau ≤ B →
      (∫⁻ x in {x : F.M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal},
        ENNReal.ofReal (redDensity F.S 0 p x tau)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) < ε := by
  let c : ℝ := 1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) *
    ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹))
  have hC : C ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (_root_.MeasureTheory.measure_ne_top volume.toSphere _root_.Set.univ) ENNReal.ofReal_ne_top)
  have hlim : _root_.Filter.Tendsto (fun N => C * gaussianTail (Module.finrank ℝ E) (c / b) N)
      atTop (𝓝 0) := by
    simpa only [_root_.MulZeroClass.mul_zero] using ENNReal.Tendsto.const_mul
      (tendsto_gaussianTail (Module.finrank ℝ E) (div_pos hc hb)) (Or.inr hC)
  obtain ⟨N, hN⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨N, ?_⟩
  intro F kappa hF p q tau htau hq
  have htau0 : 0 < tau := lt_of_lt_of_le ha htau.1
  have hpref :
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) ≤
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply sub_le_sub_right
    exact mul_le_mul_of_nonpos_left (Real.log_le_log ha htau.1)
      (neg_nonpos.mpr (by positivity))
  have htail : gaussianTail (Module.finrank ℝ E) (c / tau) N ≤
      gaussianTail (Module.finrank ℝ E) (c / b) N :=
    antitone_gaussianTail_decay _ _ (div_le_div_of_nonneg_left hc.le htau0 htau.2)
  apply lt_of_le_of_lt (ancient_redDensity_tail_le_of_redLength_le F hF p q htau0 hq N)
  apply lt_of_le_of_lt _ hN
  dsimp only [C, c] at *
  simpa only [mul_assoc] using mul_le_mul' hpref (mul_le_mul_right htail
    ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_tail_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_tail_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_tail_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_tail_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance closedBallTailTopology
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailTopology target :: scope.openDecls } }
private local instance closedBallTailCharted
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailCharted target :: scope.openDecls } }
private local instance closedBallTailSmooth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailSmooth target :: scope.openDecls } }
private local instance closedBallTailT2
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailT2 target :: scope.openDecls } }
private local instance closedBallTailSigma
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailSigma target :: scope.openDecls } }
private local instance closedBallTailMeasurable
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailMeasurable target :: scope.openDecls } }
private local instance closedBallTailBorel
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) :
    BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedBallTailBorel target :: scope.openDecls } }

theorem exists_uniform_ancient_redDensity_closedBall_compl_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
      ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (p q : F.M) {tau : ℝ}, tau ∈ _root_.Set.Icc a b → redLength F.S 0 p q tau ≤ B →
      (∫⁻ x in (riemannianClosedBallOf (I := I) (F.S.base.metric (-tau)) q (N : ℝ))ᶜ,
        ENNReal.ofReal (redDensity F.S 0 p x tau)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))) < ε := by
  obtain ⟨N, hN⟩ := exists_uniform_ancient_redDensity_tail_bound
    (I := I) (B := B) ha hab hε
  refine ⟨N, ?_⟩
  intro F kappa hF p q tau htau hq
  let _ : ConnectedSpace F.M := hF.connected
  have hsubset :
      (riemannianClosedBallOf (I := I) (F.S.base.metric (-tau)) q (N : ℝ))ᶜ ⊆
        {x : F.M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal} := by
    intro x hx
    change ¬ riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x ≤
      ENNReal.ofReal (N : ℝ) at hx
    change (N : ℝ) ≤
      (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal
    by_contra hsmall
    have hsmall' :
        (riemannianEDistOf (I := I) (F.S.base.metric (-tau)) q x).toReal < (N : ℝ) :=
      lt_of_not_ge hsmall
    have hfinite := riemannianEDistOf_ne_top (I := I) (F.S.base.metric (-tau)) q x
    exact hx ((ENNReal.ofReal_toReal hfinite).symm.trans_le
      (ENNReal.ofReal_le_ofReal hsmall'.le))
  exact (_root_.MeasureTheory.lintegral_mono_set hsubset).trans_lt (hN F hF p q htau hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_closedBall_compl_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_closedBall_compl_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_closedBall_compl_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redDensity_closedBall_compl_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM_1 : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instMeasurableSpaceM_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM_1 : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instBorelSpaceM_1 target :: scope.openDecls } }

theorem ancient_redVolume_le_of_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau B : ℝ} (htau : 0 < tau)
    (hq : redLength F.S 0 p q tau ≤ B) :
    redVolume F.S 0 p tau ≤
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) *
        (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
          gaussianTail (Module.finrank ℝ E)
            ((1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)) / tau) 0) := by
  have h := ancient_redDensity_tail_le_of_redLength_le F hF p q htau hq 0
  simpa only [redVolume, zero_sub, Nat.cast_zero, ENNReal.toReal_nonneg,
    Set.ofPred_true, Measure.restrict_univ] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redVolume_le_of_redLength_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redVolume_le_of_redLength_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redVolume_le_of_redLength_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redVolume_le_of_redLength_le

omit F in
theorem exists_uniform_ancient_redVolume_bound
    {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval),
        ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F →
        ∀ (p q : F.M) {tau : ℝ}, tau ∈ _root_.Set.Icc a b →
          redLength F.S 0 p q tau ≤ B → redVolume F.S 0 p tau ≤ C := by
  let c : ℝ := 1 / (576 * ((Module.finrank ℝ E : ℝ) + 1) ^ 2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := ha.trans_le hab
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) *
    (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
      gaussianTail (Module.finrank ℝ E) (c / b) 0)
  have hseries : gaussianTail (Module.finrank ℝ E) (c / b) 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    simpa only [gaussianTail, Nat.add_zero] using
      (summable_gaussianShell (Module.finrank ℝ E) (div_pos hc hb)).tsum_ofReal_ne_top
  have hC : C < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (_root_.MeasureTheory.measure_lt_top volume.toSphere _root_.Set.univ) ENNReal.ofReal_lt_top)
        hseries)
  refine ⟨C, hC, ?_⟩
  intro F kappa hF p q tau htau hq
  have htau0 : 0 < tau := ha.trans_le htau.1
  have hpref :
      ENNReal.ofReal (Real.exp
        (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) ≤
        ENNReal.ofReal (Real.exp
          (-((Module.finrank ℝ E : ℝ) / 2) * Real.log a -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) * Real.exp (1 + B)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    apply sub_le_sub_right
    exact mul_le_mul_of_nonpos_left (Real.log_le_log ha htau.1)
      (neg_nonpos.mpr (by positivity))
  have htail : gaussianTail (Module.finrank ℝ E) (c / tau) 0 ≤
      gaussianTail (Module.finrank ℝ E) (c / b) 0 :=
    antitone_gaussianTail_decay _ _ (div_le_div_of_nonneg_left hc.le htau0 htau.2)
  apply (ancient_redVolume_le_of_redLength_le F hF p q htau0 hq).trans
  dsimp only [C, c] at *
  exact mul_le_mul' hpref (mul_le_mul_right htail
    ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redVolume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redVolume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redVolume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_ancient_redVolume_bound

theorem ancient_redDensityMeasure_isFiniteMeasure
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    IsFiniteMeasure (redDensityMeasure F.S 0 p tau) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_ancient_redVolume_bound (I := I)
    (B := redLength F.S 0 p p tau) htau le_rfl
  constructor
  rw [redDensityMeasure_univ]
  exact (hbound F hF p p ⟨le_rfl, le_rfl⟩ le_rfl).trans_lt hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensityMeasure_isFiniteMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensityMeasure_isFiniteMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensityMeasure_isFiniteMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redDensityMeasure_isFiniteMeasure

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
