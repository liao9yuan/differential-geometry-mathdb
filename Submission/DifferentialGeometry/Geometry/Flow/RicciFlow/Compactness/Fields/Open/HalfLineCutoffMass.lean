import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.TimeIntegral
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGramContinuity
import Submission.DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM : MeasurableSpace P.M := borel P.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM : BorelSpace P.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp
    [PreconnectedSpace P.M]
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : _root_.Set.Iic (0 : ℝ) ⊆ X.D.carrier)
    {a c : ℝ} (ha : 1 ≤ a) (μ : _root_.MeasureTheory.Measure (_root_.Set.Ioo a c))
    (ell : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ)) (p : P.M) {r : ℝ} (hr : 0 < r) :
    _root_.MeasureTheory.AEStronglyMeasurable (fun s : _root_.Set.Ioo a c => ∫ y,
      radialDistanceCutoff (co.gInf (1 - a)) p r y *
        Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) μ := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology P.M := ChartedSpace.secondCountable_of_sigmaCompact H P.M
  let G : _root_.Set.Ioo a c → SmoothRiemannianMetric I P.M := fun s => co.gInf (1 - (s : ℝ))
  let qref := co.gInf (1 - a)
  let cutoff := radialDistanceCutoff qref p r
  let f : _root_.Set.Ioo a c × P.M → ℝ := fun v =>
    ell (v.2, (⟨(v.1 : ℝ), ha.trans v.1.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))
  let w : _root_.Set.Ioo a c × P.M → ℝ := fun v => Real.exp (-f v -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (v.1 : ℝ) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hf : Continuous f :=
    ell.continuous.comp (continuous_snd.prodMk
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _))
  have hlog : Continuous (fun v : _root_.Set.Ioo a c × P.M => Real.log (v.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).log (fun v =>
      ne_of_gt (zero_lt_one.trans_le (ha.trans v.1.property.1.le)))
  have hw : Continuous w :=
    Real.continuous_exp.comp
      ((hf.neg.sub (continuous_const.mul hlog)).sub continuous_const)
  have hcutoff : Continuous cutoff := continuous_radialDistanceCutoff qref p hr
  have hweight : Continuous (fun v : _root_.Set.Ioo a c × P.M => cutoff v.2 * w v) :=
    (hcutoff.comp continuous_snd).mul hw
  have hgram : ∀ (alpha : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun v : _root_.Set.Ioo a c × P.M =>
        Tensor.Coordinates.chartGramMatrix (G v.1) alpha v.2 i j)
        (_root_.Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet) := by
    intro alpha i j
    have hc := continuousOn_chartGramMatrix
      (I := I) (X := X) (P := P) (phi := phi) Phi
      (R := R) (bf := bf) (hsrc := hsrc) (htgt := htgt) co hcarrier alpha i j
    have hmap : Continuous (fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
    have hmaps : _root_.Set.MapsTo (fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
        (_root_.Set.univ ×ˢ (chartAt H alpha).source)
        (_root_.Set.Iic (0 : ℝ) ×ˢ (chartAt H alpha).source) := by
      intro v hv
      exact ⟨sub_nonpos.mpr (ha.trans v.1.property.1.le), hv.2⟩
    have hcomp := ContinuousOn.comp'
      (g := fun q : ℝ × P.M =>
        Tensor.Coordinates.chartGramMatrix (co.gInf q.1) alpha q.2 i j)
      (f := fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
      (s := _root_.Set.univ ×ˢ (chartAt H alpha).source)
      (t := _root_.Set.Iic (0 : ℝ) ×ˢ (chartAt H alpha).source)
      hc hmap.continuousOn hmaps
    exact hcomp
  have houter := aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram
    (I := I) (M := P.M) qref G μ
    (f := fun v : _root_.Set.Ioo a c × P.M => cutoff v.2 * w v) hgram hweight.aestronglyMeasurable
  exact houter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
