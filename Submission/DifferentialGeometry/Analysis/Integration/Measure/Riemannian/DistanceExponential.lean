import Submission.DifferentialGeometry.Analysis.Integration.Measure.Estimates.DistanceExponential
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicGrowth
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Analysis.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_exp_neg_mul_of_riemannianEDistOf_sub_le [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {q decay offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < decay)
    {ρ : M → ℝ} (hρ : AEMeasurable ρ (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlower : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      (riemannianEDistOf (I := I) g p x).toReal - offset ≤ ρ x) :
    Integrable (fun x => Real.exp (-decay * ρ x)) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hdist (x : M) : _root_.Dist.dist p x = (riemannianEDistOf (I := I) g p x).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
      (I := I) (M := M) p x
  let C : ℝ≥0∞ :=
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere _root_.Set.univ
  have hball : ∀ R : ℝ, 1 ≤ R →
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p R) ≤
        C * ENNReal.ofReal (Real.exp
          ((q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E) * R)) := by
    intro R hR
    have hset : Metric.ball p R =
        {x : M | riemannianEDistOf (I := I) g p x < ENNReal.ofReal R} := by
      ext x
      simp only [Metric.mem_ball, _root_.Set.mem_ofPred_eq]
      rw [dist_comm, hdist]
      exact (ENNReal.lt_ofReal_iff_toReal_lt
        (riemannianEDistOf_ne_top (I := I) g p x)).symm
    rw [hset]
    exact riemannianVolumeMeasure_ball_le_exponential g hcomplete p hq
      (zero_lt_one.trans_le hR) hRic
  have hdecay : 0 ≤ decay := le_trans (by positivity) hgap.le
  apply integrable_exp_neg_mul_of_dist_sub_le_of_exponential_ball_growth
    (riemannianVolumeMeasure (I := I) (M := M) g) p (_root_.MeasureTheory.measure_ne_top _ _) hdecay hgap hball hρ
  simpa only [hdist] using hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_of_riemannianEDistOf_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_of_riemannianEDistOf_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_of_riemannianEDistOf_sub_le ``Submission.DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_of_riemannianEDistOf_sub_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_exp_neg_mul_riemannianEDistOf [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {q decay : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < decay) :
    Integrable (fun x => Real.exp (-decay * (riemannianEDistOf (I := I) g p x).toReal))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hcont : Continuous (fun x => riemannianEDistOf (I := I) g p x) := by
    simpa only [riemannianEDistOf] using
      DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g p
  have hcontReal : Continuous (fun x => (riemannianEDistOf (I := I) g p x).toReal) :=
    ENNReal.continuousOn_toReal.comp_continuous hcont
      (fun x => riemannianEDistOf_ne_top (I := I) g p x)
  exact integrable_exp_neg_mul_of_riemannianEDistOf_sub_le g hcomplete p hq hRic hgap
    hcontReal.measurable.aemeasurable (offset := 0)
    (Filter.Eventually.of_forall fun x => by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_riemannianEDistOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_riemannianEDistOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_riemannianEDistOf ``Submission.DifferentialGeometry.Integral.Measure.integrable_exp_neg_mul_riemannianEDistOf

end DifferentialGeometry.Integral.Measure

end

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_sq_of_exp_riemannianDistance_bound
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a)
    {η : M → ℝ}
    (hη : _root_.MeasureTheory.AEStronglyMeasurable η (riemannianVolumeMeasure (I := I) (M := M) g))
    (hbound : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      |η x| ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - offset))) :
    Integrable (fun x => (η x) ^ 2) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hexp := integrable_exp_neg_mul_riemannianEDistOf g hcomplete p hq hRic hgap
  have hmajor := hexp.const_mul (Real.exp (2 * a * offset))
  apply hmajor.mono (hη.pow 2)
  filter_upwards [hbound] with x hx
  have heta : (η x) ^ 2 ≤ Real.exp (-a *
      ((riemannianEDistOf (I := I) g p x).toReal - offset)) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le).2 hx |>.trans' (by rw [sq_abs])
  have hrewrite : Real.exp (-a *
      ((riemannianEDistOf (I := I) g p x).toReal - offset)) ^ 2 =
      Real.exp (2 * a * offset) * Real.exp (-(2 * a) *
        (riemannianEDistOf (I := I) g p x).toReal) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact heta.trans_eq hrewrite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_sq_of_exp_riemannianDistance_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_sq_of_exp_riemannianDistance_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_sq_of_exp_riemannianDistance_bound ``Submission.DifferentialGeometry.Integral.Measure.integrable_sq_of_exp_riemannianDistance_bound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_mul_sq_of_exp_riemannianDistance_bound
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a)
    {η : M → ℝ}
    (hη : _root_.MeasureTheory.AEStronglyMeasurable η (riemannianVolumeMeasure (I := I) (M := M) g))
    (hbound : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      |η x| ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - offset)))
    {f : M → ℝ} (hf : _root_.MeasureTheory.AEStronglyMeasurable f (riemannianVolumeMeasure (I := I) (M := M) g))
    {K : ℝ} (hK : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g, ‖f x‖ ≤ K) :
    _root_.MeasureTheory.Integrable (fun x => f x * (η x) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (integrable_sq_of_exp_riemannianDistance_bound g hcomplete p hq hRic hgap hη hbound).bdd_mul hf hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_mul_sq_of_exp_riemannianDistance_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_mul_sq_of_exp_riemannianDistance_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_mul_sq_of_exp_riemannianDistance_bound ``Submission.DifferentialGeometry.Integral.Measure.integrable_mul_sq_of_exp_riemannianDistance_bound

end DifferentialGeometry.Integral.Measure
