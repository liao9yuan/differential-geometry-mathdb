import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.DistanceExponential
import Submission.DifferentialGeometry.Geometry.Metric.Distance.ExponentialWeight

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Geometry.Metric

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
theorem exists_positive_smooth_exp_distance_weight_integrable_sq
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a) :
    ∃ η : C^∞⟮I, M; ℝ⟯,
      (∀ x, 0 < η x) ∧
      (∀ x, Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal + 1)) ≤ η x ∧
        η x ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - 1))) ∧
      (∀ x, Tensor0SBundle.normSq0S g x 1
        (Geometry.Operator.differential1FormFun η x) ≤ 9 * a ^ 2 * (η x) ^ 2) ∧
      Integrable (fun x => (η x) ^ 2) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have ha : 0 ≤ a := by
    have hnonneg : 0 ≤ q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E := by positivity
    linarith
  obtain ⟨η, hηpos, hηbounds, hηgrad⟩ := exists_positive_smooth_exp_distance_weight g p ha
  refine ⟨η, hηpos, hηbounds, hηgrad, ?_⟩
  have hηsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (η : M → ℝ) := η.contMDiff
  apply integrable_sq_of_exp_riemannianDistance_bound g hcomplete p hq hRic hgap
    (η := (η : M → ℝ)) (offset := 1) hηsmooth.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [abs_of_pos (hηpos x)]
    exact (hηbounds x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.exists_positive_smooth_exp_distance_weight_integrable_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.exists_positive_smooth_exp_distance_weight_integrable_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.exists_positive_smooth_exp_distance_weight_integrable_sq ``Submission.DifferentialGeometry.Integral.Measure.exists_positive_smooth_exp_distance_weight_integrable_sq

end DifferentialGeometry.Integral.Measure
