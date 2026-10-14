import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.MixedCompatibility
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def tensorInnerScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    M → ℝ :=
  fun y => tensorInnerPointwise (I := I) (M := M) g r s y
    (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp]
lemma tensorInnerScalar_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (y : M) :
    tensorInnerScalar (I := I) (M := M) g r s W S y =
      tensorInnerPointwise (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (W y)) (TensorRSSpace.toModel (S y)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_apply

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [SigmaCompactSpace M] in
lemma tangentSectionAction_tensorInnerScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) V
        (tensorInnerScalar (I := I) (M := M) g r s W S) x =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s S x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) := by
  rw [tangentSectionAction_def]
  exact tensorInnerPointwise_hasMFDerivAt_metricCompatible
    (I := I) (M := M) g r s W S x (V x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tangentSectionAction_tensorInnerScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tangentSectionAction_tensorInnerScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tangentSectionAction_tensorInnerScalar ``Submission.DifferentialGeometry.Analysis.Elliptic.tangentSectionAction_tensorInnerScalar

omit [CompleteSpace E] in
theorem integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWS : ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S)) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))
          + tensorInnerScalar (I := I) (M := M) g r s W S x
            * divergenceG (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hV_cs : HasCompactSupport (V : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hIBP := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (M := M) g (f := tensorInnerScalar (I := I) (M := M) g r s W S)
    hWS V hV_cs
  have hLeibniz : ∀ x : M,
      tangentSectionAction (I := I) V
          (tensorInnerScalar (I := I) (M := M) g r s W S) x =
        covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) :=
    fun x => tangentSectionAction_tensorInnerScalar
      (I := I) (M := M) g r s W S V x
  have hLHS :
      ∫ x, tangentSectionAction (I := I) V
            (tensorInnerScalar (I := I) (M := M) g r s W S) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
                (Tensor0SSpace.toModel
                  (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g r s S x))
              + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
                (Tensor0SSpace.toModel
                  (liftedTensorSection (I := I) (M := M) g r s W x))
                (Tensor0SSpace.toModel
                  (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hLeibniz)
  have hsum :
      ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergenceG (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← hLHS]; exact hIBP
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hAB_cont : Continuous
      (tangentSectionAction (I := I) V
        (tensorInnerScalar (I := I) (M := M) g r s W S)) :=
    (tangentSectionAction_contMDiff (I := I) V hWS).continuous
  have hAB_int : _root_.MeasureTheory.Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous
        (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s S x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))) := by
      refine hAB_cont.congr (fun x => ?_)
      rw [tangentSectionAction_def]
      exact tensorInnerPointwise_hasMFDerivAt_metricCompatible
        (I := I) (M := M) g r s W S x (V x)
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC_int : _root_.MeasureTheory.Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g r s W S x
        * divergenceG (I := I) g V x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hf_cont : Continuous (tensorInnerScalar (I := I) (M := M) g r s W S) :=
      hWS.continuous
    have hdiv_cont : Continuous (divergenceG (I := I) g V) :=
      (divergence_g_contMDiff (I := I) g V).continuous
    exact (hf_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [_root_.MeasureTheory.integral_add hAB_int hC_int, hsum]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_tangentAction_add_smul_divergence_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_tangentAction_add_smul_divergence_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_tangentAction_add_smul_divergence_eq_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_tangentAction_add_smul_divergence_eq_zero

omit [CompleteSpace E] in
theorem integral_tensorInner_covDeriv_integrationByParts
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWS : ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S))
    (hWcov_int : _root_.MeasureTheory.Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S x)))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hScov_int : _root_.MeasureTheory.Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s W x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAt (I := I) (M := M) g r s S x (V x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        - ∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergenceG (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hC_int : _root_.MeasureTheory.Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g r s W S x
        * divergenceG (I := I) g V x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hf_cont : Continuous (tensorInnerScalar (I := I) (M := M) g r s W S) :=
      hWS.continuous
    have hdiv_cont : Continuous (divergenceG (I := I) g V) :=
      (divergence_g_contMDiff (I := I) g V).continuous
    exact (hf_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcombined := integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (I := I) (M := M) g r s W S V hWS
  set A : M → ℝ := fun x => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (Tensor0SSpace.toModel
      (loweredCovDerivAt (I := I) (M := M) g r s W x (V x)))
    (Tensor0SSpace.toModel
      (liftedTensorSection (I := I) (M := M) g r s S x)) with hA_def
  set B : M → ℝ := fun x => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (Tensor0SSpace.toModel
      (liftedTensorSection (I := I) (M := M) g r s W x))
    (Tensor0SSpace.toModel
      (loweredCovDerivAt (I := I) (M := M) g r s S x (V x))) with hB_def
  set C : M → ℝ := fun x => tensorInnerScalar (I := I) (M := M) g r s W S x
    * divergenceG (I := I) g V x with hC_def
  have hcombined' :
      ∫ x, (A x + B x + C x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := hcombined
  have hsplitAB :
      ∫ x, (A x + B x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        (∫ x, A x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, B x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_add hWcov_int hScov_int
  have hsplitABC :
      ∫ x, (A x + B x + C x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        (∫ x, (A x + B x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          ∫ x, C x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    _root_.MeasureTheory.integral_add (hWcov_int.add hScov_int) hC_int
  rw [hsplitABC, hsplitAB] at hcombined'
  linarith [hcombined']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_integrationByParts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_integrationByParts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_integrationByParts ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_integrationByParts

end Elliptic
end Analysis
end DifferentialGeometry

end
