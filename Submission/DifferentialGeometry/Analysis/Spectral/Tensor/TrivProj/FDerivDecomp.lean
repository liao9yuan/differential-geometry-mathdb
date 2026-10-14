import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma tensorTrivProj_eq_tensorRSChartE_section_repr
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tensorTrivProj (I := I) (M := M) g r s S α =
      tensorRSChartESectionRepr (I := I) r s α (fun b => S.toSection b) := by
  funext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_tensorRSChartE_section_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_tensorRSChartE_section_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_tensorRSChartE_section_repr ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_eq_tensorRSChartE_section_repr

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (tensorRSIntrinsicChartCLM (I := I) r s α (fun b' => S.toSection b') b
          (trivFromE (I := I) α b w)) := by
  classical
  rw [tensorTrivProj_eq_tensorRSChartE_section_repr (I := I) (M := M) g r s S α]
  rw [tensorRSIntrinsicChartCLM_apply
    (I := I) r s α (fun b' => S.toSection b') b
    (trivFromE (I := I) α b w)]
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [trivToE_trivFromE (I := I) α hb_base w]
  unfold tensorRSChartFiberFromModel
  have hb_baseRS : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ ((_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet)
    refine ⟨?_, ?_⟩
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb_base
    · change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
      exact hb_base
  exact ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
    (R := ℝ) hb_baseRS _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorRSIntrinsicChartCLM_apply_eq_cov
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) :
    tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T X b
        - (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := by
  classical
  rw [chartTensorRSCovariantDerivative_def
    (I := I) r s g α T X b]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSIntrinsicChartCLM_apply_eq_cov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSIntrinsicChartCLM_apply_eq_cov target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X b = trivFromE (I := I) α b w) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') X b
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l) ) := by
  classical
  rw [fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb w]
  rw [show trivFromE (I := I) α b w = X b from hXb.symm]
  rw [tensorRSIntrinsicChartCLM_apply_eq_cov
    (I := I) r s g α (fun b' => S.toSection b') X b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X.toFun b = trivFromE (I := I) α b w) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X.toFun b)
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X.toFun b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X.toFun b l) ) := by
  classical
  rw [fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov
    (I := I) (M := M) g r s α S X.toFun hb w hXb]
  have hcov_eq :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X.toFun b =
        TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X.toFun b) :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet
      (I := I) (M := M) g r s α S.toSection X hb
  rw [hcov_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.fderiv_tensorTrivProj_pullback_apply_eq_abstract_cov

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem mfderiv_tensorTrivProj_apply_eq_triv_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) v =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (tensorRSIntrinsicChartCLM (I := I) r s α (fun b' => S.toSection b') b v) := by
  classical
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [mfderiv_tensorTrivProj_eq_chart_fderiv
    (I := I) (M := M) g r s S α hb_chart hb_int v]
  rw [fderiv_tensorTrivProj_pullback_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb (trivToE (I := I) α b v)]
  rw [trivFromE_trivToE (I := I) α hb_base v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_triv_intrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_triv_intrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_triv_intrinsic ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_triv_intrinsic

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (mfderiv I (𝓘(ℝ, TensorRSModel r s ℝ E))
        (tensorTrivProj (I := I) (M := M) g r s S α) b) (X b) =
      (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ( chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') X b
          - (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l) ) := by
  classical
  rw [mfderiv_tensorTrivProj_apply_eq_triv_intrinsic
    (I := I) (M := M) g r s α S hb (X b)]
  rw [tensorRSIntrinsicChartCLM_apply_eq_cov
    (I := I) r s g α (fun b' => S.toSection b') X b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mfderiv_tensorTrivProj_apply_eq_chart_pushforward_cov

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
