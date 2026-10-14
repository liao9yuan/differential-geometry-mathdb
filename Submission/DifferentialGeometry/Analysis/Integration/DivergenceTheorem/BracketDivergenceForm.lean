import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.MovingFrame.IntegratedNullity
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorThirdOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

section NormedSmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

def smoothExtensionTangentSection (x : M) (v : TangentSpace I x) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma smoothExtensionTangentSection_apply (x : M) (v : TangentSpace I x) (b : M) :
    smoothExtensionTangentSection (I := I) (M := M) x v b = smoothExtensionTangent (I := I) x v b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.smoothExtensionTangentSection_apply

end NormedSmoothExtension

def lieBracketSection (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b),
    mlieBracket_contMDiff (I := I) X.contMDiff Y.contMDiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma lieBracketSection_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    lieBracketSection (I := I) (M := M) X Y b =
      VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b) b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.lieBracketSection_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem loweredCovDerivAlongVF_firstSlot_eq_lower_covApply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (covApply (tensorCov (I := I) g r s) (fun y : M => V y)
              (fun y : M => W'.toSection y) x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) := by
  classical
  have hbridge := loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
    (I := I) (M := M) g r s W'.toSection x (V x)
  rw [loweredCovDerivAlongVF_apply, hbridge]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDerivAlongVF_firstSlot_eq_lower_covApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDerivAlongVF_firstSlot_eq_lower_covApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDerivAlongVF_firstSlot_eq_lower_covApply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDerivAlongVF_firstSlot_eq_lower_covApply

theorem loweredCovDeriv_leibniz_combined_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
          + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
            * divergenceG (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g r s
    W'.toSection Z.toSection V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_leibniz_combined_integral_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_leibniz_combined_integral_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_leibniz_combined_integral_eq_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_leibniz_combined_integral_eq_zero

theorem loweredCovDeriv_bracketChannel_combined_isDivergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
          + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
            * divergenceG (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  loweredCovDeriv_leibniz_combined_integral_eq_zero
    (I := I) (M := M) g r s W' Z V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_isDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_isDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_isDivergence ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_isDivergence

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g
        (smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection)
          V) x =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
        + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
        + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
          * divergenceG (I := I) g V x := by
  rw [divergence_g_smoothSmul (I := I) (M := M) g
    (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection) V x]
  rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g r s
    W'.toSection Z.toSection V x]
  rw [loweredCovDerivAlongVF_apply, loweredCovDerivAlongVF_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [T2Space M] in
theorem divergence_g_finset_sum
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergenceG (I := I) g (∑ i, V i) x = ∑ i, divergenceG (I := I) g (V i) x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact divergence_g_zero (I := I) (M := M) g x
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [divergence_g_add (I := I) (M := M) g (V a) (∑ i ∈ t, V i) x]
    rw [ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_finset_sum ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_finset_sum

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) (x : M) :
    divergenceG (I := I) g
        (∑ i, smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (V i)) x =
      ∑ i, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergenceG (I := I) g (V i) x) := by
  classical
  rw [divergence_g_finset_sum (I := I) (M := M) g _ x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (I := I) (M := M) g r s (W i) Z (V i) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem frameSummed_bracketCovDeriv_combined_eq_divergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) (x : M) :
    divergenceG (I := I) g
        (∑ i, smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (V i)) x =
      ∑ i, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergenceG (I := I) g (V i) x) :=
  frameSummed_covDerivAlongVF_leibniz_combined_eq_divergence
    (I := I) (M := M) g r s V W Z x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_bracketCovDeriv_combined_eq_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_bracketCovDeriv_combined_eq_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_bracketCovDeriv_combined_eq_divergence ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.frameSummed_bracketCovDeriv_combined_eq_divergence

theorem integral_frameSummed_bracketCovDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergenceG (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g r s V W Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_frameSummed_bracketCovDeriv_combined_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_frameSummed_bracketCovDeriv_combined_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_frameSummed_bracketCovDeriv_combined_eq_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_frameSummed_bracketCovDeriv_combined_eq_zero

end DivergenceTheorem
end Integral
end DifferentialGeometry

end
