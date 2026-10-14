import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.CovariantDerivative
import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.InnerSectionSmoothness

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
    CovariantDerivative
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
  [BoundarylessManifold I M]

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

def loweredCovDerivAlongVFraw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, Tensor0SSpace (r + s) I y :=
  fun y => loweredCovDerivAt (I := I) (M := M) g r s S y (X y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma loweredCovDerivAlongVFraw_eq_covApply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X =
      covApply (tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g))
        (fun y : M => X y)
        (liftedTensorSection (I := I) (M := M) g r s S) := by
  funext y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_covApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_covApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_covApply ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_covApply

omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma loweredCovDerivAlongVFraw_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)) := by
  classical
  set cov := tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    with hcov_def
  have hLift : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (liftedTensorSection (I := I) (M := M) g r s S y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact liftedTensorSection_contMDiff (I := I) (M := M) g r s S
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) :=
    X.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun z : M => Tensor0SSpace (r + s) I z) y
        (covApply cov (fun y : M => X y)
          (liftedTensorSection (I := I) (M := M) g r s S) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hX hLift
  rw [loweredCovDerivAlongVFraw_eq_covApply]
  rw [← contMDiffOn_univ]
  exact hOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma loweredCovDerivAlongVFraw_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : M}
    (hy : y ∉ tsupport (fun b : M => TensorRSSpace.toModel (S b))) :
    loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y = 0 := by
  classical
  set cov := tensor0SCovariantDerivative I M (r + s) (LeviCivita (I := I) g)
    with hcov_def
  have hS_eq : (fun b : M => TensorRSSpace.toModel (S b)) =ᶠ[𝓝 y] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hy
  rw [Filter.eventuallyEq_iff_exists_mem] at hS_eq
  obtain ⟨V, hV_nhds, hV_eq⟩ := hS_eq
  obtain ⟨U, hUV, hU_open, hyU⟩ := mem_nhds_iff.mp hV_nhds
  have hLift_zero : ∀ b ∈ U,
      liftedTensorSection (I := I) (M := M) g r s S b = 0 := by
    intro b hbU
    have h_model_zero : TensorRSSpace.toModel (S b) = 0 := by
      have := hV_eq (hUV hbU); simpa using this
    have hS_b_zero : S b = 0 := by
      have : TensorRSSpace.toModel (S b) =
          TensorRSSpace.toModel (0 : TensorRSSpace r s I b) := by
        rw [h_model_zero, TensorRSSpace.toModel_zero]
      exact TensorRSSpace.toModel_injective this
    rw [liftedTensorSection_apply, hS_b_zero, TensorRSSpace.toModel_zero, map_zero]
    rfl
  have hLift_diff_y : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun w : M => Tensor0SSpace (r + s) I w) z
        (liftedTensorSection (I := I) (M := M) g r s S z)) y :=
    ((liftedTensorSection_contMDiff (I := I) (M := M) g r s S) y).mdifferentiableAt
      (by simp)
  have hcov_zero : cov.toFun
      (liftedTensorSection (I := I) (M := M) g r s S) y = 0 := by
    have hU_nhds : U ∈ 𝓝 y := hU_open.mem_nhds hyU
    have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E))
        (fun z : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
          (E := fun w : M => Tensor0SSpace (r + s) I w) z
          (0 : Tensor0SSpace (r + s) I z)) y :=
      mdifferentiableAt_zeroSection (𝕜 := ℝ)
        (F := Tensor0SModel (r + s) ℝ E)
        (E := fun w : M => Tensor0SSpace (r + s) I w) (IB := I)
    have hT_eq : ∀ᶠ z in 𝓝 y,
        liftedTensorSection (I := I) (M := M) g r s S z =
          (fun w : M => (0 : Tensor0SSpace (r + s) I w)) z :=
      Filter.Eventually.mono (Filter.eventually_of_mem hU_nhds (fun z hz => hz))
        (fun z hz => hLift_zero z hz)
    have h_eq : cov.toFun (liftedTensorSection (I := I) (M := M) g r s S) y =
        cov.toFun (fun z : M => (0 : Tensor0SSpace (r + s) I z)) y :=
      cov.isCovariantDerivativeOn.congr_of_eventuallyEq hLift_diff_y hzero_diff
        (Filter.univ_mem) hT_eq
    rw [h_eq]
    exact congrArg (fun φ => φ y) cov.zero
  change loweredCovDerivAt (I := I) (M := M) g r s S y (X y) = 0
  rw [loweredCovDerivAt_def]
  change cov.toFun (liftedTensorSection (I := I) (M := M) g r s S) y (X y) = 0
  rw [hcov_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_zero_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_zero_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_zero_off_tsupport ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_eq_zero_off_tsupport

omit [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [SigmaCompactSpace M] in
lemma loweredCovDerivAlongVFraw_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (hS_cc : HasCompactSupport (fun b : M => TensorRSSpace.toModel (S b)))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    HasCompactSupport (fun y : M => Tensor0SSpace.toModel
      (loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact hS_cc ?_
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hynot
  apply hy
  rw [loweredCovDerivAlongVFraw_eq_zero_off_tsupport (I := I) (M := M) g r s S X hynot,
    Tensor0SSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVFraw_hasCompactSupport

def loweredCovDerivAlongVF
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; Tensor0SModel (r + s) ℝ E, (fun x : M => Tensor0SSpace (r + s) I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => loweredCovDerivAlongVFraw (I := I) (M := M) g r s S X y)
    (loweredCovDerivAlongVFraw_contMDiff (I := I) (M := M) g r s S X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF

omit [CompactSpace M] [I.Boundaryless] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma loweredCovDerivAlongVF_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    loweredCovDerivAlongVF (I := I) (M := M) g r s S X y =
      loweredCovDerivAt (I := I) (M := M) g r s S y (X y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAlongVF_apply

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
lemma tensorInnerScalar_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I 𝓘(ℝ) ∞
      (tensorInnerScalar (I := I) (M := M) g r s W S) :=
  DifferentialGeometry.Tensor.tensorInnerPointwise_contMDiff_of_mdiff
    (I := I) (M := M) g r s W S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerScalar_contMDiff

omit [CompleteSpace E] in
theorem integral_tensorInner_covDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          + covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x))
          + tensorInnerScalar (I := I) (M := M) g r s W S x
            * divergenceG (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_tangentAction_add_smul_divergence_eq_zero
    (I := I) (M := M) g r s W S V
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_combined_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_combined_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_combined_eq_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_combined_eq_zero

omit [CompleteSpace E] in
theorem integral_tensorInner_covDeriv_split_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hWcov_int : _root_.MeasureTheory.Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s S x)))
      (riemannianVolumeMeasure (I := I) (M := M) g))
    (hScov_int : _root_.MeasureTheory.Integrable
      (fun x : M => covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s W x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x)))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s S V x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s S x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        - ∫ x, tensorInnerScalar (I := I) (M := M) g r s W S x
              * divergenceG (I := I) g V x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_tensorInner_covDeriv_integrationByParts (I := I) (M := M) g r s W S V
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W S)
    hWcov_int hScov_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_split_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_split_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_split_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_tensorInner_covDeriv_split_eq

end Elliptic
end Analysis
end DifferentialGeometry

end
