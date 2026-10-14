import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma mvfderiv_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    mvfderiv (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvfderiv_apply_scalar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvfderiv_apply_scalar target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma tensorCovDerivAt_zero_dir
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivAt (I := I) (M := M) g r s S x (0 : E) = 0 := by
  rw [tensorCovDerivAt_def]
  exact ContinuousLinearMap.map_zero _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_zero_dir
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_zero_dir target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma gradFun_eq_gramInv_sum
    (g : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    gradFun (I := I) g (ζ : M → ℝ) x =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
  classical
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  set rhs : TangentSpace I x :=
    ∑ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        Ginv i j * mvfderiv (I := I) (ζ : M → ℝ) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) with hrhs
  refine (DifferentialGeometry.Geometry.Operator.metricFlatLinear_injective
    (I := I) g x ?_).symm
  set tangentBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toLinearEquiv with
        htangentBasis
  refine tangentBasis.ext ?_
  intro k
  rw [htangentBasis, Module.Basis.map_apply]
  have hgrad_k : DifferentialGeometry.Geometry.Operator.metricFlatLinear (I := I) g x
      (gradFun (I := I) g (ζ : M → ℝ) x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) =
        mvfderiv (I := I) (ζ : M → ℝ) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) := by
    rw [DifferentialGeometry.Geometry.Operator.metricFlatLinear_apply, mvfderiv_apply_scalar]
    exact inner_gradFun (I := I) g (ζ : M → ℝ) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))
  have hrhs_k : DifferentialGeometry.Geometry.Operator.metricFlatLinear (I := I) g x rhs
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          Ginv i j * mvfderiv (I := I) (ζ : M → ℝ) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) *
          gramMatrixAt (I := I) (M := M) g x j k := by
    rw [DifferentialGeometry.Geometry.Operator.metricFlatLinear_apply, hrhs]
    rw [map_sum, sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_apply, smul_eq_mul, gramMatrixAt_apply, modelInnerAt_apply]
  have hgram : ∀ i : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i k := by
    intro i
    have hmul := gramMatrixAt_inv_mul_self (I := I) (M := M) g x
    have hentry := congrFun (congrFun hmul i) k
    rw [Matrix.mul_apply] at hentry
    rw [hGinv]
    exact hentry
  calc DifferentialGeometry.Geometry.Operator.metricFlatLinear (I := I) g x rhs
         ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
           ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k))
      = ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            Ginv i j *
              mvfderiv (I := I) (ζ : M → ℝ) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) *
            gramMatrixAt (I := I) (M := M) g x j k := hrhs_k
    _ = ∑ j : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
              (Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = ∑ i : Fin (Module.finrank ℝ E),
          mvfderiv (I := I) (ζ : M → ℝ) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
            (∑ j : Fin (Module.finrank ℝ E),
              Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (Module.finrank ℝ E),
          mvfderiv (I := I) (ζ : M → ℝ) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
            (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
              i k := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hgram i]
    _ = mvfderiv (I := I) (ζ : M → ℝ) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) := by
        rw [Finset.sum_eq_single k]
        · rw [Matrix.one_apply_eq, mul_one]
        · intro i _ hik
          rw [Matrix.one_apply_ne hik, _root_.MulZeroClass.mul_zero]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
    _ = DifferentialGeometry.Geometry.Operator.metricFlatLinear (I := I) g x
          (gradFun (I := I) g (ζ : M → ℝ) x)
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)) :=
        hgrad_k.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradFun_eq_gramInv_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradFun_eq_gramInv_sum target :: scope.openDecls } }

private noncomputable def covDerivHomSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covDerivHomSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : TangentSpace I x) :
    covDerivHomSection (I := I) (M := M) g r s S x v =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  rw [tensorCovDerivAt_def,
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covDerivHomSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covDerivHomSection (I := I) (M := M) g r s S x⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    with hcovLC
  have hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => S.toSection y) x⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivHomSection_contMDiff target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covDerivAlong_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, tensorCovDerivAt (I := I) (M := M) g r s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x))⟩ :
          _root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
            fun y : M => TensorRSSpace r s I y)) := by
  have hϕ := covDerivHomSection_contMDiff (I := I) (M := M) g r s S
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, V x⟩ :
        TotalSpace E (TangentSpace I : M → Type _))) :=
    V.contMDiff
  simpa only [covDerivHomSection_apply] using ContMDiff.clm_bundle_apply hϕ hv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_section_contMDiff target :: scope.openDecls } }

private noncomputable def covDerivAlongSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModelNormedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModelNormedSpace r s
  letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundleTopology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundleFiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I :=
    tensorRSBundle_smooth ∞ r s
  (ContMDiffSection.mk
      (fun x : M => tensorCovDerivAt (I := I) (M := M) g r s S x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x)))
      (covDerivAlong_section_contMDiff (I := I) (M := M) g r s S V) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covDerivAlongSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivAlongSection (I := I) (M := M) g r s S V x =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covDerivAlongSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∉ tsupport S.toFun) :
    TensorRSSpace.toModel
      (covDerivAlongSection (I := I) (M := M) g r s S V x) = 0 := by
  rw [covDerivAlongSection_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hx
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x)),
    TensorRSSpace.toModel_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_toModel_eq_zero_off_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_toModel_eq_zero_off_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma covDerivAlongSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covDerivAlongSection (I := I) (M := M) g r s S V x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covDerivAlongSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s S V hxnot)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongSection_hasCompactSupport target :: scope.openDecls } }

noncomputable def covDerivAlong
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    SmoothCcTensor g r s where
  toSection := covDerivAlongSection (I := I) (M := M) g r s S V
  hasCompactSupport :=
    covDerivAlongSection_hasCompactSupport (I := I) (M := M) g r s S V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlong_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toSection_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlong_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x))) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlong_toSection_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toFun_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_toFun_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlong_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    tsupport (covDerivAlong (I := I) (M := M) g r s S V).toFun ⊆
      tsupport S.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  rw [covDerivAlong_toFun_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hxnot
      (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x)),
    TensorRSSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlong_tsupport_subset

noncomputable def covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    SmoothCcTensor g r s :=
  covDerivAlong (I := I) (M := M) g r s S
    (gradG (I := I) g ζ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlongGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (gradFun (I := I) g (ζ : M → ℝ) x)) := by
  rw [covDerivAlongGrad, covDerivAlong_toSection_apply, grad_g_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toSection_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlongGrad_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (gradFun (I := I) g (ζ : M → ℝ) x))) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlongGrad_toSection_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toFun_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_toFun_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covDerivAlongGrad_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    tsupport (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  have hgrad_zero : gradFun (I := I) g (ζ : M → ℝ) x = (0 : TangentSpace I x) := by
    apply gradFun_eq_zero_of_eventuallyEq_zero
    have h_open : IsOpen (tsupport (ζ : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    filter_upwards [h_open.mem_nhds hxnot] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  rw [covDerivAlongGrad_toFun_apply, hgrad_zero,
    map_zero,
    tensorCovDerivAt_zero_dir (I := I) (M := M) g r s S x,
    TensorRSSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivAlongGrad_tsupport_subset

private noncomputable def tensorInnerPointwiseRightHom
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E →+ ℝ where
  toFun := fun T => tensorInnerPointwise (I := I) (M := M) g r s x A T
  map_zero' := tensorInnerPointwise_zero_right (I := I) (M := M) g r s x A
  map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g r s x A

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorInnerPointwiseRightHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorInnerPointwiseRightHom target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma tensorInnerPointwise_sum_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E)
    (T : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x A (T i j) := by
  classical
  have h := map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun i => ∑ j : Fin (Module.finrank ℝ E), T i j) Finset.univ
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) from rfl]
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun j => T i j) Finset.univ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorInnerPointwise_sum_sum_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorInnerPointwise_sum_sum_right target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma gramInv_sum_covDeriv_eq_covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
            TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) =
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x := by
  classical
  set D : E →L[ℝ] TensorRSSpace r s I x :=
    (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun y : M => S.toSection y) x).comp
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap
      with hD
  set toM : TensorRSSpace r s I x ≃L[ℝ] TensorRSModel r s ℝ E :=
    tensorRSSpaceContinuousLinearEquiv (I := I) r s x with htoM
  have hcov : ∀ v : E,
      tensorCovDerivAt (I := I) (M := M) g r s S x v = D v := fun v => rfl
  have hgoal_rhs :
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
        toM (D (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (gradFun (I := I) g (ζ : M → ℝ) x))) := by
    rw [covDerivAlongGrad_toFun_apply, hcov]
    rfl
  rw [hgoal_rhs]
  have htoModel_cov : ∀ j : Fin (Module.finrank ℝ E),
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) =
        toM (D ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
    intro j
    rw [hcov]
    rfl
  have hlhs :
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mvfderiv (I := I) (ζ : M → ℝ) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) =
        toM (D (∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mvfderiv (I := I) (ζ : M → ℝ) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mvfderiv (I := I) (ζ : M → ℝ) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                mvfderiv (I := I) (ζ : M → ℝ) x
                  ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
                toM (D ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [htoModel_cov j]
      _ = ∑ j : Fin (Module.finrank ℝ E),
            toM (D ((∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                mvfderiv (I := I) (ζ : M → ℝ) x
                  ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul D, map_smul toM, Finset.sum_smul]
      _ = toM (D (∑ j : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                mvfderiv (I := I) (ζ : M → ℝ) x
                  ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
          rw [map_sum D, map_sum toM]
  rw [hlhs]
  have hgradModel := congrArg
    (tangentSpaceModelContinuousLinearEquiv (I := I) x)
    (gradFun_eq_gramInv_sum (I := I) g ζ x)
  simp only [map_sum, map_smul,
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).apply_symm_apply]
    at hgradModel
  rw [← hgradModel]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gramInv_sum_covDeriv_eq_covDerivAlongGrad
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gramInv_sum_covDeriv_eq_covDerivAlongGrad target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (w.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x) := by
  classical
  rw [tensorCovDerivCrossRight_def]
  rw [← gramInv_sum_covDeriv_eq_covDerivAlongGrad (I := I) (M := M) g r s ζ S x]
  rw [tensorInnerPointwise_sum_sum_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tensorInnerPointwise_smul_right]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovDerivCrossRight_integral_eq_innerLow
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪(w : TensorL2 r s g),
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ :
          SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ := by
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def w
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ),
    tensorL2Inner]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w S x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_innerLow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_innerLow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_innerLow ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_innerLow

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_integral_eq_chartPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α) w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (w : TensorL2 r s g) α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s
                (covDerivAlongGrad (I := I) (M := M) g r s S
                  (chartAtlasPOU I M α)) α Q y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α) w S]
  exact tensorL2Inner_cutoff_chartKernelSupported_pull (I := I) (M := M)
    g r s α (w : TensorL2 r s g)
    (covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α))
    (covDerivAlongGrad_tsupport_subset (I := I) (M := M) g r s S
      (chartAtlasPOU I M α))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_chartPull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_chartPull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_chartPull ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_eq_chartPull

theorem tensorL2_eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g))
      _root_.Filter.atTop
      (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))) := by
  have h_clm :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  refine h_clm.congr ?_
  intro n
  rw [Function.comp_apply,
    TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2_eigenvectorSmoothApprox_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2_eigenvectorSmoothApprox_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2_eigenvectorSmoothApprox_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2_eigenvectorSmoothApprox_tendsto

def crossRightLimitComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent

theorem crossRightComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)
        α P)
      _root_.Filter.atTop
      (𝓝 (crossRightLimitComponent (I := I) (M := M)
        g r s i α P)) := by
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s
        α P).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightComponent_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightComponent_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightComponent_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightComponent_tendsto

theorem tensorCovDerivCrossRight_integral_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (S : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      _root_.Filter.atTop
      (𝓝 (⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
            SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ)) := by
  have h_clm :=
    ((innerSL ℝ
        ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
          SmoothCcTensor g r s) :
          TensorL2 r s g)).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, innerSL_apply_apply] at h_clm
  rw [real_inner_comm]
  refine h_clm.congr ?_
  intro n
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor S,
    real_inner_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_integral_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
