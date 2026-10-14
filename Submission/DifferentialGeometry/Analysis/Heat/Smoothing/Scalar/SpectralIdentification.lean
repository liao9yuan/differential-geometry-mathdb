import Submission.DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.ClosedManifold
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.ScalarPath
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.HeatOutput
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Counting.Weyl
import Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.SmoothDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import Submission.DifferentialGeometry.Geometry.Connection.Realization.Tensor0SBridge
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Tensor.RSTensor.RankZero
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private lemma real_inner_eq_mul' (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  change RCLike.re ⟪a, b⟫_ℝ = a * b
  have h := RCLike.inner_apply a b
  have hrw : RCLike.re ⟪a, b⟫_ℝ = RCLike.re (b * (starRingEnd ℝ) a) := congrArg RCLike.re h
  rw [hrw]
  simp
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.real_inner_eq_mul'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.real_inner_eq_mul' target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothToLp_inner_eq_integral_mul
    (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ⟪smoothToLp (I := I) (M := M) g f, smoothToLp (I := I) (M := M) g h⟫_ℝ =
      ∫ x, f.toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [MeasureTheory.L2.inner_def]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) f.memLp_two,
    MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) h.memLp_two] with x hx₁ hx₂
  rw [smoothToLp_apply, smoothToLp_apply]
  rw [hx₁, hx₂]
  exact real_inner_eq_mul' (f.toFun x) (h.toFun x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.smoothToLp_inner_eq_integral_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.smoothToLp_inner_eq_integral_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.smoothToLp_inner_eq_integral_mul ``Submission.DifferentialGeometry.Analysis.HeatEquation.smoothToLp_inner_eq_integral_mul

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensorEval_zero_zero_scalar0
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
      (1 : ℝ))) Fin.elim0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x := by
  unfold TensorRSField.scalar0 TensorRSField.rs0
  simp only [SmoothCcTensor.toFun_apply, Tensor0SField.toScalarField]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensorEval_zero_zero_scalar0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.tensorEval_zero_zero_scalar0 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma separableForm_zero_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v : Fin 0 → E) (w : Fin 0 → E) :
    (separableFormAt (I := I) (M := M) g x 0) v w = 1 := by
  rw [separableFormAt_apply]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.separableForm_zero_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.separableForm_zero_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensorInnerPointwise_smooth_zero_zero
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x (S.toFun x) (T.toFun x) =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x := by
  unfold tensorInnerPointwise
  rw [tensorInnerPointwise_0s_zero_arity]
  rw [lowerAllUpperIndices_apply]
  rw [lowerAllUpperIndices_apply]
  have hS : (separableFormAt (I := I) (M := M) g x 0
        (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro w
    exact separableForm_zero_apply (I := I) (M := M) g x
      (fun i : Fin 0 => (Fin.elim0 : Fin 0 → E) (Fin.castAdd 0 i)) w
  rw [hS]
  change ((S.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
    (1 : ℝ))) Fin.elim0 *
      ((T.toFun x) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
        (1 : ℝ))) Fin.elim0 =
    TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g S x]
  rw [tensorEval_zero_zero_scalar0 (I := I) (M := M) g T x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensorInnerPointwise_smooth_zero_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.tensorInnerPointwise_smooth_zero_zero target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem tensorL2Inner_zero_zero_eq_integral_scalar0_mul
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    tensorL2Inner (I := I) (M := M) g 0 0 S.toFun T.toFun =
      ∫ x,
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x *
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) T.toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact tensorInnerPointwise_smooth_zero_zero (I := I) (M := M) g S T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.tensorL2Inner_zero_zero_eq_integral_scalar0_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.tensorL2Inner_zero_zero_eq_integral_scalar0_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.tensorL2Inner_zero_zero_eq_integral_scalar0_mul ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensorL2Inner_zero_zero_eq_integral_scalar0_mul

abbrev TensorEigenIdx00 (g : SmoothRiemannianMetric I M) :=
  Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.TensorEigenIdx00 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.TensorEigenIdx00"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.TensorEigenIdx00 ``Submission.DifferentialGeometry.Analysis.HeatEquation.TensorEigenIdx00

theorem eigenvectorSmooth00_eq_basis
    (g : SmoothRiemannianMetric I M) (j : TensorEigenIdx00 g) :
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) =
      tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j := by
  calc
    (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
        = tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
    _ = tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j :=
      (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) j).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.eigenvectorSmooth00_eq_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.eigenvectorSmooth00_eq_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.eigenvectorSmooth00_eq_basis ``Submission.DifferentialGeometry.Analysis.HeatEquation.eigenvectorSmooth00_eq_basis

theorem tensorL2Coeff_eigenvectorSmooth00
    (g : SmoothRiemannianMetric I M) [DecidableEq (TensorEigenIdx00 g)]
    (i j : TensorEigenIdx00 g) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        ((eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)) i =
      (if i = j then (1 : ℝ) else 0) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  change (b.repr (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) i) =
    if i = j then (1 : ℝ) else 0
  have hbj : (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g) = b j := by
    calc
      (eigenvectorSmooth g 0 0 j : TensorL2 0 0 g)
          = tensorResolventEigenbasisVec (I := I) (M := M) hc j :=
        eigenvectorSmooth_toL2 (I := I) (M := M) g 0 0 j
      _ = b j := by
        rw [hb_def]
        exact (tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M) hc j).symm
  rw [hbj]
  rw [HilbertBasis.repr_apply_apply]
  rw [real_inner_comm]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    simpa using horth j j
  · have hne : i ≠ j := fun hij => hji hij.symm
    rw [if_neg hne]
    exact Orthonormal.inner_eq_zero b.orthonormal hji

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.tensorL2Coeff_eigenvectorSmooth00 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.tensorL2Coeff_eigenvectorSmooth00"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.tensorL2Coeff_eigenvectorSmooth00 ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensorL2Coeff_eigenvectorSmooth00

theorem tensorEigen00_rawLap_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) :
    SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i)) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0 with hc_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc with hb_def
  apply b.repr.injective
  ext j
  change tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i))) j =
    tensorL2Coeff (I := I) (M := M) hc
      ((- TensorEigenIdx.lambda (I := I) (M := M) i) •
        SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j
  rw [rawLap_coeff (I := I) (M := M) g 0 hc (eigenvectorSmooth g 0 0 i) j]
  rw [tensorL2Coeff_smul (I := I) (M := M) hc
    (- TensorEigenIdx.lambda (I := I) (M := M) i)
    (SmoothCcTensor.toL2 (eigenvectorSmooth g 0 0 i)) j]
  let _ : DecidableEq (TensorEigenIdx00 g) := Classical.decEq _
  have hcoeff := tensorL2Coeff_eigenvectorSmooth00 (I := I) (M := M) g j i
  rw [← SmoothCcTensor.toL2_apply] at hcoeff
  rw [hcoeff]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.tensorEigen00_rawLap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.tensorEigen00_rawLap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.tensorEigen00_rawLap_eq ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensorEigen00_rawLap_eq

omit [SigmaCompactSpace M] [CompactSpace M] in
private lemma rawLapSection_eq_toRS0 (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) (x : M) :
    rawTensorConnLap g 0 0 (fun y : M => S.toSection y) x =
      ((Tensor0SNabla.tensor0Iso I M x).symm (laplacian (LeviCivita g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) x)).toRS0 := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  have hraw := rawLap_scalar (I := I) (M := M) g hf x
  have hlift := TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  rw [hlift] at hraw
  exact hraw

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.rawLapSection_eq_toRS0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.rawLapSection_eq_toRS0 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] in
private lemma laplacian_scalar0_smooth (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (laplacian (I := I) (LeviCivita (I := I) g) g
      (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection)) := by
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) :=
    TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  refine (Δ_g_contMDiff (I := I) g ⟨_, hf⟩).congr ?_
  intro x
  exact laplacian_levi_eq (I := I) g hf x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.laplacian_scalar0_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.laplacian_scalar0_smooth target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private lemma tensor0Iso_fromScalarField
    (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    Tensor0SNabla.tensor0Iso I M y (Tensor0SField.fromScalarField ∞ f hf y) = f y := by
  unfold Tensor0SField.fromScalarField Tensor0SNabla.tensor0Iso
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      (Tensor0SSpace.toModel (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I y) (f y))) = f y
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.tensor0Iso_fromScalarField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.tensor0Iso_fromScalarField target :: scope.openDecls } }

omit [SigmaCompactSpace M] [CompactSpace M] in
theorem scalar0_rawLap_eq_scalarLap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection x =
      laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection) x := by
  change Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
    laplacian (I := I) (LeviCivita (I := I) g) g
      (Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞)) S.toSection)) x
  have hpt : (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
      Tensor0SField.fromScalarField ∞
        (laplacian (I := I) (LeviCivita (I := I) g) g
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
        (laplacian_scalar0_smooth (I := I) (M := M) g S) x := by
    rw [TensorRSField.rs0_apply]
    rw [rawTensorConnLapSmooth_toSection_apply]
    rw [rawLapSection_eq_toRS0 (I := I) (M := M) g S x]
    rw [Tensor0SSpace.toRS0_apply]
    have hone : (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x)
        (Tensor0SField.one0 (n := (∞ : WithTop ℕ∞))
          (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) x) = 1 := by
      change Tensor0SSpace.toModel (Tensor0SField.one0 (n := (∞ : WithTop ℕ∞))
        (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) x) Fin.elim0 = 1
      exact Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) x Fin.elim0
    rw [hone, one_smul]
    symm
    apply (Tensor0SNabla.tensor0Iso I M x).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact tensor0Iso_fromScalarField
      (laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
      (laplacian_scalar0_smooth (I := I) (M := M) g S) x
  rw [show Tensor0SField.toScalarField ∞ (TensorRSField.rs0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 S).toSection) x =
      Tensor0SField.toScalarField ∞ (Tensor0SField.fromScalarField ∞
        (laplacian (I := I) (LeviCivita (I := I) g) g
          (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection))
        (laplacian_scalar0_smooth (I := I) (M := M) g S)) x by
    unfold Tensor0SField.toScalarField
    rw [hpt]]
  rw [Tensor0SField.toScalarField_fromScalarField]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.scalar0_rawLap_eq_scalarLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.scalar0_rawLap_eq_scalarLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.scalar0_rawLap_eq_scalarLap ``Submission.DifferentialGeometry.Analysis.HeatEquation.scalar0_rawLap_eq_scalarLap

theorem scalarEigen00_laplacian_eq
    (g : SmoothRiemannianMetric I M) (i : TensorEigenIdx00 g) (x : M) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection) x =
      - TensorEigenIdx.lambda (I := I) (M := M) i *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection x := by
  rw [← scalar0_rawLap_eq_scalarLap g (eigenvectorSmooth g 0 0 i) x]
  have hcc : rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i) =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) •
        eigenvectorSmooth g 0 0 i := by
    exact Integral.L2.SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq
      (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i))
      ((- TensorEigenIdx.lambda (I := I) (M := M) i) • eigenvectorSmooth g 0 0 i)
      (by
        rw [map_smul]
        exact tensorEigen00_rawLap_eq (I := I) (M := M) g i)
  calc
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth g 0 0 (eigenvectorSmooth g 0 0 i)).toSection x
        = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
            ((- TensorEigenIdx.lambda (I := I) (M := M) i) •
              eigenvectorSmooth g 0 0 i).toSection x := by
          rw [hcc]
    _ = - TensorEigenIdx.lambda (I := I) (M := M) i *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth g 0 0 i).toSection x := by
          simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.scalarEigen00_laplacian_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.scalarEigen00_laplacian_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.scalarEigen00_laplacian_eq ``Submission.DifferentialGeometry.Analysis.HeatEquation.scalarEigen00_laplacian_eq

end HeatEquation
end Analysis
end DifferentialGeometry

end
