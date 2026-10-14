import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Lowering
import Submission.DifferentialGeometry.Analysis.Calculus.CompactSupportSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Bridge.Cross
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.LocalCongruence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

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

def LoweringIntertwinerRS (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∀ (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x),
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.LoweringIntertwinerRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.LoweringIntertwinerRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.LoweringIntertwinerRS ``Submission.DifferentialGeometry.Analysis.Elliptic.LoweringIntertwinerRS

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem loweringIntertwinerRS_holds (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    LoweringIntertwinerRS (I := I) (M := M) g r s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs (I := I) (M := M) g r s S x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_holds ``Submission.DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_holds

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem loweringIntertwinerRS_zero (g : SmoothRiemannianMetric I M) (s : ℕ) :
    LoweringIntertwinerRS (I := I) (M := M) g 0 s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_covariantTensor (I := I) (M := M) g s S x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.loweringIntertwinerRS_zero

def covDerivAlongVFrawRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace r s I y :=
  covApply (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFrawRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFrawRS (I := I) (M := M) g r s T B y =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlongVFrawRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covDerivAlongVFrawRS (I := I) (M := M) g r s T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawRS_contMDiff

def covDerivAlongVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFrawRS (I := I) (M := M) g r s T B y)
    (covDerivAlongVFrawRS_contMDiff (I := I) (M := M) g r s T B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFSectionRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionRS (I := I) (M := M) g r s T B y =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlongVFSectionRS_lowered_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s T y (B y)) := by
  rw [hint T y (B y)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_lowered_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_lowered_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_lowered_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionRS_lowered_eq

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma toModel_liftedTensorSection_covDerivAlongVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g r s
          (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSectionRS_lowered_eq (I := I) (M := M) g r s hint T B y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionRS ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionRS

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlongRS_covDerivAlongVFSectionRS_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionRS (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B) B y =
      tensorSecondCovDeriv (I := I) g r s
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g r s =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) from rfl]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongRS_covDerivAlongVFSectionRS_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongRS_covDerivAlongVFSectionRS_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongRS_covDerivAlongVFSectionRS_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongRS_covDerivAlongVFSectionRS_eq

def dirichletFormRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g r s b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g r s T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g r s T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g r s T b X +
          tensorCovDerivAt (I := I) (M := M) g r s T b Y := by
      change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g r s T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g r s T b X := by
      change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletFormRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletFormRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletFormRS ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormRS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma dirichletFormRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M)
    (X : TangentSpace I b) :
    dirichletFormRS (I := I) (M := M) g r s T v b X =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g r s T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_apply

def dirichletVFRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletFormRS (I := I) (M := M) g r s T v b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFRS ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFRS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma inner_dirichletVFRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletVFRS (I := I) (M := M) g r s T v b) X =
      dirichletFormRS (I := I) (M := M) g r s T v b X := by
  rw [dirichletVFRS]
  exact inner_metricSharp (I := I) g b (dirichletFormRS (I := I) (M := M) g r s T v b) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFRS ``Submission.DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFRS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma dirichletFormRS_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletFormRS (I := I) (M := M) g r s T v b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s T α j
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g r s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g r s T b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)) α hcov_section
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel (v.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g r s v.toSection α
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g r s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g r s T b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  have hbase_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletFormRS_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_chartBasis_component_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.dirichletFormRS_chartBasis_component_contMDiffOn target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma dirichletVFRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletVFRS (I := I) (M := M) g r s T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletFormRS (I := I) (M := M) g r s T v b)
    (fun α j => dirichletFormRS_chartBasis_component_contMDiffOn
      (I := I) (M := M) g r s T v α j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFRS_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFRS_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFRS_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFRS_contMDiff

def dirichletVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletVFRS (I := I) (M := M) g r s T v b)
    (dirichletVFRS_contMDiff (I := I) (M := M) g r s T v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma dirichletVFSectionRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    dirichletVFSectionRS (I := I) (M := M) g r s T v b =
      dirichletVFRS (I := I) (M := M) g r s T v b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionRS_apply

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma divergence_dirichletVFRS_summand_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletVFSectionRS (I := I) (M := M) g r s T v).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g r s
              (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionRS (I := I) (M := M) g r s T v with hZ_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection := by
    funext y
    rw [hZ_def, dirichletVFSectionRS_apply, inner_dirichletVFRS, dirichletFormRS_apply,
      tensorInnerScalar_apply, covDerivAlongVFSectionRS_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s
              (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B b)) := by
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g r s
              (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection) from by
      rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g r s
      (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s
          (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B)
        v.toSection b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B)
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint
        T.toSection B b,
        toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint
          v.toSection B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [hZ_def, dirichletVFSectionRS_apply, inner_dirichletVFRS, dirichletFormRS_apply]
  have hsecond := covDerivAlongRS_covDerivAlongVFSectionRS_eq (I := I) (M := M) g r s T.toSection B
    b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hsecond, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have haccel_eq :
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) =
        tensorCovDerivAt (I := I) (M := M) g r s T b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := rfl
  rw [haccel_eq]
  rw [show covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g r s T b ((B : ∀ y, TangentSpace I y) b) from rfl,
    show covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g r s v b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_summand_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_summand_eq target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I b) := by
    rw [Fintype.card_fin]
    rfl
  set tangentFrame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with htangentFrame_def
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    tangentFrame.map
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).toLinearEquiv with hframe_def
  have hframe_eq : ∀ i, frame i =
      tangentSpaceModelContinuousLinearEquiv (I := I) b
        (smoothOrthoFrame (I := I) g b i b) := by
    intro i
    rw [hframe_def, Module.Basis.map_apply, htangentFrame_def]
    change tangentSpaceModelContinuousLinearEquiv (I := I) b
        ((basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
          Fin (Module.finrank ℝ E) → TangentSpace I b) i) = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      modelInnerAt (I := I) (M := M) g b (frame i) (frame j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j, modelInnerAt_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g r s T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i, tangentSpaceModelContinuousLinearEquiv_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma divergence_dirichletVFRS_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) (b : M) :
    divergenceG (I := I) g (dirichletVFSectionRS (I := I) (M := M) g r s T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b
        + tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (dirichletVFSectionRS (I := I) (M := M) g r s T v) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_dirichletVFRS_summand_eq (I := I) (M := M) g r s hint T v b i)]
  rw [Finset.sum_add_distrib]
  rw [← tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag (I := I) (M := M) g r s T v b]
  rw [add_comm]
  congr 1
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s
    (fun y : M => T.toSection y) b]
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) from ?_]
  · rw [show (∑ i : Fin (Module.finrank ℝ E),
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g r s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b)) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g r s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ _ _ _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  · exact map_sum (tensorRSSpaceContinuousLinearEquiv (I := I) r s b)
      (fun i => tensorSecondCovDeriv (I := I) g r s
        (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y) b) Finset.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFRS_eq

omit [CompactSpace M] in
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      - tensorL2Inner (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionRS (I := I) (M := M) g r s T v with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) := by
    refine HasCompactSupport.mono (f := v.toFun) v.hasCompactSupport ?_
    intro b hb
    change v.toFun b ≠ 0
    intro hvb
    apply hb
    by_contra hZb
    have hpos := g.pos b (Z b) hZb
    have hinner : g.inner b (Z b) (Z b) = 0 := by
      rw [hZ_def, dirichletVFSectionRS_apply, inner_dirichletVFRS,
        dirichletFormRS_apply]
      change tensorInnerPointwise (I := I) (M := M) g r s b _ (v.toFun b) = 0
      rw [hvb, tensorInnerPointwise_zero_right]
    linarith
  have hdiv_zero : ∫ b, divergenceG (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergenceG (I := I) g Z b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b
        + tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
    intro b
    rw [hZ_def]
    exact divergence_dirichletVFRS_eq (I := I) (M := M) g r s hint T v b
  rw [_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b) μ :=
    tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s T v
  have hsecond_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) μ := by
    simpa only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply] using
      (rawTensorConnLapSmooth (I := I) g r s T).integrable_inner_cross v
  rw [_root_.MeasureTheory.integral_add hcross_int hsecond_int] at hdiv_zero
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (I := I) (M := M) g r s T v, ← hμ_def]
  rw [show tensorL2Inner (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b)) ∂μ from ?_]
  · linarith [hdiv_zero]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner

omit [CompactSpace M] in
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      - tensorL2Inner (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r s (loweringIntertwinerRS_holds (I := I) (M := M) g r s) T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs

omit [CompactSpace M] in
theorem integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ρ : C^∞⟮I, M; ℝ⟯) (T v : SmoothCcTensor g r s) :
    (∫ x, ρ x * tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T).toFun x) (v.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, ρ x * tensorCovDerivPointwiseInner (I := I) g r s T v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      ∫ x, tensorCovDerivCrossLeft (I := I) g r s ρ T v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let vρ := scalarSmul (I := I) g r s ρ v
  have hsplit : ∀ x, tensorCovDerivPointwiseInner (I := I) g r s T vρ x =
      ρ x * tensorCovDerivPointwiseInner (I := I) g r s T v x +
        tensorCovDerivCrossLeft (I := I) g r s ρ T v x := by
    intro x
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def,
      tensorCovDerivPointwiseInner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show vρ = scalarSmul (I := I) g r s ρ v from rfl,
      tensorCovDerivAt_scalarSmul]
    simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul,
      tensorInnerPointwise_add_right, tensorInnerPointwise_smul_right]
    change _ = _ + _ * (_ * tensorInnerPointwise (I := I) g r s x _
      (TensorRSSpace.toModel (v.toSection x)))
    ring
  have hcross_int : _root_.MeasureTheory.Integrable
      (tensorCovDerivCrossLeft (I := I) g r s ρ T v) μ := by
    have hpair := (covGrad (I := I) g r s T).integrable_inner_cross
      (prependCovGradSlot (I := I) g r s ρ v)
    refine hpair.congr (Filter.Eventually.of_forall (fun x => ?_))
    exact (tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
      (I := I) g r s ρ T v x).symm
  have hweighted_int : _root_.MeasureTheory.Integrable
      (fun x => ρ x * tensorCovDerivPointwiseInner (I := I) g r s T v x) μ := by
    have hsub := (tensorCovDerivPointwiseInner_integrable
      (I := I) g r s T vρ).sub hcross_int
    refine hsub.congr (Filter.Eventually.of_forall (fun x => ?_))
    change tensorCovDerivPointwiseInner (I := I) g r s T vρ x -
      tensorCovDerivCrossLeft (I := I) g r s ρ T v x = _
    rw [hsplit]
    ring
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) g r s T vρ
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner,
    tensorL2Inner] at hgreen
  have hpull : ∀ x, tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T).toFun x) (vρ.toFun x) =
      ρ x * tensorInnerPointwise (I := I) g r s x
        ((rawTensorConnLapSmooth (I := I) g r s T).toFun x) (v.toFun x) := by
    intro x
    rw [show vρ = scalarSmul (I := I) g r s ρ v from rfl,
      scalarSmul_toFun_apply, tensorInnerPointwise_smul_right]
  rw [_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
    _root_.MeasureTheory.integral_add hweighted_int hcross_int,
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpull)] at hgreen
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv

omit [CompactSpace M] in
theorem integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (T : SmoothCcTensor g r s) :
    (∫ x, χ x ^ 2 * tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T).toFun x) (T.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      2 * ∫ x, χ x * tensorCovDerivCrossLeft (I := I) g r s χ T T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hcross : ∀ x, tensorCovDerivCrossLeft (I := I) g r s (χ * χ) T T x =
      (2 * χ x) * tensorCovDerivCrossLeft (I := I) g r s χ T T x := by
    intro x
    rw [tensorCovDerivCrossLeft_def, tensorCovDerivCrossLeft_def,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show ((χ * χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
      (fun y => χ y * χ y) from rfl,
      DifferentialGeometry.mvfderiv_mul_at _
        (χ.contMDiff.mdifferentiableAt (by simp))
        (χ.contMDiff.mdifferentiableAt (by simp))]
    ring
  have hgreen := integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv
    (I := I) g r s (χ * χ) T T
  have hcross_integral : (∫ x, tensorCovDerivCrossLeft (I := I) g r s (χ * χ) T T x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      2 * ∫ x, χ x * tensorCovDerivCrossLeft (I := I) g r s χ T T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    rw [hcross]
    ring
  rw [hcross_integral] at hgreen
  simpa only [pow_two, ContMDiffMap.coe_mul, Pi.mul_apply] using hgreen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv

omit [CompactSpace M] in
theorem integral_weighted_rawTensorConnLap_eq_neg_covDeriv_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ρ : C^∞⟮I, M; ℝ⟯) (hρ : HasCompactSupport (ρ : M → ℝ))
    (T v : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    let cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    let grad := fun S x => covGradBundleEquiv (I := I) (M := M) r s x (cov S x)
    (∫ x, ρ x * tensorInnerPointwise (I := I) g r s x
      (TensorRSSpace.toModel (rawTensorConnLap (I := I) g r s T x))
      (TensorRSSpace.toModel (v x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, ρ x * tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (grad T x)) (TensorRSSpace.toModel (grad v x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      ∫ x, tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (grad T x))
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          ((mvfderiv (I := I) (ρ : M → ℝ) x).smulRight (v x))))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  dsimp only
  obtain ⟨Tc, hTc, hTeq⟩ := T.exists_compactly_supported_eq_nhdsSet hρ
  obtain ⟨vc, hvc, hveq⟩ := v.exists_compactly_supported_eq_nhdsSet hρ
  have hsupport (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
      (hS : IsCompact (closure {x : M | S x ≠ 0})) :
      HasCompactSupport (fun x => TensorRSSpace.toModel (S x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro x hx
    apply subset_closure
    intro hzero
    exact hx (by simp [hzero, TensorRSSpace.toModel_zero])
  let T₀ : SmoothCcTensor g r s := ⟨Tc, hsupport Tc hTc⟩
  let v₀ : SmoothCcTensor g r s := ⟨vc, hsupport vc hvc⟩
  have hcov (S Sc : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
      {x : M} (h : ∀ᶠ y in 𝓝 x, Sc y = S y) :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) Sc x =
        tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x := by
    exact tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s h
      (Sc.contMDiff.mdifferentiableAt (by simp))
      (S.contMDiff.mdifferentiableAt (by simp))
  have hlap : ∀ x, ρ x * tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T₀).toFun x) (v₀.toFun x) =
      ρ x * tensorInnerPointwise (I := I) g r s x
        (TensorRSSpace.toModel (rawTensorConnLap (I := I) g r s T x))
        (TensorRSSpace.toModel (v x)) := by
    intro x
    by_cases hx : x ∈ tsupport (ρ : M → ℝ)
    · have hT := (nhds_le_nhdsSet hx) hTeq
      have hv : ∀ᶠ y in 𝓝 x, vc y = v y := (nhds_le_nhdsSet hx) hveq
      simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]
      rw [rawTensorConnLap_congr_of_eventuallyEq (I := I) g r s Tc T hT]
      rw [show v₀.toSection x = v x from hv.self_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hgrad : ∀ x, ρ x * tensorCovDerivPointwiseInner (I := I) g r s T₀ v₀ x =
      ρ x * tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) T x)))
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) v x))) := by
    intro x
    by_cases hx : x ∈ tsupport (ρ : M → ℝ)
    · rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad,
        covGrad_toSection_apply, covGrad_toSection_apply]
      rw [hcov T Tc ((nhds_le_nhdsSet hx) hTeq),
        hcov v vc ((nhds_le_nhdsSet hx) hveq)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcross : ∀ x, tensorCovDerivCrossLeft (I := I) g r s ρ T₀ v₀ x =
      tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) T x)))
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          ((mvfderiv (I := I) (ρ : M → ℝ) x).smulRight (v x)))) := by
    intro x
    rw [tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad,
      covGrad_toSection_apply, prependCovGradSlot_toSection_apply]
    by_cases hx : x ∈ tsupport (ρ : M → ℝ)
    · rw [hcov T Tc ((nhds_le_nhdsSet hx) hTeq)]
      have hv : ∀ᶠ y in 𝓝 x, vc y = v y := (nhds_le_nhdsSet hx) hveq
      rw [show v₀.toSection x = v x from hv.self_of_nhds]
    · have hzero : mvfderiv (I := I) (ρ : M → ℝ) x = 0 := by
        have hev : (ρ : M → ℝ) =ᶠ[𝓝 x] (fun _ => 0) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (ρ : M → ℝ) x = 0 := by
          rw [hev.mfderiv_eq]
          exact mfderiv_const
        simp [mvfderiv, hmfd_zero]
      simp only [hzero, ContinuousLinearMap.zero_smulRight, map_zero,
        TensorRSSpace.toModel_zero, tensorInnerPointwise_zero_right]
  have hgreen := integral_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv
    (I := I) g r s ρ T₀ v₀
  rw [_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hlap),
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgrad),
    _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcross)] at hgreen
  exact hgreen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLap_eq_neg_covDeriv_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLap_eq_neg_covDeriv_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLap_eq_neg_covDeriv_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_weighted_rawTensorConnLap_eq_neg_covDeriv_of_hasCompactSupport

omit [CompactSpace M] in
private theorem integral_sq_weighted_rawTensorConnLapSmooth_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (T : SmoothCcTensor g r s)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x, χ x ^ 2 * tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T).toFun x) (T.toFun x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (ε - 1) * (∫ x, χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T T x
        ∂riemannianVolumeMeasure (I := I) (M := M) g) +
      ε⁻¹ * ∫ x, tensorInnerPointwise (I := I) g r (s + 1) x
        ((prependCovGradSlot (I := I) g r s χ T).toFun x)
        ((prependCovGradSlot (I := I) g r s χ T).toFun x)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let A := scalarSmul (I := I) g r (s + 1) χ (covGrad (I := I) g r s T)
  let B := prependCovGradSlot (I := I) g r s χ T
  have hAA (x : M) : tensorInnerPointwise (I := I) g r (s + 1) x
      (A.toFun x) (A.toFun x) =
      χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T T x := by
    dsimp only [A]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right,
      tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad]
    simp only [SmoothCcTensor.toFun_apply]
    ring
  have hAB (x : M) : tensorInnerPointwise (I := I) g r (s + 1) x
      (A.toFun x) (B.toFun x) =
      χ x * tensorCovDerivCrossLeft (I := I) g r s χ T T x := by
    dsimp only [A, B]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad]
    rfl
  have hAAint : _root_.MeasureTheory.Integrable
      (fun x => χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T T x) μ :=
    (A.integrable_inner_cross A).congr (Eventually.of_forall hAA)
  have hABint : _root_.MeasureTheory.Integrable
      (fun x => χ x * tensorCovDerivCrossLeft (I := I) g r s χ T T x) μ :=
    (A.integrable_inner_cross B).congr (Eventually.of_forall hAB)
  have hBBint := B.integrable_inner_cross B
  have hpoint (x : M) :
      -(2 * (χ x * tensorCovDerivCrossLeft (I := I) g r s χ T T x)) ≤
      ε * (χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T T x) +
        ε⁻¹ * tensorInnerPointwise (I := I) g r (s + 1) x (B.toFun x) (B.toFun x) := by
    rw [← hAA x, ← hAB x]
    have hnonneg := tensorInnerPointwise_nonneg (I := I) g r (s + 1) x
      (ε • A.toFun x + B.toFun x)
    rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
      tensorInnerPointwise_add_right, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right,
      tensorInnerPointwise_symm (I := I) g r (s + 1) x (B.toFun x) (A.toFun x)] at hnonneg
    have hdiv := div_nonneg hnonneg hε.le
    have halgebra (a b c : ℝ) :
        (ε * (ε * a) + ε * b + (ε * b + c)) / ε = ε * a + 2 * b + ε⁻¹ * c := by
      field_simp
      ring
    rw [halgebra] at hdiv
    linarith
  have hint := _root_.MeasureTheory.integral_mono (hABint.const_mul 2 |>.neg)
    ((hAAint.const_mul ε).add (hBBint.const_mul ε⁻¹)) hpoint
  simp only [Pi.neg_apply, Pi.add_apply] at hint
  rw [_root_.MeasureTheory.integral_neg, _root_.MeasureTheory.integral_const_mul,
    _root_.MeasureTheory.integral_add (hAAint.const_mul ε) (hBBint.const_mul ε⁻¹),
    _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul] at hint
  rw [integral_sq_weighted_rawTensorConnLapSmooth_eq_neg_covDeriv]
  dsimp only [μ, B] at hint
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLapSmooth_le target :: scope.openDecls } }

omit [CompactSpace M] in
theorem integral_sq_weighted_rawTensorConnLap_le_of_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    {ε : ℝ} (hε : 0 < ε) :
    let cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    let grad := fun x => covGradBundleEquiv (I := I) (M := M) r s x (cov T x)
    let cutoffGrad := fun x => covGradBundleEquiv (I := I) (M := M) r s x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight (T x))
    (∫ x, χ x ^ 2 * tensorInnerPointwise (I := I) g r s x
      (TensorRSSpace.toModel (rawTensorConnLap (I := I) g r s T x))
      (TensorRSSpace.toModel (T x))
      ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (ε - 1) * (∫ x, χ x ^ 2 * tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (grad x)) (TensorRSSpace.toModel (grad x))
        ∂riemannianVolumeMeasure (I := I) (M := M) g) +
      ε⁻¹ * ∫ x, tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (cutoffGrad x)) (TensorRSSpace.toModel (cutoffGrad x))
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  classical
  dsimp only
  obtain ⟨Tc, hTc, hTeq⟩ := T.exists_compactly_supported_eq_nhdsSet hχ
  have hsupport : HasCompactSupport (fun x => TensorRSSpace.toModel (Tc x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hTc
    intro x hx
    apply subset_closure
    intro hzero
    exact hx (by simp [hzero, TensorRSSpace.toModel_zero])
  let T₀ : SmoothCcTensor g r s := ⟨Tc, hsupport⟩
  have hcov {x : M} (hx : x ∈ tsupport (χ : M → ℝ)) :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) Tc x =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) T x := by
    exact tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s
      ((nhds_le_nhdsSet hx) hTeq)
      (Tc.contMDiff.mdifferentiableAt (by simp))
      (T.contMDiff.mdifferentiableAt (by simp))
  have hlap (x : M) : χ x ^ 2 * tensorInnerPointwise (I := I) g r s x
      ((rawTensorConnLapSmooth (I := I) g r s T₀).toFun x) (T₀.toFun x) =
      χ x ^ 2 * tensorInnerPointwise (I := I) g r s x
        (TensorRSSpace.toModel (rawTensorConnLap (I := I) g r s T x))
        (TensorRSSpace.toModel (T x)) := by
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have heq : ∀ᶠ y in 𝓝 x, Tc y = T y := (nhds_le_nhdsSet hx) hTeq
      simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]
      rw [rawTensorConnLap_congr_of_eventuallyEq (I := I) g r s Tc T heq]
      rw [show T₀.toSection x = T x from heq.self_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hgrad (x : M) :
      χ x ^ 2 * tensorCovDerivPointwiseInner (I := I) g r s T₀ T₀ x =
      χ x ^ 2 * tensorInnerPointwise (I := I) g r (s + 1) x
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) T x)))
        (TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) T x))) := by
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · rw [tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad,
        covGrad_toSection_apply, hcov hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcutoff (x : M) :
      (prependCovGradSlot (I := I) g r s χ T₀).toFun x =
      TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r s x
        ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight (T x))) := by
    rw [SmoothCcTensor.toFun_apply, prependCovGradSlot_toSection_apply]
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · have heq : ∀ᶠ y in 𝓝 x, Tc y = T y := (nhds_le_nhdsSet hx) hTeq
      rw [show T₀.toSection x = T x from heq.self_of_nhds]
    · have hzero : mvfderiv (I := I) (χ : M → ℝ) x = 0 := by
        have hev : (χ : M → ℝ) =ᶠ[𝓝 x] (fun _ => 0) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (χ : M → ℝ) x = 0 := by
          rw [hev.mfderiv_eq]
          exact mfderiv_const
        simp [mvfderiv, hmfd_zero]
      simp only [hzero, ContinuousLinearMap.zero_smulRight, map_zero]
  have hestimate := integral_sq_weighted_rawTensorConnLapSmooth_le g r s χ T₀ hε
  rw [_root_.MeasureTheory.integral_congr_ae (Eventually.of_forall hlap),
    _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall hgrad)] at hestimate
  simpa only [hcutoff] using hestimate

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLap_le_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLap_le_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLap_le_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_sq_weighted_rawTensorConnLap_le_of_hasCompactSupport


end Elliptic
end Analysis
end DifferentialGeometry

end
