import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantDerivativeQuadraticBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ConvexPerturbationC2
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.CovariantTwoTensor.FiberNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.SingleSlotFiberNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connectionDifferenceCovDerivBiContrFib deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff deTurckLieCovariantDerivativeInsertionFib deTurckLieCovariantDerivativeInsertionFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnectionDifferenceCovDeriv connectionDifference_pairing_mdiffAt connectionDifferenceCovDerivOp deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def deTurckLieConnectionDifferenceDerivCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieConnectionDifferenceDerivativeBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieConnectionDifferenceDerivCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connectionDifferenceCovDerivBiContrFib (I := I) g₁ g_bg x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_toSection

def deTurckLieCovariantDerivativeInsertionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieCovariantDerivativeInsertionFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieCovariantDerivativeInsertionField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieCovariantDerivativeInsertionFib (I := I) g₁ g_bg x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeInsertionField_toSection

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieConnectionDifferenceDerivCoeffField_toSection, deTurckLieCovariantDerivativeInsertionField_toSection,
    deTurckLieCoeffField_toSection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connectionDifference_cocycle (gA gB gC : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connectionDifference (I := I) gA gB x u v + PDE.DeTurck.connectionDifference (I := I) gB gC x u v =
      PDE.DeTurck.connectionDifference (I := I) gA gC x u v := by
  classical
  have hσ := smoothExtensionTangent_mdiff (I := I) x u x
  have hu : smoothExtensionTangent (I := I) x u x = u :=
    smoothExtensionTangent_eq (I := I) x u
  rw [← hu]
  rw [PDE.DeTurck.connectionDifference_apply (I := I) gA gB hσ v,
    PDE.DeTurck.connectionDifference_apply (I := I) gB gC hσ v,
    PDE.DeTurck.connectionDifference_apply (I := I) gA gC hσ v]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.connectionDifference_cocycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.connectionDifference_cocycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.connectionDifference_cocycle ``Submission.DifferentialGeometry.Analysis.Sobolev.connectionDifference_cocycle

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeA_backgroundSplit
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (X P Q : Π b : M, TangentSpace I b) (x : M)
    (hP : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (P b)) x)
    (hQ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Q b)) x) :
    deTurckConnectionDifferenceCovDeriv (I := I) g₁ g_bg X P Q x =
      covDerivConnectionDifference (I := I) g₀ g₁ X Q P x
        - covDerivConnectionDifference (I := I) g₀ g_bg X Q P x
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)) := by
  classical
  have hσ := connectionDifference_pairing_mdiffAt (I := I) g₁ g_bg hP hQ
  have hσB := connectionDifference_pairing_mdiffAt (I := I) g_bg g₀ hP hQ
  have hsum : (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) =
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b))
        + (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) := by
    funext b
    change PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b) =
      PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)
        + PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)
    exact (connectionDifference_cocycle (I := I) g₁ g_bg g₀ b (P b) (Q b)).symm
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b))
    (σ' := fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) hσ hσB
  have hsplit : (LeviCivita (I := I) g₀).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
    have h3 : (LeviCivita (I := I) g₀).toFun
        (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          + (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
      rw [hsum]
      have h2 := congrArg (fun L => L (X x)) hadd
      simpa using h2
    rw [h3]
    abel
  have hout' : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        = (LeviCivita (I := I) g₁).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          - (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := fun b : M =>
        PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) hσ (X x)
    rw [h]
    abel
  have hinnP' : (LeviCivita (I := I) g₁).toFun P x (X x)
      = (LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)
        = (LeviCivita (I := I) g₁).toFun P x (X x)
          - (LeviCivita (I := I) g₀).toFun P x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := P) hP (X x)
    rw [h]
    abel
  have hinnQ' : (LeviCivita (I := I) g₁).toFun Q x (X x)
      = (LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x) := by
    have h : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)
        = (LeviCivita (I := I) g₁).toFun Q x (X x)
          - (LeviCivita (I := I) g₀).toFun Q x (X x) :=
      PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀ (σ := Q) hQ (X x)
    rw [h]
    abel
  have hsplitT2 : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x)
      = PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x) (X x)) (Q x) := by
    rw [map_add]
    rfl
  have hsplitT3 : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x))
      = PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        + PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Q x) (X x)) :=
    map_add _ _ _
  have hT2c : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
      = PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := by
    have h := connectionDifference_cocycle (I := I) g₁ g_bg g₀ x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
    rw [← h]
    abel
  have hT3c : PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
      = PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x)) := by
    have h := connectionDifference_cocycle (I := I) g₁ g_bg g₀ x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
    rw [← h]
    abel
  have hA : covDerivConnectionDifference (I := I) g₀ g₁ X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  have hB : covDerivConnectionDifference (I := I) g₀ g_bg X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connectionDifference (I := I) g_bg g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connectionDifference (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₁).toFun P x (X x)) (Q x)
      - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₁).toFun Q x (X x)) = _
  rw [hout', hinnP', hinnQ', hsplitT2, hsplitT3, hT2c, hT3c, hsplit, hA, hB]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeA_backgroundSplit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeA_backgroundSplit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeA_backgroundSplit ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieCovariantDerivativeA_backgroundSplit

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    connectionDifferenceCovDerivOp (I := I) g₁ g_bg x v0 p q =
      covDerivConnectionDifference (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v0)
          (smoothExtensionTangent (I := I) x q)
          (smoothExtensionTangent (I := I) x p) x
        - covDerivConnectionDifference (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v0)
            (smoothExtensionTangent (I := I) x q)
            (smoothExtensionTangent (I := I) x p) x
        + PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x p q) v0
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p v0) q
        - PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x p
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0) := by
  rw [deTurckLieConnectionDifferenceDerivativeCovKernel_apply_extend (I := I) g₁ g_bg x v0 p q]
  rw [deTurckLieCovariantDerivativeA_backgroundSplit (I := I) g₀ g₁ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x p)
    (smoothExtensionTangent (I := I) x q) x
    (smoothExtensionTangent_mdiff (I := I) x p x)
    (smoothExtensionTangent_mdiff (I := I) x q x)]
  simp only [smoothExtensionTangent_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit ``Submission.DifferentialGeometry.Analysis.Sobolev.deTurckLieConnectionDifferenceDerivativeCovKernel_backgroundSplit

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPath convexPerturbation metricPerturbationPath_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one metricPerturbationPathDomain)
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
  (metric_inner_cauchy_schwarz_sq)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connectionDifference_gFibreNorm_le_iteratedCovGrad_of_lt_one deTurckLieConnectionDifferenceDerivativeBiContrFibFixedFrame_toModel)
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnectionDifference_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem abs_metric_inner_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  have h2 := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x u v
  have habs : |g.inner x u v| = Real.sqrt ((g.inner x u v) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_mul (metric_inner_self_nonneg (I := I) (M := M) g x u)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.abs_metric_inner_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.abs_metric_inner_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.abs_metric_inner_le ``Submission.DifferentialGeometry.Analysis.Sobolev.abs_metric_inner_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_metric_inner_add_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u + v) (u + v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have huu := metric_inner_self_nonneg (I := I) (M := M) g x u
  have hvv := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hexp : g.inner x (u + v) (u + v) =
      g.inner x u u + g.inner x u v + (g.inner x v u + g.inner x v v) := by
    simp only [map_add, add_apply]
    ring
  have hsymm : g.inner x v u = g.inner x u v := g.symm x v u
  have hcs := abs_metric_inner_le (I := I) (M := M) g x u v
  have hsq : g.inner x (u + v) (u + v) ≤
      (Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v)) ^ 2 := by
    rw [hexp, hsymm]
    have h1 := Real.sq_sqrt huu
    have h2 := Real.sq_sqrt hvv
    have h3 := abs_le.mp hcs
    nlinarith [h3.2, Real.sqrt_nonneg (g.inner x u u), Real.sqrt_nonneg (g.inner x v v)]
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_add_le ``Submission.DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_add_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_metric_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u - v) (u - v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have hneg : g.inner x (-v) (-v) = g.inner x v v := by
    simp only [map_neg, neg_apply, neg_neg]
  have h := sqrt_metric_inner_add_le (I := I) (M := M) g x u (-v)
  rw [← sub_eq_add_neg] at h
  rw [hneg] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_sub_le ``Submission.DifferentialGeometry.Analysis.Sobolev.sqrt_metric_inner_sub_le

end DifferentialGeometry.Analysis.Sobolev

end
