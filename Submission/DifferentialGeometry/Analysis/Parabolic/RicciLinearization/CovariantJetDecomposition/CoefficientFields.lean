import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.JetTower
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.Covariant
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.TensorHilbertSobolev
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetricField
import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import Submission.DifferentialGeometry.Tensor.RSTensor.Smoothness.Parametric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix _root_.Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def linearizedRicciCovariantJetJointSmoothness (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ} : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 ((Φ p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ'))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciCovariantJetJointSmoothness_zero (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    {δ δ' : ℝ} :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun _ : ℝ => (0 : SmoothCcTensor g₀ r 2)) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciCovariantJetJointSmoothness]
  have heq : (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1
        (((fun _ : ℝ => (0 : SmoothCcTensor g₀ r 2)) p.2).toSection p.1)) =
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1
          (0 : Tensor0SBundle.TensorRSSpace r 2 I p.1)) := by
    funext p
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
    rw [show ((0 : SmoothCcTensor g₀ r 2).toSection : ContMDiffSection I _ ∞ _) = 0 from rfl]
    rfl
  rw [heq]
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
      (Bundle.zeroSection (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z)) :=
    Bundle.contMDiff_zeroSection ℝ (fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z)
  exact (hzero.comp contMDiff_fst).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciCovariantJetJointSmoothness_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun t => A t + B t) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add (I := I) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciCovariantJetJointSmoothness_smul (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (A : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun t => c • A t) (δ := δ) (δ' := δ') := by
  have hsmul := jointTotalSpaceRS_const_smul (I := I) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (A p.2).toSection p.1) hA
  refine hsmul.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciCovariantJetJointSmoothness_add_smul (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun t => A t + c • B t) (δ := δ) (δ' := δ') :=
  linearizedRicciCovariantJetJointSmoothness_add (I := I) (M := M) g₀ r A (fun t => c • B t) hA
    (linearizedRicciCovariantJetJointSmoothness_smul (I := I) (M := M) g₀ r c B hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_add_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciCovariantJetJointSmoothness_smul_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun t => c • A t + B t) (δ := δ) (δ' := δ') :=
  linearizedRicciCovariantJetJointSmoothness_add (I := I) (M := M) g₀ r (fun t => c • A t) B
    (linearizedRicciCovariantJetJointSmoothness_smul (I := I) (M := M) g₀ r c A hA) hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciCovariantJetJointSmoothness_smul_add

end NormedSpaceModel

section NormedTermFields

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

def linearizedRicciOrderZeroBaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    - ricciOrderZeroCurvCoeff (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciOrderZeroBaseCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciOrderZeroBaseCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciOrderZeroBaseCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciOrderZeroBaseCoeff

noncomputable def linearizedRicciFirstOrderFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x).comp
    (cometricDoubleTraceFib (I := I) g₁ 1 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem linearizedRicciFirstOrderFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) :
    linearizedRicciFirstOrderFib (I := I) g₀ g₁ x D =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          raisedKoszulFib (I := I) g₀ g₁ x)
        (cometricDoubleTraceFib (I := I) g₁ 1 x D) := by
  rw [linearizedRicciFirstOrderFib, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem linearizedRicciFirstOrderFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (linearizedRicciFirstOrderFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => linearizedRicciFirstOrderFib (I := I) g₀ g₁ x)
  intro Y
  have hdt : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) Y.contMDiff
  have hkos : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x)
          (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (raisedKoszulFib_contMDiff (I := I) g₀ g₁) hdt
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [linearizedRicciFirstOrderFib, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderFib_contMDiff

noncomputable def ricciFirstOrderKoszulCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciFirstOrderFib (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciFirstOrderFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
@[simp] theorem ricciFirstOrderKoszulCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciFirstOrderKoszulCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciFirstOrderFib (I := I) g₀ g₁ x) :=
        rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFirstOrderKoszulCoeff_toSection

def linearizedRicciFirstOrderBaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  ricciFirstOrderKoszulCoeff (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderBaseCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderBaseCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderBaseCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciFirstOrderBaseCoeff

def traceHessianSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianSlotPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianSlotPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianSlotPerm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianSlotPerm

noncomputable def domDomCongrFib (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          traceHessianSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem domDomCongrFib_apply (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFib (I := I) x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFib]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrFib_apply

noncomputable def traceHessianFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFib (I := I) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem traceHessianFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (traceHessianFib (I := I) g₁ x D) =
      modelDoubleTrace (E := E) 2 (cometricLmodel (I := I) g₁ x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, cometricDoubleTraceFib_toModel,
    domDomCongrFib_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_toModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_toModel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongr_section_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((Bundle.Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j)))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongr_section_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongr_section_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem traceHessianFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (traceHessianFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
      (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => traceHessianFib (I := I) g₁ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff (I := I) traceHessianSlotPerm (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianFib_contMDiff

noncomputable def traceHessianCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
      contMDiff_toFun := traceHessianFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
@[simp] theorem traceHessianCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_toSection

def linearizedRicciSecondOrderFieldLichnerowicz (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciSecondOrderFieldLichnerowicz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciSecondOrderFieldLichnerowicz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciSecondOrderFieldLichnerowicz ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciSecondOrderFieldLichnerowicz

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_eq_ccTensorBilin_local (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_ccTensorBilin_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_ccTensorBilin_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_ccTensorBilin_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_ccTensorBilin_local

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem traceHessianCoeff_apply_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₁) W)
          x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I
                x from
                W.toSection x) (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, operatorFieldApplication_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [traceHessianCoeff_toSection, traceHessianFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem cDualBasis_trace_basis_indep
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k) := by
  have hcoordB : ∀ k : Fin (Module.finrank ℝ E),
      B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis B) k)
  have hcoordFin : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k)
  rw [show (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap (B.coord k)) (B k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordB k])]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k))
            ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordFin k])]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  have h_cov : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) z
          = ∑ i : Fin (Module.finrank ℝ E), b.coord j (B i) * B.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) = z from
                B.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        F (LinearMap.toContinuousLinearMap (B.coord i)) (B i))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (B.coord i)) (B i)
                = F (LinearMap.toContinuousLinearMap (B.coord i))
                    (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) := by
                  rw [show (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) = B i from
                    b.sum_repr (B i)]
            _ = ∑ j : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
                    F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin (Module.finrank ℝ E), F
            (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
              LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E),
            F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cDualBasis_trace_basis_indep

end NormedTermFields

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
