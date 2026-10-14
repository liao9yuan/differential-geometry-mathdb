import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SecondGradient
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CorrectionFields.PointwiseBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.ConnectionBicontraction
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.JetIntegral
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Curvature.DecompositionMonomialBounds
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.Decomposition
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.FamilySmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

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


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covariantDerivativeTermField_eq_deTurckLieConnectionDifferenceDerivativeCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCovariantDerivativeTermField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_eq_deTurckLieConnectionDifferenceDerivativeCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_eq_deTurckLieConnectionDifferenceDerivativeCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_eq_deTurckLieConnectionDifferenceDerivativeCoeffField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_eq_deTurckLieConnectionDifferenceDerivativeCoeffField


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endomorphismTermField_eq_deTurckLieCovariantDerivativeInsertionCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_eq_deTurckLieCovariantDerivativeInsertionCoeffField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_eq_deTurckLieCovariantDerivativeInsertionCoeffField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_eq_deTurckLieCovariantDerivativeInsertionCoeffField ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_eq_deTurckLieCovariantDerivativeInsertionCoeffField


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem covariantJetJointSmoothness_add_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_add_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_add_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_add_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_add_local


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem covariantJetJointSmoothness_sub_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := r) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_sub_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_sub_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_sub_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantJetJointSmoothness_sub_local


omit [SigmaCompactSpace M] in
theorem covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovariantDerivativeTermField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have h := deTurckLieConnectionDifferenceDerivativeBiContrFib_metricPerturbationPath_jointContMDiffOn (I := I) (M := M)
    g₀ T 0 hδ hδZ g_bg
  refine h.congr (fun p _ => ?_)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness


omit [SigmaCompactSpace M] in
theorem endomorphismTermField_metricPerturbationPath_covariantJetJointSmoothness
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ 2
      (fun s => deTurckLieEndoTermField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have hC := deTurckLieCoeffField_metricPerturbationPath_jointContMDiff (I := I)
    g₀ T 0 hδ hδZ g_bg
  have hA := covariantDerivativeTermField_metricPerturbationPath_covariantJetJointSmoothness (I := I) (M := M)
    g₀ T hδ hδZ g_bg
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 2) (s := 2)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    hC hA
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  change (deTurckLieEndoTermField (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1 =
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
      - (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
  have hsplit : deTurckLieEndoTermField (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg
        - deTurckLieCovariantDerivativeTermField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (deTurckLieCoeffField_eq_covDerivTerm_add_endoTerm (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ p.2) g_bg).symm
  rw [hsplit, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_metricPerturbationPath_covariantJetJointSmoothness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_metricPerturbationPath_covariantJetJointSmoothness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_metricPerturbationPath_covariantJetJointSmoothness ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.endomorphismTermField_metricPerturbationPath_covariantJetJointSmoothness


omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGrad_riemannianFiberNormSq_bound (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_iteratedCovGrad_riemannianFiberNormSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_iteratedCovGrad_riemannianFiberNormSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_iteratedCovGrad_riemannianFiberNormSq_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_iteratedCovGrad_riemannianFiberNormSq_bound

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma palatiniRiemannianFiberNormSq_iteratedCovGrad_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniRiemannianFiberNormSq_iteratedCovGrad_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniRiemannianFiberNormSq_iteratedCovGrad_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniRiemannianFiberNormSq_iteratedCovGrad_add_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniRiemannianFiberNormSq_iteratedCovGrad_add_le

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma palatiniOperatorFieldComposition_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ - ccOperatorFieldComp (I := I) (M := M) g a
        b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁).toSection x -
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [sub_apply]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOperatorFieldComposition_sub_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOperatorFieldComposition_sub_right target :: scope.openDecls } }

private def palatiniVFSec (g₁ gA gB : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ gA : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) -
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniVFSec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniVFSec target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma palatiniVFSec_apply (g₁ gA gB : SmoothRiemannianMetric I M) (b : M) :
    palatiniVFSec (I := I) (M := M) g₁ gA gB b =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b -
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b := by
  rw [palatiniVFSec, ContMDiffSection.coe_sub, Pi.sub_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniVFSec_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniVFSec_apply target :: scope.openDecls } }

def palatiniXiFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₀ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniXiFix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniXiFix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniXiFix ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniXiFix

private def palatiniOmegaAtConnectionMetric (g₀ g₁ gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gc)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric target :: scope.openDecls } }

def palatiniOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (palatiniXiFix (I := I) (M := M) g₀ g_bg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma palatiniOmega_eq_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    palatiniOmega (I := I) (M := M) g₀ g₁ g_bg =
      palatiniOmegaAtConnectionMetric (I := I) (M := M) g₀ g₁ g_bg - palatiniOmegaAtConnectionMetric (I := I) (M := M) g₀ g₁ g₀ := by
  rw [palatiniOmegaAtConnectionMetric, palatiniOmegaAtConnectionMetric, ← palatiniOperatorFieldComposition_sub_right, palatiniOmega]
  congr 1
  rw [palatiniXiFix]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_eq_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_eq_sub target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma palatiniUnitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply, Tensor0SSpace.toModel_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_sub

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma palatiniUnitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    add_apply, Tensor0SSpace.toModel_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitModel_add

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma palatiniConnectionDifferenceLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricLoweredConnectionDifferenceField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma palatiniConnectionDifferenceLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x m =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [palatiniConnectionDifferenceLoweredCc_unitModel]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniConnectionDifferenceLoweredCc_unitModel_apply

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma unitModel_metricLoweredConnectionDifferenceCoefficient_sub_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gc) x m =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ gc x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [palatiniUnitModel_sub, sub_apply,
    palatiniConnectionDifferenceLoweredCc_unitModel_apply, palatiniConnectionDifferenceLoweredCc_unitModel_apply]
  rw [show g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) -
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) gc g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)) -
          PDE.DeTurck.connectionDifference (I := I) gc g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) from by
    rw [map_sub, sub_apply]]
  rw [connectionDifference_endpoint_cocycle (I := I) g₀ g₁ gc x
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1))]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_metricLoweredConnectionDifferenceCoefficient_sub_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_metricLoweredConnectionDifferenceCoefficient_sub_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma palatiniOmegaAtConnectionMetric_toSection_unit (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (palatiniOmegaAtConnectionMetric (I := I) (M := M) g₀ g₁ gc).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gc).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [palatiniOmegaAtConnectionMetric, operatorFieldComposition_toSection]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric_toSection_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric_toSection_unit target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma palatiniOmegaAtConnectionMetric_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (palatiniOmegaAtConnectionMetric (I := I) (M := M) g₀ g₁ gc) x
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
      g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) z := by
  classical
  rw [unitModel, palatiniOmegaAtConnectionMetric_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gc).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpaceContinuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x))
          (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z)]
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g₁ x i x))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z))]
    have hm : Tensor0SSpace.toModel D
        (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₁ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₁ x i x))
            (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z))) =
        unitModel (I := I) (M := M) g₀ 3
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gc) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₁ x i x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₁ x i x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x z] := by
      rw [unitModel, ← hD]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hm, unitModel_metricLoweredConnectionDifferenceCoefficient_sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, ContinuousLinearEquiv.symm_apply_apply]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connectionDifference (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, sum_apply]]
  rw [← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gc x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmegaAtConnectionMetric_unitModel_apply target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma palatiniOmega_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
      g₀.inner x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) z := by
  rw [palatiniOmega_eq_sub, palatiniUnitModel_sub, sub_apply,
    palatiniOmegaAtConnectionMetric_unitModel_apply, palatiniOmegaAtConnectionMetric_unitModel_apply, palatiniVFSec_apply]
  rw [map_sub, sub_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_unitModel_apply target :: scope.openDecls } }

def palatiniAlphaA (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA

def palatiniCA (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCA then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCA"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCA ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCA

def palatiniAlphaB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2 (palatiniCA (I := I) (M := M) g₀ g₁)
    (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB

def palatiniAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  palatiniAlphaA (I := I) (M := M) g₀ g₁ g_bg + palatiniAlphaB (I := I) (M := M) g₀ g₁ g_bg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlpha then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlpha"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlpha ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlpha

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma palatiniTensor0SCovDeriv01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          (fun i => Fin.elim0 i)) =
      directionalDeriv (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b)
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
                (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v))
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
              (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
              (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniTensor0SCovDeriv01_consEval_leibnizDefect
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniTensor0SCovDeriv01_consEval_leibnizDefect target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma palatiniOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    change unitModel (I := I) (M := M) g₀ 1
        (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) x (fun _ : Fin 1 => m 0) = _
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      palatiniOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
  rw [hL]
  have hR : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    rw [Tensor0SSpace.toModel_apply_model_vector, cotangentToDual_apply]
  rw [hR, cotangentToDual_g0FlatCLM]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_toSection_unit_eq_flat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniOmega_toSection_unit_eq_flat target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma palatiniUnitEvalSection_bdOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      g₀.inner b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) z := by
  rw [unitEvalSection_apply]
  rw [show (unitZeroSec (I := I) (M := M) b) = unitTensor (I := I) (M := M) b from rfl]
  rw [palatiniOmega_toSection_unit_eq_flat]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
          (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) b z)
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitEvalSection_bdOmega_toModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniUnitEvalSection_bdOmega_toModel target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private lemma palatiniAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (palatiniAlphaA (I := I) (M := M) g₀ g₁ g_bg) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun
          (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [palatiniAlphaA, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
      tangentSpaceModelContinuousLinearEquiv (I := I) x w] : Fin 2 → E)
      ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x w,
        tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
    funext i; fin_cases i <;> simp]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x)
    ![tangentSpaceModelContinuousLinearEquiv (I := I) x w,
      tangentSpaceModelContinuousLinearEquiv (I := I) x u]]
  rw [show (![tangentSpaceModelContinuousLinearEquiv (I := I) x w,
      tangentSpaceModelContinuousLinearEquiv (I := I) x u] : Fin 2 → E) 0 =
      tangentSpaceModelContinuousLinearEquiv (I := I) x w from rfl]
  rw [show Matrix.vecTail
      (![tangentSpaceModelContinuousLinearEquiv (I := I) x w,
        tangentSpaceModelContinuousLinearEquiv (I := I) x u] : Fin 2 → E) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x w)]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq (I := I) (M := M) g₀ 1
    (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (![tangentSpaceModelContinuousLinearEquiv (I := I) x u] : Fin 1 → E) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
        (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [palatiniTensor0SCovDeriv01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
          (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) (Y b)) := by
    funext b
    exact palatiniUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDeriv_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) (W := fun b => Y b)
    (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀).contMDiff Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (palatiniOmega (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w))
        (fun i => Fin.elim0 i)) =
      g₀.inner x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    palatiniUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaA_unitModel_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma palatiniInterior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D)
        (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (w k)) =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniInterior_product_toModel_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniInterior_product_toModel_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniInterior_product_toModel_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniInterior_product_toModel_eval

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma palatiniAlphaB_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (palatiniAlphaB (I := I) (M := M) g₀ g₁ g_bg) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) u := by
  classical
  rw [unitModel, palatiniAlphaB, operatorFieldComposition_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [palatiniOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [palatiniCA, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x)]
  have hinterior := palatiniInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
    (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) D ![u, w]
  change Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (1 + 1) x
        (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) D)
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x w] = _ at hinterior
  rw [hinterior]
  have hDm : Tensor0SSpace.toModel D
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x))
        (fun k : Fin 2 => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![u, w] : Fin 2 → TangentSpace I x) k))) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x),
          tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] := by
    rw [unitModel, ← hD]
    rfl
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x
        (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x),
      tangentSpaceModelContinuousLinearEquiv (I := I) x u,
      tangentSpaceModelContinuousLinearEquiv (I := I) x w] : Fin 3 → E)
        ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x),
        tangentSpaceModelContinuousLinearEquiv (I := I) x w,
        tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]]
  rw [palatiniConnectionDifferenceLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniAlphaB_unitModel_apply target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma palatiniLeviCivita_toFun_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    (LeviCivita (I := I) g₀).toFun (fun b => A b - B b) x w =
      (LeviCivita (I := I) g₀).toFun (fun b => A b) x w -
        (LeviCivita (I := I) g₀).toFun (fun b => B b) x w := by
  have hsub : (fun b : M => A b - B b) =
      (fun b : M => A b) + (fun b : M => ((-1 : ℝ) • B) b) := by
    funext b
    rw [Pi.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply, neg_one_smul,
      sub_eq_add_neg]
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => A b) (σ' := fun b : M => ((-1 : ℝ) • B) b) (x := x)
    (A.mdifferentiableAt (x := x)) (((-1 : ℝ) • B).mdifferentiableAt (x := x))
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => B b) (a := (-1 : ℝ)) (x := x) (B.mdifferentiableAt (x := x))
  have hcoe : (fun b : M => ((-1 : ℝ) • B) b) = (-1 : ℝ) • (fun b : M => B b) := by
    funext b
    rw [ContMDiffSection.coe_smul]
  rw [hsub, hadd]
  rw [hcoe, hsmul]
  rw [add_apply, smul_apply, neg_one_smul,
    sub_eq_add_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniLeviCivita_toFun_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniLeviCivita_toFun_sub target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma palatiniWEndo_eq_covDeriv_add_connectionDifference (g₀ g₁ gc : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w +
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
  have hcd := PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀
    (σ := fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) (x := x)
    (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯).mdifferentiableAt w
  have hEndo : deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₁).toFun
        (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := rfl
  rw [hEndo, hcd]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndo_eq_covDeriv_add_connectionDifference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndo_eq_covDeriv_add_connectionDifference target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma palatiniWEndo_sub_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w - deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w := by
  rw [palatiniWEndo_eq_covDeriv_add_connectionDifference (I := I) (M := M) g₀ g₁ g_bg x w,
    palatiniWEndo_eq_covDeriv_add_connectionDifference (I := I) (M := M) g₀ g₁ g₀ x w]
  have hLC : (LeviCivita (I := I) g₀).toFun
      (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w -
        (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := by
    have h := palatiniLeviCivita_toFun_sub (I := I) (M := M) g₀
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x w
    rw [← h]
    rfl
  have hcd : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w =
      PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w -
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
    rw [palatiniVFSec_apply, map_sub, sub_apply]
  rw [hLC, hcd]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndo_sub_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndo_sub_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma palatiniCotangentToDual_slotInsertEndoFib (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) from by
    rw [Tensor0SSpace.toModel_apply_tangent, Tensor0SSpace.eval_eq]]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) 0
        (tangentLinearMapToModel Λ
          (tangentSpaceModelContinuousLinearEquiv (I := I) x w)) =
      (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x (Λ w)) from by
    funext k
    fin_cases k
    change tangentLinearMapToModel Λ
        (tangentSpaceModelContinuousLinearEquiv (I := I) x w) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x (Λ w)
    rw [tangentLinearMapToModel_apply, ContinuousLinearEquiv.symm_apply_apply]]
  rw [Tensor0SSpace.toModel_apply_tangent, Tensor0SSpace.eval_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_slotInsertEndoFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_slotInsertEndoFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_slotInsertEndoFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_slotInsertEndoFib

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma palatiniCotangentToDual_cometricRaise_bdAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₀ x om),
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) from by
    rw [Tensor0SSpace.toModel_apply_tangent, Tensor0SSpace.eval_eq]]
  rw [palatiniInterior_product_toModel_eval (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_cometricRaise_bdAlpha
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniCotangentToDual_cometricRaise_bdAlpha target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem palatiniWEndoInsert_sub_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (palatiniAlpha (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [palatiniCotangentToDual_cometricRaise_bdAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x -
          (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g₀).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om -
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om from rfl]
  rw [show cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om -
          slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om) w =
      cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om) w -
        cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om) w from by
    rw [show cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om) =
        cotangentToDualLinear (I := I) (x := x)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om) from rfl]
    rw [map_sub]
    rfl]
  rw [palatiniCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om w]
  rw [palatiniCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x) om w]
  rw [show cotangentToDual (I := I) om (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w) -
        cotangentToDual (I := I) om (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x w) =
      cotangentToDual (I := I) om
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w - deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x w) from by
    rw [show cotangentToDual (I := I) om
          (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w - deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x w) =
        cotangentToDualLinear (I := I) (x := x) om
          (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w - deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g₀ x w)
        from rfl]
    rw [map_sub]
    rfl]
  rw [palatiniWEndo_sub_eq (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [palatiniAlpha, palatiniUnitModel_add, add_apply,
    palatiniAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    palatiniAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
            (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
          PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show ∀ v : TangentSpace I x, cotangentToDual (I := I) om v =
        cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
    exact map_add _ _ _]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
          (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun
          (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from by
    rw [show cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
        cotangentToDualLinear (I := I) (x := x) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show cotangentToDual (I := I) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun
      (fun b => palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        (palatiniVFSec (I := I) (M := M) g₁ g_bg g₀ x) w)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndoInsert_sub_eq_cometricRaise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndoInsert_sub_eq_cometricRaise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndoInsert_sub_eq_cometricRaise ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.palatiniWEndoInsert_sub_eq_cometricRaise

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
