import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.FiniteSpectralRepresentation
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.LinearMap
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Retag
import Mathlib.Analysis.Normed.Operator.Extend

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
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

abbrev ScalarH2Core (g : SmoothRiemannianMetric I M) :=
  TensorHs.finiteSupportSubmodule
    (I := I) (M := M) (g := g) (r := 0) (s := 0) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ScalarH2Core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ScalarH2Core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ScalarH2Core ``Submission.DifferentialGeometry.Analysis.Spectral.ScalarH2Core

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toRS0_sub {x : M} (A B : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 (A - B) =
      Tensor0SSpace.toRS0 A - Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  change (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • (A - B) =
    (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • A -
      (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x) c • B
  exact smul_sub _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.toRS0_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.toRS0_sub target :: scope.openDecls } }

noncomputable def lapDiffSec
    (g h : SmoothRiemannianMetric I M) :
    ScalarH2Core (I := I) (M := M) g →ₗ[Real] SmoothCcTensor g 0 0 :=
  ((SmoothCcTensor.retagEquiv h g 0 0).toLinearMap.comp
      ((rawConnLapLin (I := I) h 0 0).comp
        ((SmoothCcTensor.retagEquiv g h 0 0).toLinearMap.comp
          (finiteReprLin (I := I) (M := M) g 0 0 2)))) -
    (rawConnLapLin (I := I) g 0 0).comp
      (finiteReprLin (I := I) (M := M) g 0 0 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffSec ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffSec

theorem lapDiffSec_apply
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g) (x : M) :
    (lapDiffSec (I := I) (M := M) g h v).toSection x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
            ΔG (I := I) g ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x)) := by
  simp only [lapDiffSec, LinearMap.sub_apply, LinearMap.comp_apply,
    finiteReprLin_apply, rawConnLapLin_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  change rawTensorConnLap (I := I) h 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x -
      rawTensorConnLap (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x = _
  rw [← repr_eq_lift (I := I) (M := M) v.1 v.2]
  rw [rawLap_scalar (I := I) (M := M) h
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x,
    rawLap_scalar (I := I) (M := M) g
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x]
  rw [laplacian_levi_eq (I := I) h
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x,
    laplacian_levi_eq (I := I) g
      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x]
  rw [← toRS0_sub]
  rw [map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffSec_apply ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffSec_apply

noncomputable def lapDiffCore
    (g h : SmoothRiemannianMetric I M) :
    ScalarH2Core (I := I) (M := M) g →ₗ[Real] TensorL2 0 0 g :=
  (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 0)).toLinearMap.comp
    (lapDiffSec (I := I) (M := M) g h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore

theorem lapDiffCore_pair
    (q h : SmoothRiemannianMetric I M)
    (v w : ScalarH2Core (I := I) (M := M) q) :
    inner Real (lapDiffCore (I := I) (M := M) q h v)
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)) =
      ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
            ΔG (I := I) q ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x) *
          reprScalar0 (I := I) (M := M) w.1 w.2 x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  change _root_.Inner.inner Real
      (SmoothCcTensor.toL2 (lapDiffSec (I := I) (M := M) q h v))
      (SmoothCcTensor.toL2
        (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)) = _
  rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply]
  rw [lapDiffSec_apply (I := I) (M := M) q h v x]
  have hrepr_x :
      (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2).toSection x =
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) w.1 w.2)
          (reprScalar0_smooth (I := I) (M := M) w.1 w.2)).toTensorRSField ∞ x := by
    exact congrArg (fun T => T x)
      (repr_eq_lift (I := I) (M := M) w.1 w.2).symm
  rw [hrepr_x, Tensor0SField.toRS0_eq,
    inner_toRS0_zero (I := I) (M := M) q x]
  have hlap :
      (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x)
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
            ΔG (I := I) q ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x)) =
        ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
          ΔG (I := I) q ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x := by
    change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hrepr :
      (tensor0SSpaceEvalScalar (𝕜 := Real) (I := I) (M := M) x)
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) w.1 w.2)
          (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x) =
        reprScalar0 (I := I) (M := M) w.1 w.2 x := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SSpace.toModel
      (Tensor0SField.fromScalarField ∞
        (reprScalar0 (I := I) (M := M) w.1 w.2)
        (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x) Fin.elim0 = _
    exact Tensor0SField.fromScalarField_apply ∞
      (reprScalar0 (I := I) (M := M) w.1 w.2)
      (reprScalar0_smooth (I := I) (M := M) w.1 w.2) x Fin.elim0
  rw [hlap, hrepr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore_pair

theorem lapDiffCore_sq
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g) :
    ‖lapDiffCore (I := I) (M := M) g h v‖ ^ 2 =
      ∫ x, (ΔG (I := I) h ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x -
            ΔG (I := I) g ⟨_, (reprScalar0_smooth (I := I) (M := M) v.1 v.2)⟩ x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  change ‖SmoothCcTensor.toL2
      (lapDiffSec (I := I) (M := M) g h v)‖ ^ 2 = _
  rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun (I := I) (M := M) g 0 0
      (lapDiffSec (I := I) (M := M) g h v)]
  unfold tensorL2Inner
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply]
  rw [lapDiffSec_apply (I := I) (M := M) g h v x]
  rw [inner_toRS0_scalar (I := I) (M := M) g x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore_sq ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore_sq

theorem lapDiffCore_norm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : ScalarH2Core (I := I) (M := M) g),
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g <= (1 / 2 : Real) →
          ‖lapDiffCore (I := I) (M := M) g h v‖ <=
            Real.sqrt C *
              |CheegerGromovCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h g g| * ‖v‖ := by
  obtain ⟨C, hC, henergy⟩ := lapDiff_energy_le (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro h v hsmall
  let rho : Real :=
    CheegerGromovCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g
  have hsq :
      ‖lapDiffCore (I := I) (M := M) g h v‖ ^ 2 <=
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [lapDiffCore_sq (I := I) (M := M) g h v]
    simpa only [rho, Submodule.norm_coe] using henergy h v.1 v.2 hsmall
  have hrhs :
      (Real.sqrt C * |rho| * ‖v‖) ^ 2 =
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC, sq_abs]
  have hrhs0 : 0 <= Real.sqrt C * |rho| * ‖v‖ := by positivity
  rw [← hrhs] at hsq
  nlinarith [norm_nonneg
    (lapDiffCore (I := I) (M := M) g h v)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffCore_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffCore_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffCore_norm ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffCore_norm

noncomputable def lapDiffOp
    (g h : SmoothRiemannianMetric I M) :
    TensorHs (I := I) (M := M) g 0 0 2 →L[Real] TensorL2 0 0 g :=
  (lapDiffCore (I := I) (M := M) g h).extendOfNorm
    (ScalarH2Core (I := I) (M := M) g).subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffOp ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffOp

theorem lapDiffOp_apply_scalarH2Core
    (g h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) g)
    (hsmall : (Module.finrank Real E : Real) *
        CheegerGromovCompactness.metricDerivNormSupOn
          (I := I) Set.univ 1 h g g <= (1 / 2 : Real)) :
    lapDiffOp (I := I) (M := M) g h v.1 =
      lapDiffCore (I := I) (M := M) g h v := by
  obtain ⟨C, hC, hbound⟩ := lapDiffCore_norm (I := I) (M := M) g
  let B : Real := Real.sqrt C *
    |CheegerGromovCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g|
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) g).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := g) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨B, ?_⟩
  intro w
  simpa only [B, Submodule.coe_subtype, Submodule.norm_coe] using hbound h w hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffOp_apply_scalarH2Core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffOp_apply_scalarH2Core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffOp_apply_scalarH2Core ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffOp_apply_scalarH2Core

theorem lapDiffOp_norm
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M),
        (Module.finrank Real E : Real) *
            CheegerGromovCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h g g <= (1 / 2 : Real) →
          ‖lapDiffOp (I := I) (M := M) g h‖ <=
            Real.sqrt C *
              |CheegerGromovCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h g g| := by
  obtain ⟨C, hC, hbound⟩ := lapDiffCore_norm (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro h hsmall
  let B : Real := Real.sqrt C *
    |CheegerGromovCompactness.metricDerivNormSupOn
      (I := I) Set.univ 1 h g g|
  have hB : 0 <= B := by positivity
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) g).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := g) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply LinearMap.opNorm_extendOfNorm_le hdense hB
  intro w
  simpa only [B, Submodule.coe_subtype, Submodule.norm_coe] using hbound h w hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffOp_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffOp_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffOp_norm ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffOp_norm

end Spectral
end Analysis
end DifferentialGeometry

end
