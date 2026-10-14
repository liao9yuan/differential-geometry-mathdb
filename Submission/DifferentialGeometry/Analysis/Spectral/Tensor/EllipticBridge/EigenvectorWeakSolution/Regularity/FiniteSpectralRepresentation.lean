import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.SpectralSeriesSecondOrderSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Integral.L2

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

private noncomputable def finiteCoeffLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    TensorHs.finiteSupportSubmodule
        (I := I) (M := M) (g := g) (r := r) (s := s) σ →ₗ[ℝ]
      (TensorEigenIdx (I := I) (M := M) g r s →₀ ℝ) where
  toFun v := Finsupp.ofSupportFinite v.1.coeff v.2
  map_add' v w := by
    ext i
    rfl
  map_smul' c v := by
    ext i
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteCoeffLin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteCoeffLin target :: scope.openDecls } }

noncomputable def finiteReprLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    TensorHs.finiteSupportSubmodule
        (I := I) (M := M) (g := g) (r := r) (s := s) σ →ₗ[ℝ]
      SmoothCcTensor g r s :=
  (Finsupp.linearCombination ℝ
      (eigenvectorSmooth (I := I) (M := M) g r s)).comp
    (finiteCoeffLin (I := I) (M := M) g r s σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin


omit [CompleteSpace E] in
@[simp] theorem finiteReprLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (v : TensorHs.finiteSupportSubmodule
      (I := I) (M := M) (g := g) (r := r) (s := s) σ) :
    finiteReprLin (I := I) (M := M) g r s σ v =
      tensorHsSmoothRepr (I := I) (M := M) v.1 v.2 := by
  classical
  let hv : (Function.support v.1.coeff).Finite := v.2
  change
    Finsupp.linearCombination ℝ
        (eigenvectorSmooth (I := I) (M := M) g r s)
        (Finsupp.ofSupportFinite v.1.coeff hv) =
      tensorHsSmoothRepr (I := I) (M := M) v.1 hv
  have hsupp :
      (Finsupp.ofSupportFinite v.1.coeff hv).support = hv.toFinset :=
    Finsupp.ofSupportFinite_support hv
  rw [Finsupp.linearCombination_apply, Finsupp.sum,
    hsupp, tensorHsSmoothRepr_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.finiteReprLin_apply

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
