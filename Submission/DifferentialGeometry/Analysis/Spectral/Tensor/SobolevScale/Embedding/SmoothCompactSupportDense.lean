import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.SpectralSeriesSecondOrderSobolev
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }


noncomputable def ccToHsLin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) :
    SmoothCcTensor g 0 s →ₗ[ℝ] TensorHs (I := I) (M := M) g 0 s σ where
  toFun := ccTensorToHs (I := I) (M := M) g s σ
  map_add' := ccTensorToHs_add (I := I) (M := M) g s σ
  map_smul' := ccTensorToHs_smul (I := I) (M := M) g s σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHsLin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHsLin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHsLin ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHsLin


@[simp] theorem ccToHsLin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g 0 s) :
    ccToHsLin (I := I) (M := M) g s σ S =
      ccTensorToHs (I := I) (M := M) g s σ S :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHsLin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHsLin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHsLin_apply ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHsLin_apply

theorem ccToHsLin_repr
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (v : TensorHs (I := I) (M := M) g 0 s σ)
    (hv : (Function.support v.coeff).Finite) :
    ccToHsLin (I := I) (M := M) g s σ
        (tensorHsSmoothRepr (I := I) (M := M) v hv) = v := by
  apply TensorHs.ext
  funext i
  simp only [ccToHsLin_apply, ccTensorToHs_coeff]
  rw [SmoothCcTensor.toL2_apply,
    tensorHsSmoothRepr_toL2 (I := I) (M := M) hσ v hv,
    tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHsLin_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHsLin_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHsLin_repr ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHsLin_repr

theorem ccToHs_eigen
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    ccTensorToHs (I := I) (M := M) g s σ
        (eigenvectorSmooth (I := I) (M := M) g 0 s i) =
      tensorHsBasisVec (I := I) (M := M)
        (g := g) (r := 0) (s := s) σ i := by
  classical
  let v := tensorHsBasisVec (I := I) (M := M)
    (g := g) (r := 0) (s := s) σ i
  have hv : (Function.support v.coeff).Finite := by
    refine Set.finite_singleton i |>.subset ?_
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · exact False.elim ((Function.mem_support.mp hj) (by simp [v, hji]))
  have hfin : hv.toFinset = {i} := by
    ext j
    simp only [Set.Finite.mem_toFinset,
      Function.mem_support, v, tensorHsBasisVec_coeff, ne_eq]
    by_cases hji : j = i <;> simp [hji]
  have hre : tensorHsSmoothRepr (I := I) (M := M) v hv =
      eigenvectorSmooth (I := I) (M := M) g 0 s i := by
    rw [tensorHsSmoothRepr_eq (I := I) (M := M) v hv, hfin]
    simp [v]
  rw [← hre, ← ccToHsLin_apply]
  exact ccToHsLin_repr (I := I) (M := M) g s hσ v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHs_eigen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHs_eigen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHs_eigen ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHs_eigen

theorem ccToHsLin_dense
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    DenseRange (ccToHsLin (I := I) (M := M) g s σ) := by
  classical
  refine (tensorHsFiniteSupportSubmodule_dense
    (I := I) (M := M) (g := g) (r := 0) (s := s) (σ := σ)).mono ?_
  intro v hv
  have hvfs : (Function.support v.coeff).Finite :=
    (TensorHs.mem_finiteSupportSubmodule (I := I) (M := M) v).mp hv
  exact ⟨tensorHsSmoothRepr (I := I) (M := M) v hvfs,
    ccToHsLin_repr (I := I) (M := M) g s hσ v hvfs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccToHsLin_dense then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccToHsLin_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccToHsLin_dense ``Submission.DifferentialGeometry.Analysis.Spectral.ccToHsLin_dense

end DifferentialGeometry.Analysis.Spectral

end
