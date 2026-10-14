import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarComposition
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem scalar0_comp (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (S T : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (ccOperatorFieldComp g 0 0 0 S T).toSection x =
      TensorRSField.scalar0 S.toSection x * TensorRSField.scalar0 T.toSection x := by
  let f : C^∞⟮𝓘(ℝ, ℝ), M; ℝ⟯ :=
    ⟨TensorRSField.scalar0 S.toSection, TensorRSField.scalar0_smooth S.toSection⟩
  have hS : scalarCc g f = S := SmoothCcTensor.ext_scalar0 (scalar0_scalarCc g f)
  rw [← hS, operatorFieldComposition_zero_eq_operatorFieldApply, app_scalarCc,
    scalar0_smul_cc, scalar0_scalarCc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalar0_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalar0_comp target :: scope.openDecls } }

theorem scalarH1ToContinuous_scalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u v : TensorHs g 0 0 ((1 : ℕ) : ℝ)) (x : M) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    scalarH1ToContinuous g (J (scalarHsMul g 1 (by norm_num) u v)) x =
      scalarH1ToContinuous g (J u) x * scalarH1ToContinuous g (J v) x := by
  let hn : Module.finrank ℝ ℝ / 2 + 1 ≤ 1 := by norm_num
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  have heval : Continuous
      (fun u : TensorHs g 0 0 ((1 : ℕ) : ℝ) => scalarH1ToContinuous g (J u) x) :=
    (ContinuousMap.evalCLM ℝ x).continuous.comp
      ((scalarH1ToContinuous g).continuous.comp J.continuous)
  refine (ccToHsLin_dense g 0
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq
      (heval.comp ((scalarHsMul g 1 hn).continuous.clm_apply continuous_const))
      (heval.mul continuous_const)
  intro S
  refine (ccToHsLin_dense g 0
    (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))).induction_on v ?_ ?_
  · exact isClosed_eq
      (heval.comp (scalarHsMul g 1 hn (ccToHsLin g 0 ((1 : ℕ) : ℝ) S)).continuous)
      (continuous_const.mul heval)
  intro T
  change scalarH1ToContinuous g (J (scalarHsMul g 1 hn
    (ccTensorToHs g 0 ((1 : ℕ) : ℝ) S)
    (ccTensorToHs g 0 ((1 : ℕ) : ℝ) T))) x = _
  simp only [scalarHsMul_apply_ccTensorToHs, J, tensorHsInclusion_ccTensorToHs,
    scalarH1ToContinuous_apply_ccTensorToHs, ccToHsLin_apply]
  exact scalar0_comp g S T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_scalarHsMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_scalarHsMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_scalarHsMul ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_scalarHsMul

end DifferentialGeometry.Analysis.Spectral
