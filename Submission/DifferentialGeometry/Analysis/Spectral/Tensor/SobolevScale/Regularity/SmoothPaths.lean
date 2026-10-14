import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TimeDependentApplication

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.RealInnerProductSpace _root_.InnerProductSpace
namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem rankZero_one (x : M) (A : Tensor0SSpace 0 I x) :
    tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x A •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x = A := by
  apply (tensor0SSpaceContinuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x A •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x) v = Tensor0SSpace.toModel A v
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
    Tensor0SSpace.evalScalar_apply]
  have hone : Tensor0SSpace.toModel
      (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) ∞ x) v = (1 : ℝ) :=
    Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) ∞ x v
  rw [hone, mul_one]
  exact congrArg (Tensor0SSpace.toModel A) (Subsingleton.elim Fin.elim0 v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.rankZero_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.rankZero_one target :: scope.openDecls } }

private noncomputable def oneCc (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 0 :=
  scalarCc (I := I) (M := M) g
    ⟨(fun _ : M => (1 : ℝ)), contMDiff_const⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.oneCc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.oneCc target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem oneCc_apply (g : SmoothRiemannianMetric I M)
    (x : M) (A : Tensor0SSpace 0 I x) :
    (oneCc (I := I) (M := M) g).toSection x A = A := by
  simp only [oneCc, scalarCc, tensorRSField_smulByFun_apply]
  change
    (((1 : ℝ) •
      (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) ∞).toTensorRSField ∞ x) A) = A
  rw [one_smul]
  rw [Tensor0SField.toRS0_apply, rankZero_one (I := I) (M := M)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.oneCc_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.oneCc_apply target :: scope.openDecls } }
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem operatorFieldApplication_one (g : SmoothRiemannianMetric I M) (c : ℕ)
    (Phi : SmoothCcTensor g 0 c) :
    operatorFieldApply (I := I) (M := M) g 0 c Phi (oneCc (I := I) (M := M) g) = Phi := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldApplication_toSection]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.comp_apply, oneCc_apply (I := I) (M := M)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_one target :: scope.openDecls } }

theorem ccHs_eq_smoothHs (g : SmoothRiemannianMetric I M) (sigma : ℝ)
    (Phi : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 sigma Phi =
      smoothCcToTensorHs (I := I) (M := M) g sigma Phi := by
  refine TensorHs.ext ?_
  funext i
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccHs_eq_smoothHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccHs_eq_smoothHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccHs_eq_smoothHs ``Submission.DifferentialGeometry.Analysis.Spectral.ccHs_eq_smoothHs

theorem smoothHs_path_cd
    (g : SmoothRiemannianMetric I M) (n : ℕ)
    (Phi : ℝ → SmoothCcTensor g 0 2) {S : Set ℝ} (hS : IsOpen S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContDiffOn ℝ ∞
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t)) S := by
  let U : TensorHs (I := I) (M := M) g 0 0 (n : ℝ) :=
    ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
      (oneCc (I := I) (M := M) g)
  have h := appHs_path_cd (I := I) (M := M) g 0 2 n Phi hS hPhi U
  have hpath :
      (fun t => appHs g 0 2 n (Phi t) U) =
        fun t => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi t) := by
    funext t
    rw [appHs_apply_ccTensorToHs, operatorFieldApplication_one (I := I) (M := M), ccHs_eq_smoothHs]
  rwa [hpath] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothHs_path_cd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothHs_path_cd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothHs_path_cd ``Submission.DifferentialGeometry.Analysis.Spectral.smoothHs_path_cd

theorem smoothHs_deriv
    (g : SmoothRiemannianMetric I M)
    (Phi : ℝ → SmoothCcTensor g 0 2) {S : Set ℝ} (hS : IsOpen S)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((Phi p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ dPhi : ℝ → SmoothCcTensor g 0 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
          (E := fun x : M => TensorRSSpace 0 2 I x) p.1
          ((dPhi p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ S) ∧
      (∀ t ∈ S, ∀ x : M, ∀ A : Tensor0SSpace 0 I x,
        ∀ slots : Fin 2 → E,
          HasDerivAt
            (fun tau => Tensor0SSpace.toModel (((Phi tau).toSection x) A) slots)
            (Tensor0SSpace.toModel (((dPhi t).toSection x) A) slots) t) ∧
      ∀ n : ℕ, ∀ t ∈ S,
        HasDerivAt
          (fun tau => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi tau))
          (smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (dPhi t)) t := by
  obtain ⟨dPhi, hdPhi, hcomp, hderiv⟩ :=
    exists_timeDerivative_appHs (I := I) (M := M) g 0 2 Phi hS hPhi
  refine ⟨dPhi, hdPhi, hcomp, ?_⟩
  intro n t ht
  let U : TensorHs (I := I) (M := M) g 0 0 (n : ℝ) :=
    ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
      (oneCc (I := I) (M := M) g)
  have happ := hderiv n t ht U
  have hpath :
      (fun tau => appHs g 0 2 n (Phi tau) U) =
        fun tau => smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (Phi tau) := by
    funext tau
    rw [appHs_apply_ccTensorToHs, operatorFieldApplication_one (I := I) (M := M), ccHs_eq_smoothHs]
  have hdval : appHs g 0 2 n (dPhi t) U =
      smoothCcToTensorHs (I := I) (M := M) g (n : ℝ) (dPhi t) := by
    rw [appHs_apply_ccTensorToHs, operatorFieldApplication_one (I := I) (M := M), ccHs_eq_smoothHs]
  rwa [hpath, hdval] at happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.smoothHs_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.smoothHs_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.smoothHs_deriv ``Submission.DifferentialGeometry.Analysis.Spectral.smoothHs_deriv

end DifferentialGeometry.Analysis.Spectral

end
