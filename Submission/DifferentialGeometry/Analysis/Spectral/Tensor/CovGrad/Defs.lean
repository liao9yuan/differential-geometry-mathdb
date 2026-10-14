import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Scalar
import Submission.DifferentialGeometry.Tensor.RSTensor.Reindexing.CovariantSlot

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

private noncomputable def covGradGradSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => w.toSection y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma covGradGradSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) (v : TangentSpace I x) :
    covGradGradSection (I := I) (M := M) g r s w x v =
      tensorCovDerivAt (I := I) (M := M) g r s w x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  unfold covGradGradSection tensorCovDerivAt
  rw [(tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma covGradGradSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) with hcovLC
  have hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => w.toSection y) x⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => w.toSection y)
      (w.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_contMDiff target :: scope.openDecls } }

private noncomputable def covGradSmoothSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :=
  letI : NormedAddCommGroup (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (s + 1)
  letI : NormedSpace ℝ (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModelNormedSpace r (s + 1)
  letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundleTopology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundleFiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) I :=
    tensorRSBundle_smooth ∞ r (s + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ∘
          (fun x : M =>
            (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
              _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
                fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph.contMDiff.comp
      (covGradGradSection_contMDiff (I := I) (M := M) g r s w)
  have hsmooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        (fun x : M =>
          (⟨x, covGradBundleEquiv (I := I) (M := M) r s x
              (covGradGradSection (I := I) (M := M) g r s w x)⟩ :
            _root_.Bundle.TotalSpace (TensorRSModel r (s + 1) ℝ E)
              fun y : M => TensorRSSpace r (s + 1) I y)) := by
    refine hcomp.congr ?_
    intro x
    rw [Function.comp_apply,
      covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x)]
  (ContMDiffSection.mk
      (fun x : M => covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x))
      hsmooth :
    Cₛ^∞⟮I; TensorRSModel r (s + 1) ℝ E,
      (fun x : M => TensorRSSpace r (s + 1) I x)⟯)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covGradSmoothSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    covGradSmoothSection (I := I) (M := M) g r s w x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_apply target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covGradSmoothSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport w.toFun) :
    TensorRSSpace.toModel
      (covGradSmoothSection (I := I) (M := M) g r s w x) = 0 := by
  have hgrad_zero : covGradGradSection (I := I) (M := M) g r s w x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [zero_apply, covGradGradSection_apply]
    exact tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s w hx
      (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
  rw [covGradSmoothSection_apply, hgrad_zero, map_zero, TensorRSSpace.toModel_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_toModel_eq_zero_off_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_toModel_eq_zero_off_tsupport target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma covGradSmoothSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covGradSmoothSection (I := I) (M := M) g r s w x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covGradSmoothSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s w hxnot)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradSmoothSection_hasCompactSupport target :: scope.openDecls } }

noncomputable def covGrad (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r (s + 1) :=
  fun w =>
    { toSection := covGradSmoothSection (I := I) (M := M) g r s w
      hasCompactSupport :=
        covGradSmoothSection_hasCompactSupport (I := I) (M := M) g r s w }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma covGrad_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    (covGrad (I := I) (M := M) g r s w).toSection =
      covGradSmoothSection (I := I) (M := M) g r s w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g r s w).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => w.toSection y) x) := by
  rw [covGrad_toSection, covGradSmoothSection_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_toSection_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s w).toSection x) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply]
  rw [covGradBundleEquiv_apply_toModel]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_toSection_apply_natural
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s w).toSection x) D) v =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s w x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply, covGradBundleEquiv_apply_eval, tensorCovDerivAt_def,
    ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_natural ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_natural

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covGradGradSection_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x =
      covGradGradSection (I := I) (M := M) g r s w₁ x +
        covGradGradSection (I := I) (M := M) g r s w₂ x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [add_apply, covGradGradSection_apply,
    covGradGradSection_apply, covGradGradSection_apply]
  exact tensorCovDerivAt_add (I := I) (M := M) g r s w₁ w₂ x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_add target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma covGradGradSection_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (c • w) x =
      c • covGradGradSection (I := I) (M := M) g r s w x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply, covGradGradSection_apply,
    covGradGradSection_apply]
  exact tensorCovDerivAt_smul (I := I) (M := M) g r s c w x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradGradSection_smul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (w₁ + w₂) =
      covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂).toSection x) =
      (covGrad (I := I) (M := M) g r s w₁).toSection x +
        (covGrad (I := I) (M := M) g r s w₂).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (w₁ + w₂).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₁.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₁ x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₂.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₂ x from rfl,
    covGradGradSection_add (I := I) (M := M) g r s w₁ w₂ x, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_add

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (c • w) =
      c • covGrad (I := I) (M := M) g r s w := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • covGrad (I := I) (M := M) g r s w).toSection x) =
      c • (covGrad (I := I) (M := M) g r s w).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (c • w).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (c • w) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w x from rfl,
    covGradGradSection_smul (I := I) (M := M) g r s c w x, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
@[simp] theorem covGrad_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    covGrad (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := covGrad_smul (I := I) (M := M) g r s (0 : ℝ) 0
  rwa [zero_smul, zero_smul] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
