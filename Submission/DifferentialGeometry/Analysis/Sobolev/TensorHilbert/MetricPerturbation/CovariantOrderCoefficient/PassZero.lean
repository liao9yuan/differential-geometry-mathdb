import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
section NormedDomReindexing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (tensorRSDomDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => tensorRSDomDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x)
              (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))).mp
        hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSDomDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrFib_contMDiff

def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => tensorRSDomDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection ``Submission.DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      tensorRSDomDomCongr σ (R.toSection x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.rsDomDomCongrSection_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma rsDomDomCongr_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (X Y : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ X -
        rsDomDomCongrSection (I := I) (M := M) g r s σ Y := by
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  let := tensorRSBundleFiber (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  let := tensorRSBundle_vector (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  let := tensorRSBundle_smooth (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r s
  apply SmoothCcTensor.ext
  apply DFunLike.ext _ _
  intro x
  have hsub : (X - Y).toSection x = X.toSection x - Y.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  have hsub2 :
      (rsDomDomCongrSection (I := I) (M := M) g r s σ X -
          rsDomDomCongrSection (I := I) (M := M) g r s σ Y).toSection x =
        (rsDomDomCongrSection (I := I) (M := M) g r s σ X).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g r s σ Y).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub2,
    rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  change tensorRSDomDomCongr σ (X.toSection x - Y.toSection x) =
    tensorRSDomDomCongr σ (X.toSection x) - tensorRSDomDomCongr σ (Y.toSection x)
  apply ContinuousLinearMap.ext
  intro D
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro m
  change Tensor0SSpace.eval
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSDomDomCongr σ (X.toSection x - Y.toSection x)) D) m =
    Tensor0SSpace.eval
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSDomDomCongr σ (X.toSection x) -
          tensorRSDomDomCongr σ (Y.toSection x)) D) m
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ
    (X.toSection x - Y.toSection x) D m]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      rsDomDomCongr σ (X.toSection x) - rsDomDomCongr σ (Y.toSection x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (X.toSection x - Y.toSection x : TensorRSSpace r s I x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x) D from rfl]
  rw [Tensor0SSpace.eval_sub]
  rw [Tensor0SSpace.eval_sub]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (Y.toSection x) D m]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongr_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.rsDomDomCongr_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.rsDomDomCongr_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.rsDomDomCongr_sub

end NormedDomReindexing

def termSlotEndoPassZeroCc (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g 2 3 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 3 (finRotate 3)
    (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] lemma termSlotEndoPassZeroCc_toSection (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (termSlotEndoPassZeroCc (I := I) (M := M) g Term).toSection x =
      tensorRSDomDomCongr (finRotate 3)
        ((bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term).toSection x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc_toSection ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotEndoPassZeroCc_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : SmoothCcTensor g 1 2) (x : M) (om : Tensor0SSpace 1 I x)
    (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
            (termSlotEndoPassZeroCc (I := I) (M := M) g Term) W).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
        (fun j : Fin 2 => if j = 0 then
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (Term x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)))
        else v 0) := by
  classical
  let vt : Fin 3 → TangentSpace I x :=
    fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
  have hcomp : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
          (termSlotEndoPassZeroCc (I := I) (M := M) g Term) W).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (termSlotEndoPassZeroCc (I := I) (M := M) g Term).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) := by
    rw [operatorFieldComposition_toSection]
    rfl
  rw [hcomp, termSlotEndoPassZeroCc_toSection]
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSDomDomCongr (finRotate 3)
          ((bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term).toSection x))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)) vt =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
      (fun j : Fin 2 => if j = 0 then Term x (vt 1) (vt 2) else vt 0)
  rw [rsDomDomCongr_apply_eval]
  rw [termSlotEndoCc_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Term x)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 1 x (Term x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) from rfl]
  rw [termSlotFib_apply_eval]
  have hslot := slotInsertEndoFib_apply_eval (I := I) (M := M) (1 + 1) 0 x
    ((Term x) (vt ((finRotate 3) 0)))
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
    (Matrix.vecTail fun k => vt ((finRotate 3) k))
  change Tensor0SSpace.eval
      (slotInsertEndoFib (I := I) (M := M) (1 + 1) 0 x
        ((Term x) (vt ((finRotate 3) 0)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om))
      (Matrix.vecTail fun k => vt ((finRotate 3) k)) =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
      (Function.update (Matrix.vecTail fun k => vt ((finRotate 3) k)) 0
        (((Term x) (vt ((finRotate 3) 0)))
          ((Matrix.vecTail fun k => vt ((finRotate 3) k)) 0))) at hslot
  rw [hslot]
  have hr0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have hr1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have hr2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, if_pos rfl]
    change Term x (vt (finRotate 3 0)) (vt (finRotate 3 1)) = Term x (vt 1) (vt 2)
    rw [hr0, hr1]
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Function.update_of_ne (Fin.succ_ne_zero 0), if_neg (Fin.succ_ne_zero 0)]
    change vt (finRotate 3 2) = vt 0
    rw [hr2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval ``Submission.DifferentialGeometry.Analysis.Sobolev.toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma exists_iteratedCovGrad_termSlotEndoPassZeroCc_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) :
    ∃ τ : Equiv.Perm (Fin (3 + j)), ∀ (x : M) (d : Tensor0SSpace 2 I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
            (iteratedCovGrad (I := I) g 2 3 j
              (termSlotEndoPassZeroCc (I := I) (M := M) g Term)).toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
              (iteratedCovGrad (I := I) g 2 3 j
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term)).toSection x) d)) := by
  induction j with
  | zero =>
    refine ⟨finRotate 3, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero, termSlotEndoPassZeroCc_toSection,
      toModel_rsDomDomCongr_apply]
  | succ j ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g 2 (3 + j) τ
      (iteratedCovGrad (I := I) g 2 3 j (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term))
      (iteratedCovGrad (I := I) g 2 3 j (termSlotEndoPassZeroCc (I := I) (M := M) g Term))
      hτ x d v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_iteratedCovGrad_termSlotEndoPassZeroCc_toSection_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.exists_iteratedCovGrad_termSlotEndoPassZeroCc_toSection_eq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_termSlotEndoPassZeroCc_eq
    (g : SmoothRiemannianMetric I M)
    (Term : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (termSlotEndoPassZeroCc (I := I) (M := M) g Term)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term)).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_iteratedCovGrad_termSlotEndoPassZeroCc_toSection_eq
    (I := I) (M := M) g Term j
  have hsec : (iteratedCovGrad (I := I) g 2 3 j
        (termSlotEndoPassZeroCc (I := I) (M := M) g Term)).toSection x =
      tensorRSDomDomCongr τ
        ((iteratedCovGrad (I := I) g 2 3 j
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term)).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          (iteratedCovGrad (I := I) g 2 3 j
            (termSlotEndoPassZeroCc (I := I) (M := M) g Term)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          tensorRSDomDomCongr τ
            ((iteratedCovGrad (I := I) g 2 3 j
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 Term)).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g 2 (3 + j) x τ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_iteratedCovGrad_termSlotEndoPassZeroCc_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_iteratedCovGrad_termSlotEndoPassZeroCc_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_iteratedCovGrad_termSlotEndoPassZeroCc_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.riemannianFiberNormSq_iteratedCovGrad_termSlotEndoPassZeroCc_eq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricCovDeriv_symm_right
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricCovDeriv (I := I) g cov X Y Z x = metricCovDeriv (I := I) g cov X Z Y x := by
  unfold metricCovDeriv
  rw [show (fun b : M => g.inner b (Z b) (Y b)) = (fun b : M => g.inner b (Y b) (Z b)) from by
    funext b; rw [g.symm b (Z b) (Y b)]]
  rw [g.symm x (cov.toFun Y x (X x)) (Z x), g.symm x (Y x) (cov.toFun Z x (X x))]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.metricCovDeriv_symm_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.metricCovDeriv_symm_right target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma metricDiffCovDeriv_symm_right
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ X Z Y x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_symm_right (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x,
    metricCovDeriv_symm_right (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.metricDiffCovDeriv_symm_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.metricDiffCovDeriv_symm_right target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem endoCovariantDerivative_metricComparisonDifferenceEndomorphismField_resolvent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - metricDiffCovDeriv (I := I) g₁ g₀
          (fun y : M => V y)
          (fun y : M => metricComparisonEndomorphism (I := I) g₀ g₁ y (W y))
          (fun y : M => Z y) x := by
  classical
  have hg1gir : ∀ u : TangentSpace I x,
      g₁.inner x (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x)) u = g₀.inner x (W x) u := by
    intro u
    rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have hpair : g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x)) (V x)) (Z x)
        - g₀.inner x (W x) (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x)) := by
    rw [endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x (V x) (W x)]
    rw [map_add, add_apply, map_neg, neg_apply,
      inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
    simp only [ContinuousLinearMap.coe_coe, neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show (cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (W x)))
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x)) =
          g₀.inner x (W x) (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x)) from
      cotangentToDual_g0FlatCLM (I := I) g₀ x (W x)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x))]
    ring
  have hk1 := connectionDifference_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => metricComparisonEndomorphism (I := I) g₀ g₁ y (W y))
    (Z := fun y : M => Z y) V.mdifferentiableAt
    ((metricComparisonEndomorphism_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
    Z.mdifferentiableAt
  have hk2 := connectionDifference_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => Z y)
    (Z := fun y : M => metricComparisonEndomorphism (I := I) g₀ g₁ y (W y)) V.mdifferentiableAt
    Z.mdifferentiableAt
    ((metricComparisonEndomorphism_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
  have hsym := metricDiffCovDeriv_symm_right (I := I) g₁ g₀
    (fun y : M => V y) (fun y : M => Z y)
    (fun y : M => metricComparisonEndomorphism (I := I) g₀ g₁ y (W y)) x
  have hconv : g₀.inner x (W x) (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x)) =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x))
        (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x)) := by
    rw [← hg1gir (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x)),
      g₁.symm x (metricComparisonEndomorphism (I := I) g₀ g₁ x (W x))
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Z x) (V x))]
  rw [hpair, hconv]
  linarith [hk1, hk2, hsym]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_metricComparisonDifferenceEndomorphismField_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_metricComparisonDifferenceEndomorphismField_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_metricComparisonDifferenceEndomorphismField_resolvent ``Submission.DifferentialGeometry.Analysis.Sobolev.endoCovariantDerivative_metricComparisonDifferenceEndomorphismField_resolvent

end Sobolev
end Analysis
end DifferentialGeometry

end
