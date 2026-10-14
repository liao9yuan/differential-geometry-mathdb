import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.TensorSlotSwap
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensor.SectionCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
omit [T2Space M] in
private theorem tangentBilinFlip_curry_apply_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedSpace r (t + 2)
    letI := tensorRSBundleTopology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundleFiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv Yu : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x) (Yu x))) := by
  let : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 2)
  let : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedSpace r (t + 2)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundleTopology r (t + 2)
  let : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundleFiber r (t + 2)
  let : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  let : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv Yu
  have hA :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
  have h1 := ContMDiff.clm_bundle_apply (b := id) hA Yu.contMDiff
  have h2 :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
  have h3 := ContMDiff.clm_bundle_apply (b := id) h2 Yv.contMDiff
  refine h3.congr ?_
  intro x
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tangentBilinFlip_curry_apply_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tangentBilinFlip_curry_apply_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem tangentBilinFlip_curry_apply_contMDiff (r t : ℕ)
    :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedSpace r (t + 2)
    letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundleTopology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundleFiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))) := by
  let : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 2)
  let : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedSpace r (t + 2)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundleTopology r (t + 2)
  let : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundleFiber r (t + 2)
  let : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  let : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => tangentBilinFlip (I := I) (M := M)
      (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))
  intro Yu
  exact tangentBilinFlip_curry_apply_apply_contMDiff (I := I) (M := M) r t Z Yv Yu

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tangentBilinFlip_curry_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tangentBilinFlip_curry_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoCurryFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedSpace r (t + 2)
    letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundleTopology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundleFiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun x : M => TensorRSSpace r (t + 2) I x)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x) (Yv x))) := by
  let : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 2)
  let : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedSpace r (t + 2)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundleTopology r (t + 2)
  let : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundleFiber r (t + 2)
  let : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  let : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  have hflip := tangentBilinFlip_curry_apply_contMDiff (I := I) (M := M) r t Z Yv
  let : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 1)
  let : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModelNormedSpace r (t + 1)
  let := tensorRSBundleTopology (I := I) (M := M) r (t + 1)
  let := tensorRSBundleFiber (I := I) (M := M) r (t + 1)
  let := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  let := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph ∘
        (fun x : M => (⟨x, tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r t ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r t I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph.contMDiff.comp hflip
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)),
    swapTwoCurryFib_apply (I := I) (M := M) r t x (Z x) (Yv x)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoCurryFib_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.swapTwoCurryFib_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoCurryFib_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedSpace r (t + 2)
    letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundleTopology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundleFiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x))) := by
  let : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 2)
  let : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedSpace r (t + 2)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundleTopology r (t + 2)
  let : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundleFiber r (t + 2)
  let : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  let : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r (t + 1) I z)
    (φ := fun x => swapTwoCurryFib (I := I) (M := M) r t x (Z x))
  intro Yv
  exact swapTwoCurryFib_apply_contMDiff (I := I) (M := M) r t Z Yv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoCurryFib_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.swapTwoCurryFib_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
omit [T2Space M] in
private lemma swapTwoFib_fromCurry (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) :
    covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        (swapTwoCurryFib (I := I) (M := M) r t x T) =
      swapTwoFib (I := I) (M := M) r t x T :=
  (swapTwoFib_apply (I := I) (M := M) r t x T).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoFib_fromCurry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.swapTwoFib_fromCurry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem swapTwoFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModelNormedSpace r (t + 2)
    letI := tensorRSBundleTopology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundleFiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x (Z x))) := by
  let : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 2)
  let : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModelNormedSpace r (t + 2)
  let : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundleTopology r (t + 2)
  let : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundleFiber r (t + 2)
  let : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  let : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  have hΨ := swapTwoCurryFib_contMDiff (I := I) (M := M) r t Z
  let : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (t + 1)
  let : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModelNormedSpace r (t + 1)
  let := tensorRSBundleTopology (I := I) (M := M) r (t + 1)
  let := tensorRSBundleFiber (I := I) (M := M) r (t + 1)
  let := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  let := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph ∘
        (fun x : M => (⟨x,
          swapTwoCurryFib (I := I) (M := M) r t x (Z x)⟩ :
          _root_.Bundle.TotalSpace (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r (t + 1) I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph.contMDiff.comp hΨ
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r (t + 1) x _]
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E) x)
    (swapTwoFib_fromCurry (I := I) (M := M) r t x (Z x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoFib_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.swapTwoFib_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem swapTwoFib_contMDiff (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r (t + 2) I z)
    (φ := fun x => swapTwoFib (I := I) (M := M) r t x)
  intro Z
  exact swapTwoFib_apply_contMDiff (I := I) (M := M) r t Z

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoFib_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.swapTwoFib_contMDiff target :: scope.openDecls } }

noncomputable def swapTwoSec (r t : ℕ) :
    HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I where
  toFun := fun x : M => swapTwoFib (I := I) (M := M) r t x
  contMDiff_toFun := swapTwoFib_contMDiff (I := I) (M := M) r t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.swapTwoSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.swapTwoSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.swapTwoSec ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoSec

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
lemma swapTwoSec_apply (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
      swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.swapTwoSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.swapTwoSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.swapTwoSec_apply ``Submission.DifferentialGeometry.Geometry.Curvature.swapTwoSec_apply

end Curvature
end Geometry
end DifferentialGeometry
