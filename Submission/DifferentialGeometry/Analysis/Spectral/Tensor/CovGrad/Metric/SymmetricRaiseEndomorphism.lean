import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.CometricRaise
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

noncomputable def symmRaiseEndoFib (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) g x
        (ccTensorBilinSymm (I := I) g T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
            (ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ccTensorBilinSymm (I := I) g T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
            (ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ccTensorBilinSymm (I := I) g T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma symmRaiseEndoFib_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v : TangentSpace I x) :
    symmRaiseEndoFib (I := I) (M := M) g T x v =
      DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
        (ccTensorBilinSymm (I := I) g T x v).toLinearMap := by
  rw [symmRaiseEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndoFib_apply

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inner_symmRaiseEndo (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    g.inner x (symmRaiseEndoFib (I := I) (M := M) g T x v) w =
      ccTensorBilinSymm (I := I) g T x v w := by
  rw [symmRaiseEndoFib_apply]
  exact DifferentialGeometry.Geometry.Operator.inner_metricSharp (I := I) g x
    (ccTensorBilinSymm (I := I) g T x v).toLinearMap w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_symmRaiseEndo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_symmRaiseEndo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_symmRaiseEndo ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.inner_symmRaiseEndo

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem symmRaiseEndo_smooth (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (symmRaiseEndoFib (I := I) (M := M) g T x)) := by
  apply contMDiff_continuousLinearMap_section_of_apply (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => symmRaiseEndoFib (I := I) (M := M) g T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g T b (Y b)).toLinearMap
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α j)
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
      DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g T b (Y b)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)⟩ :
            _root_.Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase :
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
          (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := DifferentialGeometry.Geometry.Operator.metricSharp_contMDiff_total
    (I := I) g
    (cv := fun b : M =>
      (ccTensorBilinSymm (I := I) g T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
        (ccTensorBilinSymm (I := I) g T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x
      (symmRaiseEndoFib (I := I) (M := M) g T x (Y x))
  rw [symmRaiseEndoFib_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smooth target :: scope.openDecls } }

noncomputable def symmRaiseEndo (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => symmRaiseEndoFib (I := I) (M := M) g T x
  contMDiff_toFun := symmRaiseEndo_smooth (I := I) (M := M) g T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma symmRaiseEndo_apply (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (x : M) :
    symmRaiseEndo (I := I) (M := M) g T x =
    symmRaiseEndoFib (I := I) (M := M) g T x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccMultilinear_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + U) x : Tensor0SSpace 2 I x) =
      (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) +
        (ccTensorMultilinear (I := I) g U x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccMultilinear_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccMultilinear_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccModel_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + U) x =
      ccTensorModel (I := I) g T x +
        ccTensorModel (I := I) g U x := by
  unfold ccTensorModel
  rw [ccMultilinear_add, Tensor0SSpace.toModel_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccModel_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccModel_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + U) x v w =
      ccTensorBilinSymm (I := I) g T x v w +
        ccTensorBilinSymm (I := I) g U x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccModel_add,
    add_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccBilinSymm_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccBilinSymm_add target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
lemma symmRaiseEndo_add (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    symmRaiseEndo (I := I) (M := M) g (T + U) =
      symmRaiseEndo (I := I) (M := M) g T +
        symmRaiseEndo (I := I) (M := M) g U := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [show ((symmRaiseEndo (I := I) (M := M) g T +
      symmRaiseEndo (I := I) (M := M) g U) x) =
      symmRaiseEndo (I := I) (M := M) g T x +
        symmRaiseEndo (I := I) (M := M) g U x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [add_apply, map_add]
  simp only [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [add_apply, ccBilinSymm_add]
  rw [inner_symmRaiseEndo, inner_symmRaiseEndo]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_add

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma symmRaiseEndo_smul (g : SmoothRiemannianMetric I M) (a : ℝ)
    (T : SmoothCcTensor g 0 2) :
    symmRaiseEndo (I := I) (M := M) g (a • T) =
      a • symmRaiseEndo (I := I) (M := M) g T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [show ((a • symmRaiseEndo (I := I) (M := M) g T) x) =
      a • symmRaiseEndo (I := I) (M := M) g T x from by
    rw [ContMDiffSection.coe_smul]
    rfl]
  rw [smul_apply, map_smul]
  simp only [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [smul_apply, ccTensorBilinSymm_smul]
  rw [inner_symmRaiseEndo, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmRaiseEndo_smul

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_bilin (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (u w : E) :
    unitModel (I := I) (M := M) g 2 S x ![u, w] =
      ccTensorBilin (I := I) g S x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm u)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) := by
  rw [ccTensorBilin_apply, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g S x =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        S.toSection x) (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_bilin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_eq_bilin target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_toModel_eval (s : ℕ) (x : M)
    (v : TangentSpace I x) (D : Tensor0SSpace (s + 1) I x)
    (w : Fin s → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) w) := by
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.interior_product_toModel_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.interior_product_toModel_eval target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m =
      cotangentToDual (I := I) (x := x) om
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
  rw [Tensor0SSpace.toModel_apply_model_vector]
  rw [show (fun k : Fin 1 =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m k)) =
      (fun _ : Fin 1 =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) from by
    funext k
    fin_cases k
    rfl]
  rw [cotangentToDual_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toModel_om_single
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toModel_om_single target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
lemma insert_symmRaise_eq (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    slotInsertEndoCc (I := I) (M := M) g 0
        (symmRaiseEndo (I := I) (M := M) g T) =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hleft : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g T x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))
        (inverseMetricSharpFib (I := I) g x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (symmRaiseEndo (I := I) (M := M) g T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single (I := I) (M := M) x om
      (Function.update w 0
        (tangentLinearMapToModel
          (symmRaiseEndo (I := I) (M := M) g T x) (w 0)))]
    rw [Function.update_self, tangentLinearMapToModel_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [symmRaiseEndo_apply]
    rw [show cotangentToDual (I := I) (x := x) om
        (symmRaiseEndoFib (I := I) (M := M) g T x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))) =
      cotangentToDualLinear (I := I) (x := x) om
        (symmRaiseEndoFib (I := I) (M := M) g T x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (symmRaiseEndoFib (I := I) (M := M) g T x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0)))]
    rw [g.symm]
    rw [inner_symmRaiseEndo]
  rw [hleft]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 0 x _ om]
  rw [interior_product_toModel_eval (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g
    (Equiv.swap (0 : Fin 2) 1)
    (ccTensor02Symm (I := I) (M := M) g T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) g x om)) w : Fin 2 → E)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![w 0, tangentSpaceModelContinuousLinearEquiv (I := I) x
        (inverseMetricSharpFib (I := I) g x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_bilin (I := I) (M := M) g
    (ccTensor02Symm (I := I) (M := M) g T) x
    (w 0) (tangentSpaceModelContinuousLinearEquiv (I := I) x
      (inverseMetricSharpFib (I := I) g x om))]
  rw [smoothCcTensorBilinForm_ccTensor02Symm (I := I) (M := M) g T x]
  rw [ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.insert_symmRaise_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.insert_symmRaise_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.insert_symmRaise_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.insert_symmRaise_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
