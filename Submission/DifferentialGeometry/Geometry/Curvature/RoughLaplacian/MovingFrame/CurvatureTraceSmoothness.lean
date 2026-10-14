import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.FieldDecomposition
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.GenuineCurvatureField
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Uniform.SmoothTensor
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Reconstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def genuineCurvTraceFixedFrameCurvatureOnly
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    riemannSec (tensorCov (I := I) g 0 s) (B i) W
      (covApply (tensorCov (I := I) g 0 s) (B i) S) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCurvatureOnly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCurvatureOnly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCurvatureOnly ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCurvatureOnly

noncomputable def genuineCurvTraceFixedFrameCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    (tensorCov (I := I) g 0 s).toFun
      (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma genuineCurvTraceFixedFramePureR_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_def ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_def

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma genuineCurvTraceFixedFrameCovDeriv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_def ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_def

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma genuineCurvTraceFixedFramePureR_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) W
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) S) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_smoothOrthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_smoothOrthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_smoothOrthoFrame ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_smoothOrthoFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) W S b) x
          (smoothOrthoFrame (I := I) g x i x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma genuineCurvTraceFixedFramePureR_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y)) := by
  classical
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) S y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hcovBS

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_summand_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_summand_contMDiff target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem genuineCurvTraceFixedFramePureR_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFramePureR_summand_contMDiff (I := I) g s hW hB hS_total i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_contMDiff ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_contMDiff

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        ((tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y))) := by
  classical
  have hcurvSec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W S y)) :=
    riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hS_total
  exact covApplyRS_contMDiff (I := I) g 0 s hcurvSec (hB i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem genuineCurvTraceFixedFrameCovDeriv_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff (I := I) g s hW hB hS_total i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_contMDiff ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFrameCovDeriv_contMDiff

noncomputable def genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s
          (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibPureR then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibPureR"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibPureR ``Submission.DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibPureR

noncomputable def genuineThirdCurvFieldFibCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibCovDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibCovDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibCovDeriv ``Submission.DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFibCovDeriv

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem genuineThirdCurvFieldFib_eq_pureR_add_covDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) :
    genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m =
      genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m +
        genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m := by
  classical
  rw [genuineThirdCurvFieldFib, genuineThirdCurvFieldFibPureR, genuineThirdCurvFieldFibCovDeriv,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsplit_val :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s
          (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) := by
    have hclm :
        (tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x : TensorRSSpace 0 s I x) =
        genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s
          (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x +
          genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
      rw [genuineCurvTraceFixedFrameCurvatureOnly, genuineCurvTraceFixedFrameCovDeriv,
        ← Finset.sum_add_distrib, tensor3rdCurvGenuine]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x) = _ from hclm]
    rw [add_apply]
  rw [hsplit_val, Tensor0SSpace.toModel_add, add_apply, smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib_eq_pureR_add_covDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib_eq_pureR_add_covDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib_eq_pureR_add_covDeriv ``Submission.DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib_eq_pureR_add_covDeriv

private def genuinePureRDirLMSummand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) v
    (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_add v v']
    rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_smul c v]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuinePureRDirLMSummand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuinePureRDirLMSummand target :: scope.openDecls } }

noncomputable def genuinePureRDirCLMSummand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (genuinePureRDirLMSummand (I := I) (M := M) g s S x i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLMSummand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLMSummand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLMSummand ``Submission.DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLMSummand

noncomputable def genuineCurvatureOnlyDirectionalCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  ∑ i : Fin (Module.finrank ℝ E), genuinePureRDirCLMSummand (I := I) (M := M) g s S x i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlyDirectionalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlyDirectionalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlyDirectionalCLM ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlyDirectionalCLM

omit [CompactSpace M] [I.Boundaryless] in
private lemma genuinePureRDirCLM_apply_extend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    genuineCurvatureOnlyDirectionalCLM (I := I) (M := M) g s S x v =
      genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s (smoothExtensionTangent (I := I) x v)
        (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
  classical
  rw [genuineCurvatureOnlyDirectionalCLM, sum_apply,
    genuineCurvTraceFixedFrameCurvatureOnly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [genuinePureRDirCLMSummand, LinearMap.coe_toContinuousLinearMap', genuinePureRDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x v)) :=
    smoothExtensionTangent_contMDiff x v
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total hB
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := smoothOrthoFrame (I := I) g x i)
    (Y := smoothExtensionTangent (I := I) x v)
    (Z := covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (fun z : M => S.toSection z))
    (x := x) hB hW hcovBS
  rw [smoothExtensionTangent_eq x v] at happly
  rw [happly]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLM_apply_extend
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuinePureRDirCLM_apply_extend target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0S_curry_covGradBundleEquiv_unit_apply
    (s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    (v : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  let vu : Fin (s + 1) → E :=
    Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) u
  have hcurry := TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
      (unitZeroSec (I := I) (M := M) x))
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v) u
  rw [ContinuousLinearEquiv.symm_apply_apply] at hcurry
  rw [hcurry]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
        (unitZeroSec (I := I) (M := M) x)) vu = _
  rw [covGradBundleEquiv_apply_toModel (I := I) (M := M) 0 s x Φ
    (unitZeroSec (I := I) (M := M) x) vu]
  have hzero :
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (vu 0) = v := by
    unfold vu
    rw [Fin.cons_zero, ContinuousLinearEquiv.symm_apply_apply]
  have htail : Matrix.vecTail vu = u := by
    unfold vu
    funext k; rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  rw [hzero, htail]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_curry_covGradBundleEquiv_unit_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensor0S_curry_covGradBundleEquiv_unit_apply target :: scope.openDecls } }

noncomputable def genuineCurvPureRFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    TensorRSSpace 0 (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 s x
    (genuineCurvatureOnlyDirectionalCLM (I := I) (M := M) g s S x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib

omit [CompactSpace M] [I.Boundaryless] in
private lemma tensor0S_curry_genuineCurvPureRFib_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          genuineCurvPureRFib (I := I) (M := M) g s S x)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s (smoothExtensionTangent (I := I) x v)
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) := by
  rw [genuineCurvPureRFib]
  rw [tensor0S_curry_covGradBundleEquiv_unit_apply (I := I) (M := M) s x
    (genuineCurvatureOnlyDirectionalCLM (I := I) (M := M) g s S x) v]
  rw [genuinePureRDirCLM_apply_extend (I := I) (M := M) g s S x v]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_curry_genuineCurvPureRFib_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensor0S_curry_genuineCurvPureRFib_unit target :: scope.openDecls } }

def pureRDirLMSummandFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 s) x (B i x) v
    (covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x (B i x)).map_add v v']
    rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x (B i x)).map_smul c v]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pureRDirLMSummandFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pureRDirLMSummandFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pureRDirLMSummandFixedFrame ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirLMSummandFixedFrame

noncomputable def pureRDirCLMSummandFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRDirLMSummandFixedFrame (I := I) (M := M) g s S B x i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pureRDirCLMSummandFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pureRDirCLMSummandFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pureRDirCLMSummandFixedFrame ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirCLMSummandFixedFrame

noncomputable def pureRDirCLMFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRDirCLMSummandFixedFrame (I := I) (M := M) g s S B x i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma pureRDirCLMFixedFrame_apply_smooth
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) (x : M) :
    pureRDirCLMFixedFrame (I := I) (M := M) g s S B x (W x) =
      genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W B (fun y : M => S.toSection y) x := by
  classical
  rw [pureRDirCLMFixedFrame, sum_apply, genuineCurvTraceFixedFrameCurvatureOnly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrame, LinearMap.coe_toContinuousLinearMap',
    pureRDirLMSummandFixedFrame, LinearMap.coe_mk, AddHom.coe_mk]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  rw [happly]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_apply_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_apply_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_apply_smooth ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_apply_smooth

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRDirCLMFixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    pureRDirCLMFixedFrame (I := I) (M := M) g s S (smoothOrthoFrame (I := I) g x) x =
      genuineCurvatureOnlyDirectionalCLM (I := I) (M := M) g s S x := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_smoothOrthoFrame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_smoothOrthoFrame target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureRDirCLMFixedFrame_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y) x
        (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)) := by
  classical
  refine contMDiff_continuousLinearMap_section_of_apply
    (φ := fun x : M => pureRDirCLMFixedFrame (I := I) (M := M) g s S B x) (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  have htrace := genuineCurvTraceFixedFramePureR_contMDiff (I := I) g s
    (W := fun b : M => Y b) (B := B) (S := fun y : M => S.toSection y) hY hB
    S.toSection.contMDiff_toFun
  refine htrace.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z) x)
    (pureRDirCLMFixedFrame_apply_smooth (I := I) (M := M) g s S hY hB x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_homSection_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.pureRDirCLMFixedFrame_homSection_contMDiff target :: scope.openDecls } }

noncomputable def genuineCurvPureRFibFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace 0 (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 s x (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma genuineCurvPureRFibFixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S (smoothOrthoFrame (I := I) g x) x =
      genuineCurvPureRFib (I := I) (M := M) g s S x := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame_smoothOrthoFrame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame_smoothOrthoFrame target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem genuineCurvPureRFibFixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 s).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y) x
            (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 s).toDiffeomorph.contMDiff.comp
      (pureRDirCLMFixedFrame_homSection_contMDiff (I := I) (M := M) g s S hB)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 s x
    (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFibFixedFrame_contMDiff target :: scope.openDecls } }

private noncomputable def pureRValuedBilinAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Π b : M, TangentSpace I b) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : TopologicalSpace (TensorRSSpace 0 s I y) :=
    tensorRSSpaceTopologicalSpace 0 s y
  letI : AddCommGroup (TensorRSSpace 0 s I y) := tensorRSSpaceAddCommGroup 0 s y
  letI : Module ℝ (TensorRSSpace 0 s I y) := tensorRSSpaceModule 0 s y
  letI : ContinuousAdd (TensorRSSpace 0 s I y) := tensorRSSpace_continuousAdd 0 s y
  letI : ContinuousSMul ℝ (TensorRSSpace 0 s I y) := tensorRSSpace_continuousSMul 0 s y
  letI : AddCommMonoid (TensorRSSpace 0 s I y →L[ℝ] TensorRSSpace 0 s I y) :=
    ContinuousLinearMap.addCommMonoid
  letI : ContinuousAdd (TensorRSSpace 0 s I y →L[ℝ] TensorRSSpace 0 s I y) :=
    inferInstance
  letI : AddCommMonoid
      (TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y →L[ℝ] TensorRSSpace 0 s I y) :=
    ContinuousLinearMap.addCommMonoid
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g 0 s) y X (W y)).comp
        ((tensorCov (I := I) g 0 s).toFun (fun b : M => S.toSection b) y)
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          (riemannOp (tensorCov (I := I) g 0 s) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 s) y).map_smul c X] }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRValuedBilinAt_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Π b : M, TangentSpace I b) (y : M) (X Y : TangentSpace I y) :
    pureRValuedBilinAt (I := I) (M := M) g s S W y X Y =
      riemannOp (tensorCov (I := I) g 0 s) y X (W y)
        ((tensorCov (I := I) g 0 s).toFun (fun b : M => S.toSection b) y Y) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt_apply target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRValuedBilinAt_frame_summand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    pureRValuedBilinAt (I := I) (M := M) g s S W x (B i x) (B i x) =
      riemannSec (tensorCov (I := I) g 0 s) (B i) W
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y)) x := by
  classical
  rw [pureRValuedBilinAt_apply]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  exact happly

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt_frame_summand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.pureRValuedBilinAt_frame_summand target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem genuineCurvTraceFixedFramePureR_frame_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hC : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (C i))) (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W B (fun b : M => S.toSection b) y =
      genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W C (fun b : M => S.toSection b) y := by
  classical
  have : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  have : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have : T2Space (TensorRSSpace 0 s I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y))
  have : FiniteDimensional ℝ (TensorRSSpace 0 s I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y))
  set scalarize : TensorRSSpace 0 s I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T) D) m
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) m =
            Tensor0SSpace.toModel (T D) m + Tensor0SSpace.toModel (T' D) m
          rw [add_apply, Tensor0SSpace.toModel_add,
            add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) m = c • Tensor0SSpace.toModel (T D) m
          rw [smul_apply, Tensor0SSpace.toModel_smul,
            smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace 0 s I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T) D) m := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp (pureRValuedBilinAt (I := I) (M := M) g s S W y X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y (X + X') Y) =
            scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X Y) +
              scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X' Y)
          rw [map_add (pureRValuedBilinAt (I := I) (M := M) g s S W y) X X',
            add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y (c • X) Y) =
            c • scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X Y)
          rw [map_smul (pureRValuedBilinAt (I := I) (M := M) g s S W y) c X,
            smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          pureRValuedBilinAt (I := I) (M := M) g s S W y X Y) D) m := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]
  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F i))) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W F (fun b : M => S.toSection b) y)
            D) m =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F hF
    have hsum_apply :
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s W F (fun b : M => S.toSection b) y) D
            =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            riemannSec (tensorCov (I := I) g 0 s) (F i) W
              (covApply (tensorCov (I := I) g 0 s) (F i) (fun b : M => S.toSection b)) y) D := by
      rw [genuineCurvTraceFixedFrameCurvatureOnly, sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRValuedBilinAt_frame_summand (I := I) (M := M) g s S hW hF i y]
  rw [hframe B hB, hframe C hC]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_frame_independent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvTraceFixedFramePureR_frame_independent target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
private lemma genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    genuineCurvPureRFib (I := I) (M := M) g s S y =
      genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S
        (smoothOrthoFrame (I := I) g x₀) y := by
  classical
  rw [genuineCurvPureRFib, genuineCurvPureRFibFixedFrame]
  congr 1
  refine ContinuousLinearMap.ext (fun v => ?_)
  have hRHS : pureRDirCLMFixedFrame (I := I) (M := M) g s S
        (smoothOrthoFrame (I := I) g x₀) y v =
      genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s (smoothExtensionTangent (I := I) y v)
        (smoothOrthoFrame (I := I) g x₀) (fun b : M => S.toSection b) y := by
    rw [show v = (smoothExtensionTangent (I := I) y v) y from
      (smoothExtensionTangent_eq y v).symm]
    rw [pureRDirCLMFixedFrame_apply_smooth (I := I) (M := M) g s S
      (smoothExtensionTangent_contMDiff y v)
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y]
    rw [smoothExtensionTangent_eq y v]
  rw [genuinePureRDirCLM_apply_extend (I := I) (M := M) g s S y v, hRHS]
  exact genuineCurvTraceFixedFramePureR_frame_independent (I := I) (M := M) g s S
    (smoothExtensionTangent_contMDiff y v)
    (fun i => smoothOrthoFrame_smooth (I := I) g y i)
    (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
private theorem genuineCurvPureRFib_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y
        (genuineCurvPureRFib (I := I) (M := M) g s S y)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y
        (genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S
          (smoothOrthoFrame (I := I) g x₀) y)) x₀ :=
    genuineCurvPureRFibFixedFrame_contMDiff (I := I) (M := M) g s S
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y)
    (genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood (I := I) (M := M) g s S x₀ hy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRFib_contMDiff target :: scope.openDecls } }

private noncomputable def genuineCurvPureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun y : M => genuineCurvPureRFib (I := I) (M := M) g s S y
      contMDiff_toFun := genuineCurvPureRFib_contMDiff (I := I) (M := M) g s S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection target :: scope.openDecls } }

omit [I.Boundaryless] in
@[simp] lemma genuineCurvPureRSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineCurvPureRSection (I := I) (M := M) g s S).toSection x =
      genuineCurvPureRFib (I := I) (M := M) g s S x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection_toSection ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvPureRSection_toSection

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private lemma smoothOrthoFrame_parseval_expand
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) u • (smoothOrthoFrame (I := I) g x a x) := by
  classical
  have : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard)
      i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ E), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ E),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), _root_.MulZeroClass.mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_parseval_expand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.smoothOrthoFrame_parseval_expand target :: scope.openDecls } }

noncomputable def genuineCurvatureOnlySection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  genuineCurvPureRSection (I := I) (M := M) g s S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlySection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlySection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlySection ``Submission.DifferentialGeometry.Geometry.Curvature.genuineCurvatureOnlySection

omit [I.Boundaryless] in
theorem GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → E),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m := by
  classical
  refine ⟨Module.finrank ℝ E, fun a => smoothOrthoFrame (I := I) g x a x, rfl,
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j, fun w m => ?_⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have hexp : ∀ u : TangentSpace I x, u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (e a) u • e a := fun u =>
    smoothOrthoFrame_parseval_expand (I := I) (M := M) g x u
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (genuineCurvPureRSection (I := I) (M := M) g s S).toSection x)
        (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
    genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m
  rw [genuineCurvPureRSection_toSection]
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      genuineCurvPureRFib (I := I) (M := M) g s S x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFibPureR]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_genuineCurvPureRFib_unit (I := I) (M := M) g s S x (e a)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR ``Submission.DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR

noncomputable def fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun x : M => genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x
      contMDiff_toFun := genuineCurvPureRFibFixedFrame_contMDiff (I := I) (M := M) g s S hB }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection ``Submission.DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem fixedFramePureRSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) (x : M) :
    (fixedFramePureRSection (I := I) (M := M) g s S B hB).toSection x =
      genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection_toSection ``Submission.DifferentialGeometry.Geometry.Curvature.fixedFramePureRSection_toSection

omit [I.Boundaryless] in
theorem GcurvSection_toSection_eventuallyEq_fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x₀ : M)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x₀ i))) :
    ∀ᶠ y in 𝓝 x₀,
      (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection y =
        (fixedFramePureRSection (I := I) (M := M) g s S
          (smoothOrthoFrame (I := I) g x₀) hB).toSection y := by
  filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with y hy
  rw [genuineCurvatureOnlySection, genuineCurvPureRSection_toSection,
    fixedFramePureRSection_toSection]
  exact genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_neighborhood (I := I) (M := M) g s S x₀ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eventuallyEq_fixedFramePureRSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eventuallyEq_fixedFramePureRSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eventuallyEq_fixedFramePureRSection ``Submission.DifferentialGeometry.Geometry.Curvature.GcurvSection_toSection_eventuallyEq_fixedFramePureRSection

end Curvature
end Geometry
end DifferentialGeometry

end
