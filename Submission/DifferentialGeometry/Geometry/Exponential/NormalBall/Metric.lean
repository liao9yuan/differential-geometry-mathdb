import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [T2Space (TangentBundle I M)]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 target :: scope.openDecls } }

namespace NormalBallChart

def ball {p : M} (c : NormalBallChart (I := I) p) : _root_.TopologicalSpace.Opens E :=
  ⟨Metric.ball (0 : E) c.radius, Metric.isOpen_ball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ball ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ball

def image {p : M} (c : NormalBallChart (I := I) p) : _root_.TopologicalSpace.Opens M :=
  ⟨c.restrictBall.target, c.restrictBall.open_target⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.image ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.image

noncomputable def ballDiffeo {p : M}
    (c : NormalBallChart (I := I) p) :
    Diffeomorph (modelWithCornersSelf Real E) I c.ball c.image ∞ := by
  have hsub : (c.ball : Set E) ⊆ c.restrictBall.source := by
    intro z hz
    exact hz
  let V : _root_.TopologicalSpace.Opens M :=
    ⟨c.restrictBall '' (c.ball : Set E), image_opens_isOpen c.restrictBall hsub⟩
  have hV : V = c.image := by
    apply Opens.ext
    change c.restrictBall '' c.restrictBall.source = c.restrictBall.target
    exact c.restrictBall.toPartialEquiv.image_source_eq_target
  rw [← hV]
  exact PartialDiffeomorph.toOpensDiffeo c.restrictBall hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private theorem ballSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.ball := by
  let : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballSigma target :: scope.openDecls } }

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private theorem imageSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.image := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (c.ballDiffeo : c.ball → c.image) = Set.univ :=
    Set.range_eq_univ.mpr c.ballDiffeo.surjective
  rw [← hrange]
  exact isSigmaCompact_range c.ballDiffeo.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.imageSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.imageSigma target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) :
    ((c.ballDiffeo z : c.image) : M) = c.hom (z : E) := by
  change c.restrictBall (z : E) = c.hom (z : E)
  exact c.restrict_ball_apply (z : E)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_mfd {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v : E) :
    mfderiv (modelWithCornersSelf Real E) I
        (c.ballDiffeo : c.ball → c.image) z v =
      mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => c.hom u) (z : E) v := by
  have hΨd : MDifferentiableAt (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z :=
    c.ballDiffeo.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalImage : MDifferentiableAt I I (Subtype.val : c.image → M) (c.ballDiffeo z) :=
    ((contMDiff_subtype_val (I := I) (U := c.image)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalBall : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (Subtype.val : c.ball → E) z := by
    exact ContMDiffAt.mdifferentiableAt
      (contMDiff_subtype_val (I := modelWithCornersSelf Real E) (U := c.ball)).contMDiffAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hhomd : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun u : E => c.hom u) (z : E) :=
    (c.smooth_to.contMDiffAt (Metric.isOpen_ball.mem_nhds z.2)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hleft : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) z =
        (mfderiv I I (Subtype.val : c.image → M) (c.ballDiffeo z)).comp
          (mfderiv (modelWithCornersSelf Real E) I
            (c.ballDiffeo : c.ball → c.image) z) :=
    mfderiv_comp z hvalImage hΨd
  have hright : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => c.hom (y : E)) z =
        (mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)).comp
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (Subtype.val : c.ball → E) z) :=
    mfderiv_comp z hhomd hvalBall
  have hfun : (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) =
      fun y : c.ball => c.hom (y : E) := by
    funext y
    exact c.ballDiffeo_apply y
  have hfun' : (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) =ᶠ[nhds z]
      fun y : c.ball => c.hom (y : E) :=
    Filter.Eventually.of_forall (fun y => congrFun hfun y)
  have hmap : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) z =
        mfderiv (modelWithCornersSelf Real E) I
          (fun y : c.ball => c.hom (y : E)) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hfun'
  rw [hleft] at hmap
  rw [hright] at hmap
  have hleftId :
      (mfderiv I I (Subtype.val : c.image → M) (c.ballDiffeo z)).comp
          (mfderiv (modelWithCornersSelf Real E) I
            (c.ballDiffeo : c.ball → c.image) z) =
        mfderiv (modelWithCornersSelf Real E) I
          (c.ballDiffeo : c.ball → c.image) z := by
    ext w
    exact mfderiv_subtype_val_apply (I := I) c.image (c.ballDiffeo z) _
  have hrightId :
      (mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)).comp
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (Subtype.val : c.ball → E) z) =
        mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E) := by
    ext w
    change mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)
      (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
        (Subtype.val : c.ball → E) z w) = _
    rw [mfderiv_subtype_val_apply (I := modelWithCornersSelf Real E) c.ball z]
    rfl
  rw [hleftId, hrightId] at hmap
  exact DFunLike.congr_fun hmap v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo_mfd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.ballDiffeo_mfd target :: scope.openDecls } }

noncomputable def localMetric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) c.ball := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  letI : SigmaCompactSpace c.image := c.imageSigma
  exact Diffeomorph.pullbackMetricCross
    (g.restrictOpen (I := I) c.image) c.ballDiffeo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem localMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v w : E) :
    (c.localMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      c.metric g z v w := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  let : SigmaCompactSpace c.image := c.imageSigma
  rw [localMetric, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [ballDiffeo_apply]
  rw [show mfderiv (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v) =
      mfderiv (modelWithCornersSelf Real E) I (fun u : E ↦ c.hom u) (z : E) v by
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      c.ballDiffeo_mfd z v]
  rw [show mfderiv (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      mfderiv (modelWithCornersSelf Real E) I (fun u : E ↦ c.hom u) (z : E) w by
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      c.ballDiffeo_mfd z w]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.localMetric_inner

noncomputable def cut {p : M}
    (c : NormalBallChart (I := I) p) : ContDiffBump (0 : E) :=
  ⟨c.radius / 4, c.radius / 2,
    div_pos c.radius_pos (by norm_num),
    by linarith [c.radius_pos]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_smooth {p : M} (c : NormalBallChart (I := I) p) :
    ContMDiff (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real Real) ∞ (c.cut : E → Real) :=
  c.cut.contDiff.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_smooth ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_smooth

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_range {p : M} (c : NormalBallChart (I := I) p) (z : E) :
    c.cut z ∈ Set.Icc (0 : Real) 1 :=
  ⟨c.cut.nonneg, c.cut.le_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_range ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_range

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_support {p : M} (c : NormalBallChart (I := I) p) :
    tsupport (c.cut : E → Real) ⊆ (c.ball : Set E) := by
  rw [c.cut.tsupport_eq]
  change Metric.closedBall (0 : E) (c.radius / 2) ⊆
    Metric.ball (0 : E) c.radius
  exact Metric.closedBall_subset_ball (by linarith [c.radius_pos])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_support ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_support

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_one {p : M} (c : NormalBallChart (I := I) p)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    c.cut z = 1 :=
  c.cut.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_one ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.cut_one

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem inner_subset {p : M} (c : NormalBallChart (I := I) p) :
    Metric.ball (0 : E) (c.radius / 4) ⊆ (c.ball : Set E) :=
  Metric.ball_subset_ball (by linarith [c.radius_pos])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.inner_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.inner_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.inner_subset ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.inner_subset

private noncomputable def flatMetric :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.flatMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.flatMetric target :: scope.openDecls } }

noncomputable def totalMetric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) E := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  exact (flatMetric (E := E)).bumpExtendOpen c.ball (c.localMetric g)
    (c.cut : E → Real) c.cut_smooth c.cut_range c.cut_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) (v w : E) :
    (c.totalMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      c.metric g z v w := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  let : SigmaCompactSpace c.image := c.imageSigma
  have hsub := c.inner_subset
  calc
    (c.totalMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      (c.localMetric g).inner ⟨z, hsub hz⟩
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) (⟨z, hsub hz⟩ : c.ball)).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) (⟨z, hsub hz⟩ : c.ball)).symm w) := by
      simpa only [totalMetric, tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        bumpExtendOpen_eq_gU_on (I := modelWithCornersSelf Real E)
          (flatMetric (E := E)) c.ball (c.localMetric g)
          (c.cut : E → Real) c.cut_smooth c.cut_range c.cut_support
          (Metric.ball (0 : E) (c.radius / 4))
          (fun q hq => c.cut_one hq) hsub z hz
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm w)
    _ = c.metric g z v w := c.localMetric_inner g ⟨z, hsub hz⟩ v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_inner

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) z
        ((c.totalMetric g).inner z) = c.metric g z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact c.totalMetric_inner g z hz v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.totalMetric_eq

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem total_cov_const (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (v w : E) :
    tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z
        ((Geometry.Connection.leviCivitaConnectionOfMetric
          (I := modelWithCornersSelf Real E)
          (c.totalMetric g) (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)) =
      MetricKoszul.koszulVec (E := E) hco
        (fderiv Real (c.metric g) z) v w := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) y ((c.totalMetric g).inner y)) =ᶠ[nhds z]
          c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_cont_diff_on g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.Submission.DifferentialGeometry.Geometry.Connection.const_cov_eq_nhds
    (c.totalMetric g) (c.metric g) hEq hdiff hco v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_const ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_const

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem total_cov_fderiv (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (V : E → E)
    (_hV : MDifferentiableAt (modelWithCornersSelf Real E)
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real E))
      (fun y : E => (⟨y, (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) y).symm (V y)⟩ : TangentBundle
          (modelWithCornersSelf Real E) E)) z)
    (v : E) :
    tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z
        ((Geometry.Connection.leviCivitaConnectionOfMetric
          (I := modelWithCornersSelf Real E) (c.totalMetric g)
          (fun y : E => (tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) y).symm (V y)) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)) =
      fderiv Real V z v +
        MetricKoszul.koszulVec (E := E) hco
          (fderiv Real (c.metric g) z) v (V z) := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) y ((c.totalMetric g).inner y)) =ᶠ[nhds z]
          c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_cont_diff_on g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.Submission.DifferentialGeometry.Geometry.Connection.cov_eq_fderiv_add
    (c.totalMetric g) (c.metric g) hEq hdiff hco V _hV v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_fderiv ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.total_cov_fderiv

noncomputable def accel (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) : E :=
  -(tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z.1
      ((_root_.Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
        (I := modelWithCornersSelf Real E) (c.totalMetric g)
        (constantModelVectorField z.2) z.1)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z.1).symm z.2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] theorem accel_zero (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    c.accel g (0 : E × E) = 0 := by
  unfold accel
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [_root_.Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply]
  have hz :
      _root_.Submission.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionAt
          (I := modelWithCornersSelf Real E)
          (c.totalMetric g) (constantModelVectorField (0 : E))
          (0 : E) ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) (0 : E)).symm 0) = 0 :=
    ContinuousLinearMap.map_zero _
  rw [hz]
  have hzero : tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) (0 : E) (0 : TangentSpace
        (modelWithCornersSelf Real E) (0 : E)) = 0 :=
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) (0 : E)).map_zero
  rw [hzero, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_zero

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem accel_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E)
    (hz : z.1 ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z.1)) :
    c.accel g z =
      -MetricKoszul.koszulVec (E := E) hco
        (fderiv Real (c.metric g) z.1) z.2 z.2 := by
  unfold accel
  rw [c.total_cov_const g z.1 hz hco z.2 z.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.accel_eq

end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
