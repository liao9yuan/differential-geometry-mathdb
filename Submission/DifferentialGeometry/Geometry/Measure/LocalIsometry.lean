import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Submission.DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import Submission.DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Measure

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens N) : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens N) : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }

theorem riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {S : Set M} (hS : MeasurableSet S) :
    riemannianVolumeMeasure I M g S = riemannianVolumeMeasure J N h (f '' S) := by
  let V := hf.image
  let e := diffeomorphOntoImage f hf hinj
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  have he (x : M) : (e x : N) = f x := diffeomorphOntoImage_apply f hf hinj x
  have hpull : g = Diffeomorph.pullbackMetricCross (h.restrictOpen V) e := by
    change g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric x v w
  rw [hpull, riemannianVolumeMeasure_pullback_cross]
  rw [Measure.map_apply e.symm.contMDiff.continuous.measurable hS]
  have hopen : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have himage : MeasurableSet (f '' S) :=
    hopen.measurableEmbedding.measurableSet_image.mpr hS
  have hpre : e.symm ⁻¹' S = (Subtype.val : V → N) ⁻¹' (f '' S) := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, (he (e.symm y)).symm.trans (congrArg Subtype.val (e.apply_symm_apply y))⟩
    · rintro ⟨q, hq, hqy⟩
      have heq : e q = y := Subtype.ext ((he q).trans hqy)
      change e.symm y ∈ S
      rw [← heq, e.symm_apply_apply]
      exact hq
  rw [hpre]
  exact riemannianVolumeMeasure_restrictOpen_preimage_of_subset h V himage
    (by rintro _ ⟨q, _, rfl⟩; exact ⟨q, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry

theorem riemannianVolumeMeasure_map_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) :
    Measure.map f (riemannianVolumeMeasure I M g) =
      (riemannianVolumeMeasure J N h).restrict (_root_.Set.range f) := by
  have hfmeas := hf.contMDiff.continuous.measurable
  ext S hS
  rw [Measure.map_apply hfmeas hS, Measure.restrict_apply hS,
    riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      g h f hf hinj hmetric (hfmeas hS), _root_.Set.image_preimage_eq_inter_range]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry

theorem riemannianVolumeMeasure_map_restrict_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (S : Set M) :
    Measure.map f ((riemannianVolumeMeasure I M g).restrict S) =
      (riemannianVolumeMeasure J N h).restrict (f '' S) := by
  have hopen : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have hemb := hopen.measurableEmbedding
  conv_lhs => rw [← hinj.preimage_image S]
  rw [← hemb.restrict_map,
    riemannianVolumeMeasure_map_of_injective_local_isometry g h f hf hinj hmetric,
    Measure.restrict_restrict_of_subset (_root_.Set.image_subset_range _ _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_restrict_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_restrict_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_restrict_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_map_restrict_of_injective_local_isometry

theorem setLIntegral_image_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (S : Set M) (u : N → ℝ≥0∞) :
    ∫⁻ y in f '' S, u y ∂riemannianVolumeMeasure J N h =
      ∫⁻ x in S, u (f x) ∂riemannianVolumeMeasure I M g := by
  have hopen : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  rw [← riemannianVolumeMeasure_map_restrict_of_injective_local_isometry
    g h f hf hinj hmetric S]
  exact hopen.measurableEmbedding.lintegral_map u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.setLIntegral_image_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.setLIntegral_image_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.setLIntegral_image_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Measure.setLIntegral_image_of_injective_local_isometry



theorem riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (x : M) (r : ℝ) :
    riemannianVolumeMeasure I M g (riemannianBallOf g x r) ≤
      riemannianVolumeMeasure J N h (riemannianBallOf h (f x) r) := by
  have hopen : IsOpen (riemannianBallOf g x r) :=
    isOpen_lt (Riemannian.continuous_riemannianEDist g x) continuous_const
  rw [riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    g h f hf hinj hmetric hopen.measurableSet]
  apply _root_.MeasureTheory.measure_mono
  rintro _ ⟨y, hy, rfl⟩
  have hd := edistOf_le_of_quad_of_localDiffeomorph g h f hf zero_lt_one
    (fun z v => by rw [one_mul, hmetric z v v]) x y
  simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
  exact hd.trans_lt hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry

end DifferentialGeometry.Geometry.Measure

end

noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Measure

universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [SigmaCompactSpace M] [SigmaCompactSpace N]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_2 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_3 : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }

theorem riemannianVolumeMeasure_ball_eq_of_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    (p : M) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) p R)) :
    riemannianVolumeMeasure I M (localPullMetric g f hf)
        (riemannianBallOf (localPullMetric g f hf) p r) =
      riemannianVolumeMeasure I N g (riemannianBallOf g (f p) r) := by
  have hmeas : MeasurableSet (riemannianBallOf (localPullMetric g f hf) p r) :=
    (isOpen_lt (Riemannian.continuous_riemannianEDist _ p) continuous_const).measurableSet
  rw [riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (localPullMetric g f hf) g f hf hinj (localPullMetric_inner g f hf) hmeas]
  rw [Metric.image_riemannianBallOf_localPullMetric g f hf hinj p hr hrR hcpt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric

end DifferentialGeometry.Geometry.Measure
