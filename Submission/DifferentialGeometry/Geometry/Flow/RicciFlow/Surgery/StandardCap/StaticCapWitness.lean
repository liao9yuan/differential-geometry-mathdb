import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalCapChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticProfile
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessProducer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Composition
import Submission.DifferentialGeometry.Topology.Manifold.ULift
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientT2Space target :: scope.openDecls } }

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε)

def toStaticCapWitness (hD : 0 < D) :
    StaticCapWitness d.oriented.toNormalizedNeck fixed D m ε := by
  letI := neckRetainedCollarChartedSpace d.precision_pos
  letI := neckRetainedCollar_isManifold d.precision_pos
  letI := threeBallChartedSpace
  letI := threeBall_isManifold
  letI := standardCapCoreChartedSpace
  letI := standardCapCore_isManifold
  letI := w.properties.secondCountable
  letI := uliftChartedSpace ThreeSpace (InsertionQuotient (inv_pos.mpr d.precision_pos))
  letI := isManifold_ulift ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
  letI := staticCapInsertionQuotientChartedSpace d.precision_pos
  let e : InsertionQuotient (inv_pos.mpr d.precision_pos) ≃ₘ⟮ThreeModel, ThreeModel⟯
      ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
    uliftDiffeomorph ThreeModel _
  let up : C(InsertionQuotient (inv_pos.mpr d.precision_pos),
      ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))) := ⟨e, e.continuous⟩
  let liftedMetric := Diffeomorph.pullbackMetricCross w.data.outMetric e.symm
  refine
    { radius_pos := hD
      accuracy_pos := w.accuracy_pos
      Output := ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))
      outputTopology := inferInstance
      outputCharts := inferInstance
      outputSmooth := inferInstance
      outputHausdorff := inferInstance
      outputCountable := e.toHomeomorph.symm.secondCountableTopology
      attaching := Diffeomorph.refl (𝓡 2) (Sphere 2) ∞
      quotientCharts := staticCapInsertionQuotientChartedSpace d.precision_pos
      quotientSmooth := staticCapInsertionQuotient_isManifold d.precision_pos
      quotientPresentation :=
        (staticCapQuotientDiffeomorphInsertionQuotient d.precision_pos).trans e
      retainedCharts := inferInstance
      retainedSmooth := inferInstance
      retained_induced := neckRetainedCollar_inclusion_isSmoothEmbedding d.precision_pos
      ballCharts := inferInstance
      ballSmooth := inferInstance
      ball_induced := isSmoothEmbedding_threeBall_inclusion
      retained := up.comp w.retainedMap
      cap := up.comp w.cap
      retained_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.retainedMap_isSmoothEmbedding e
      cap_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.cap_smooth e
      retained_quotient := ?_
      cap_quotient := ?_
      cover := ?_
      overlap := ?_
      boundary_eq := fun y => congrArg e (w.cap_boundary y)
      tip := e w.data.tip
      tip_interior := ?_
      metric := liftedMetric
      retainedMetric := w.retainedMetric
      retained_metric_output := ?_
      retained_metric_input := w.retained_metric_input_neck
      window := up.comp w.window
      window_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.window_smooth e
      window_tip := fun hx => congrArg e (w.window_tip hx)
      windowMetric := w.windowMetric
      window_inner := ?_
      window_closeness := w.window_closeness
      modelCoreCharts := inferInstance
      modelCoreSmooth := inferInstance
      modelCore_induced := standardCapCore_induced
      capChart := up.comp w.capChart
      capChart_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.capChart_smooth e
      capChart_range := ?_
      capChart_boundary := fun y hx => congrArg e (w.capChart_boundary y hx)
      capChart_tip := fun hx => congrArg e (w.capChart_tip hx)
      window_deep := fun x _ hx hc => congrArg e (w.windowMap_eq_capChart x hx hc)
      tipCoordinate := w.data.profileTip
      tipCoordinate_lower := w.properties.profileTip_location.1
      tipCoordinate_upper := w.properties.profileTip_location.2
      radial := w.data.profile
      radial_continuous := w.properties.profile_smooth.continuous.continuousOn
      radial_monotone := w.properties.profile_monotone.monotoneOn _
      radial_range := w.properties.profile_mapsTo
      radial_smooth := w.properties.profile_smooth.contDiffOn
      radial_tip := w.properties.profile_tip
      radial_boundary := w.properties.profile_zero
      radial_derivative := fun z hz => w.profile_derivWithin_mem_Icc ⟨hz.1.le, hz.2⟩
      radial_tip_germ := w.profile_tip_germ
      radial_collar := fun z hz => w.profile_collar_eq_standardCapRadiusOfZ hz
      collapse := up.comp w.collapse
      collapse_locallyLipschitz := ?_
      collapse_retained := fun x hz => congrArg e (w.collapse_retained x hz)
      collapse_tip := fun x hz => congrArg e (w.collapse_tip x hz)
      collapse_radial := fun x hlo hhi hx => congrArg e (w.collapse_radial x hlo hhi hx)
      collapse_length := ?_ }
  · intro x
    apply congrArg e
    change w.data.retainedInclusion _ = _
    erw [staticCapQuotientDiffeomorphInsertionQuotient_retained, w.properties.retainedInclusion_eq]
  · intro x
    apply congrArg e
    change w.data.capInclusion _ = _
    erw [staticCapQuotientDiffeomorphInsertionQuotient_cap, w.properties.capInclusion_eq]
    rfl
  · change _root_.Set.range (e ∘ w.retainedMap) ∪ _root_.Set.range (e ∘ w.cap) = _root_.Set.univ
    rw [_root_.Set.range_comp, _root_.Set.range_comp, ← _root_.Set.image_union, w.retainedMap_range, w.cap_range,
      _root_.Set.union_comm, w.properties.inclusions_cover, _root_.Set.image_univ]
    exact e.surjective.range_eq
  · change _root_.Set.range (e ∘ w.retainedMap) ∩ _root_.Set.range (e ∘ w.cap) =
      _root_.Set.range (e ∘ (w.cap ∘ sphereToThreeBall))
    rw [_root_.Set.range_comp e w.retainedMap, _root_.Set.range_comp e w.cap,
      _root_.Set.range_comp e (w.cap ∘ sphereToThreeBall)]
    have hi : _root_.Function.Injective (e : InsertionQuotient (inv_pos.mpr d.precision_pos) →
        ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))) := e.injective
    rw [← _root_.Set.image_inter hi, w.retainedMap_range, w.cap_range, _root_.Set.inter_comm,
      w.properties.inclusions_inter]
    rfl
  · obtain ⟨x, hx, he⟩ := w.cap_tip_interior
    exact ⟨x, hx, congrArg e he⟩
  · intro x V W
    change w.retainedMetric.inner x V W =
      liftedMetric.inner (e (w.retainedMap x))
        (mfderiv (𝓡∂ 3) ThreeModel (e ∘ w.retainedMap) x V)
        (mfderiv (𝓡∂ 3) ThreeModel (e ∘ w.retainedMap) x W)
    rw [DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner
      w.data.outMetric e w.retainedMap w.retainedMap_contMDiff]
    exact w.retained_metric_output x V W
  · intro x V W
    change w.windowMetric.inner x V W = metricScalarAt g x₀ *
      liftedMetric.inner (e (w.window x))
        (mfderiv ThreeModel ThreeModel (e ∘ w.window) x V)
        (mfderiv ThreeModel ThreeModel (e ∘ w.window) x W)
    rw [DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner
      w.data.outMetric e w.window w.window_smooth.contMDiff]
    exact w.window_inner x V W
  · change _root_.Set.range (e ∘ w.capChart) = _root_.Set.range (e ∘ w.cap)
    rw [_root_.Set.range_comp, _root_.Set.range_comp, w.capChart_range_cap]
  · intro x
    obtain ⟨U, hU, L, hL⟩ := w.collapse_locallyLipschitz x
    refine ⟨U, hU, L, ?_⟩
    intro y hy z hz
    change riemannianEDistOf liftedMetric (e (w.collapse y)) (e (w.collapse z)) ≤ _
    rw [DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross]
    simp only [Diffeomorph.symm_apply_apply]
    exact hL y hy z hz
  · intro γ a b _ hγ _
    have h := w.collapse_length γ a b hγ
    change DifferentialGeometry.Geometry.riemannianCurveVariation liftedMetric
      (e ∘ w.collapse ∘ γ) a b ≤
        riemannianCurveLength g (fun t => d.oriented.map (γ t).1) a b
    unfold DifferentialGeometry.Geometry.riemannianCurveVariation
    simp only [liftedMetric, Function.comp_apply,
      DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross,
      Diffeomorph.symm_apply_apply]
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.toStaticCapWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.toStaticCapWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.toStaticCapWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.toStaticCapWitness

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
