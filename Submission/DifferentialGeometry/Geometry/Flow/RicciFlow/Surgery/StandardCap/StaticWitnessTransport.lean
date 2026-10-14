import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionNaturality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap : ChartedSpace (EuclideanHalfSpace 3) Cap := closedBallChartedSpace transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatCap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap : IsManifold (𝓡∂ 3) ∞ Cap := closedBall_isManifold transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopCap target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

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
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

variable {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

theorem CanonicalStaticInsertionWitness.canonical_window_close
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    metricDerivENormSupOn
      {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
      (modelWindowPullback (inv_pos.mpr d.precision_pos) w.properties.window_fit
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos
          (d.oriented.positiveSideInsertionMetric hA w.properties.cut_fit)))
      (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
      ENNReal.ofReal ε := by
  simpa only [w.properties.outMetric_eq, w.properties.windowMap_eq, modelWindowPullback] using
    w.properties.window_close

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.canonical_window_close

variable {E' H' N : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g' : SmoothRiemannianMetric J N} {x₀' : N} {d' : normalizedDatum g' x₀' δ k}

structure StaticInsertionGeometryEq
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (w' : CanonicalStaticInsertionWitness d' A hA D m ε) : Prop where
  quotient : w'.data.quotientDiffeomorph = w.data.quotientDiffeomorph
  gluing : w'.data.gluingDiffeomorph = w.data.gluingDiffeomorph
  capInclusion : w'.data.capInclusion = w.data.capInclusion
  retainedInclusion : w'.data.retainedInclusion = w.data.retainedInclusion
  tip : w'.data.tip = w.data.tip
  window : w'.data.windowMap = w.data.windowMap
  cap : w'.data.capMap = w.data.capMap
  deep : w'.data.deepMap = w.data.deepMap
  profileTip : w'.data.profileTip = w.data.profileTip
  profile : w'.data.profile = w.data.profile

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionGeometryEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionGeometryEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionGeometryEq ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionGeometryEq

theorem canonicalStaticInsertionWitness_geometry_eq
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (w' : CanonicalStaticInsertionWitness d' A hA D m ε) : StaticInsertionGeometryEq w w' := by
  have hc : w'.data.capInclusion = w.data.capInclusion :=
    w'.properties.capInclusion_eq.trans w.properties.capInclusion_eq.symm
  have hcap : w'.data.capMap = w.data.capMap :=
    w'.properties.capMap_eq.trans (hc.trans w.properties.capMap_eq.symm)
  refine
    { quotient := w'.properties.quotientDiffeomorph_eq.trans w.properties.quotientDiffeomorph_eq.symm
      gluing := w'.properties.gluingDiffeomorph_eq.trans w.properties.gluingDiffeomorph_eq.symm
      capInclusion := hc
      retainedInclusion := w'.properties.retainedInclusion_eq.trans w.properties.retainedInclusion_eq.symm
      tip := ?_
      window := w'.properties.windowMap_eq.trans w.properties.windowMap_eq.symm
      cap := hcap
      deep := ?_
      profileTip := w'.properties.profileTip_eq.trans w.properties.profileTip_eq.symm
      profile := w'.properties.profile_eq.trans w.properties.profile_eq.symm }
  · rw [w'.properties.tip_eq, w.properties.tip_eq, hc]
  · rw [w'.properties.deepMap_eq, w.properties.deepMap_eq, hcap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_geometry_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_geometry_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_geometry_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_geometry_eq

def CanonicalStaticInsertionWitness.transportIsometry
    (w : CanonicalStaticInsertionWitness d A hA D m ε) (F : datumIsometry d d') (hD : 0 < D) :
    CanonicalStaticInsertionWitness d' A hA D m ε := by
  apply canonicalStaticInsertionWitness d' A hA D hD m ε w.properties.cut_fit w.properties.window_fit
  · exact w.properties.profileTip_eq ▸ w.properties.profileTip_location
  · rw [F.oriented.modelWindowPullback_eq hA w.properties.cut_fit w.properties.window_fit]
    exact w.canonical_window_close

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.transportIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.transportIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.transportIsometry ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.transportIsometry

theorem canonicalStaticInsertionWitness_isometry_laws
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (w' : CanonicalStaticInsertionWitness d' A hA D m ε) (F : datumIsometry d d') :
    StaticInsertionGeometryEq w w' ∧ w'.data.outMetric = w.data.outMetric ∧
      ∀ p : d.oriented.controlledImage,
        w'.data.collapse (F.oriented.controlledImageMap p) = w.data.collapse p := by
  refine ⟨canonicalStaticInsertionWitness_geometry_eq w w', ?_, ?_⟩
  · exact w'.properties.outMetric_eq.trans
      ((F.oriented.positiveSideInsertionMetric_eq hA w.properties.cut_fit).trans w.properties.outMetric_eq.symm)
  · intro p
    rw [w'.properties.collapse_eq, w.properties.collapse_eq]
    exact F.oriented.positiveSideQuotientCollapseMap_eq hA w.properties.cut_fit p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_isometry_laws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_isometry_laws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_isometry_laws ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_isometry_laws

def CanonicalStaticInsertionWitness.rescale
    (w : CanonicalStaticInsertionWitness d A hA D m ε) (c : ℝ) (hc : 0 < c) (hD : 0 < D) :
    CanonicalStaticInsertionWitness (d.rescaled c hc) A hA D m ε := by
  apply canonicalStaticInsertionWitness (d.rescaled c hc) A hA D hD m ε
    w.properties.cut_fit w.properties.window_fit
  · exact w.properties.profileTip_eq ▸ w.properties.profileTip_location
  · change metricDerivENormSupOn _ m
      (modelWindowPullback (inv_pos.mpr d.precision_pos) w.properties.window_fit
        (scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (d.oriented.rescaled c hc).scalar_pos
          ((d.oriented.rescaled c hc).positiveSideInsertionMetric hA w.properties.cut_fit))) _ _ < _
    rw [d.oriented.rescaled_modelWindowPullback c hc hA w.properties.cut_fit w.properties.window_fit]
    exact w.canonical_window_close

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.rescale ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.rescale

theorem canonicalStaticInsertionWitness_rescaling_laws
    (w : CanonicalStaticInsertionWitness d A hA D m ε) (c : ℝ) (hc : 0 < c)
    (w' : CanonicalStaticInsertionWitness (d.rescaled c hc) A hA D m ε) :
    StaticInsertionGeometryEq w w' ∧ w'.data.outMetric = scaleMetric c hc w.data.outMetric ∧
      ∀ p : d.oriented.controlledImage, w'.data.collapse p = w.data.collapse p := by
  refine ⟨canonicalStaticInsertionWitness_geometry_eq w w', ?_, ?_⟩
  · exact w'.properties.outMetric_eq.trans
      ((d.oriented.rescaled_positiveSideInsertionMetric c hc hA w.properties.cut_fit).trans
        (congrArg (scaleMetric c hc) w.properties.outMetric_eq.symm))
  · intro p
    rw [w'.properties.collapse_eq, w.properties.collapse_eq]
    exact d.oriented.rescaled_positiveSideQuotientCollapseMap c hc hA w.properties.cut_fit p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_rescaling_laws then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_rescaling_laws"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_rescaling_laws ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness_rescaling_laws
end DifferentialGeometry.PDE.RicciFlow.StandardCap
