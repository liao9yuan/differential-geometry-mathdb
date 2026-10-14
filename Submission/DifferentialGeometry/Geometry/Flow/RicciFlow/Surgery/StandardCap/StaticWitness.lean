import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticThresholds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FixedRegionMargin
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse
import Submission.DifferentialGeometry.Geometry.Neck.InsertionOrientation
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.IsManifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Cap target :: scope.openDecls } }
private abbrev Retained (δ : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) δ⁻¹

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Retained target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
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
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) Cap) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) Cap) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceCap target :: scope.openDecls } }
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
private local instance quotientRegularSpace {B : ℝ} {hB : 0 < B} :
    RegularSpace (InsertionQuotient hB) :=
  (radialCapAttachmentHomeomorph transitionEnd_pos hB).isEmbedding.isInducing.regularSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientRegularSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientRegularSpace target :: scope.openDecls } }
private def capTip : Cap := ⟨0, by simpa using transitionEnd_pos.le⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capTip
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capTip target :: scope.openDecls } }
private def radialCapPoint (r : ℝ) (hr : r ∈ _root_.Set.Icc (0 : ℝ) transitionEnd) (y : S2) : Cap :=
  ⟨r • y.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1,
      mem_sphere_zero_iff_norm.mp y.property, mul_one]
    exact hr.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialCapPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialCapPoint target :: scope.openDecls } }
private def deepCapPoint (A : ℝ) (x : deepRegion A) : Cap :=
  ⟨x.val, x.property.trans ((fixed_radii_bounds A).2.2.1.le.trans (min_le_right _ _))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deepCapPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.deepCapPoint target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
private abbrev Plus (d : normalizedDatum g x₀ δ k) := InsertionQuotient (inv_pos.mpr d.precision_pos)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.Plus
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.Plus target :: scope.openDecls } }
private local instance imageRegularSpace (d : normalizedDatum g x₀ δ k) : RegularSpace d.controlledImage :=
  d.controlledChart.symm.toHomeomorph.isEmbedding.isInducing.regularSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.imageRegularSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.imageRegularSpace target :: scope.openDecls } }

structure StaticInsertionData (d : normalizedDatum g x₀ δ k) (A D : ℝ) where
  quotientDiffeomorph : Plus d ≃ₘ⟮𝓡 3, 𝓡 3⟯ Plus d
  gluingDiffeomorph :
    letI := retainedFaceChartedSpace (inv_pos.mpr d.precision_pos)
    BoundaryManifold (𝓡∂ 3) Cap ≃ₘ⟮𝓡 2, 𝓡 2⟯ retainedFace δ⁻¹
  capInclusion : Cap → Plus d
  retainedInclusion : Retained δ → Plus d
  tip : Plus d
  outMetric : SmoothRiemannianMetric (𝓡 3) (Plus d)
  windowMap : modelWindow (D + 1) → Plus d
  capMap : Cap → Plus d
  deepMap : deepRegion A → Plus d
  profileTip : ℝ
  profile : ℝ → ℝ
  collapse : d.oriented.controlledImage → Plus d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionData ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionData

structure StaticInsertionProperties (d : normalizedDatum g x₀ δ k)
    (A : ℝ) (hA : 0 < A) (D : ℝ) (m : ℕ) (ε : ℝ)
    (s : StaticInsertionData d A D) : Prop where
  secondCountable : SecondCountableTopology (Plus d)
  boundary_empty : (𝓡 3).boundary (Plus d) = ∅
  cut_fit : 2 * A < δ⁻¹
  window_fit : D + 1 ≤ transitionEnd + δ⁻¹
  quotientDiffeomorph_eq : s.quotientDiffeomorph = Diffeomorph.refl (𝓡 3) (Plus d) ∞
  gluingDiffeomorph_eq : s.gluingDiffeomorph =
    radialCapGluingDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)
  capInclusion_eq : s.capInclusion =
    adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary (inv_pos.mpr d.precision_pos))
  retainedInclusion_eq : s.retainedInclusion =
    adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary (inv_pos.mpr d.precision_pos))
  gluing_coherence : ∀ b : BoundaryManifold (𝓡∂ 3) Cap,
    s.capInclusion b.val = s.retainedInclusion (s.gluingDiffeomorph b).val
  cap_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ s.capInclusion
  retained_embedding :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
    _root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞ s.retainedInclusion
  inclusions_cover : _root_.Set.range s.capInclusion ∪ _root_.Set.range s.retainedInclusion = _root_.Set.univ
  inclusions_inter : _root_.Set.range s.capInclusion ∩ _root_.Set.range s.retainedInclusion =
    _root_.Set.range (s.capInclusion ∘ radialCapBoundary transitionEnd_pos)
  tip_eq : s.tip = s.capInclusion capTip
  tip_interior : ∃ b : Cap, b ∉ (𝓡∂ 3).boundary Cap ∧ s.capInclusion b = s.tip
  outMetric_eq : s.outMetric = d.oriented.positiveSideInsertionMetric hA cut_fit
  retained_metric :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
    ∀ (q : Retained δ) (v w : TangentSpace IR q),
      s.outMetric.inner (s.retainedInclusion q)
        (mfderiv IR (𝓡 3) s.retainedInclusion q v) (mfderiv IR (𝓡 3) s.retainedInclusion q w) =
      g.inner (d.oriented.positiveRetainedMap q)
        (mfderiv IR I d.oriented.positiveRetainedMap q v) (mfderiv IR I d.oriented.positiveRetainedMap q w)
  windowMap_eq : s.windowMap = modelWindowMap (inv_pos.mpr d.precision_pos) window_fit
  window_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ s.windowMap
  window_local : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ s.windowMap
  window_tip_mem : (0 : E3) ∈ modelWindow (D + 1)
  window_pointed : s.windowMap ⟨0, window_tip_mem⟩ = s.tip
  window_close : metricDerivENormSupOn
    {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric (metricScalarAt g x₀) d.scalar_pos s.outMetric)
      s.windowMap window_local window_embedding.isEmbedding.injective)
    (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
      ENNReal.ofReal ε
  capMap_eq : s.capMap = s.capInclusion
  capMap_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ s.capMap
  capMap_image : _root_.Set.range s.capMap = _root_.Set.range s.capInclusion
  capMap_boundary : ∀ y : S2, s.capMap (radialCapBoundary transitionEnd_pos y) =
    s.retainedInclusion (retainedBoundary (inv_pos.mpr d.precision_pos) y)
  capMap_tip : s.capMap capTip = s.tip
  deepMap_eq : s.deepMap = s.capMap ∘ deepCapPoint A
  deep_in_window : ∀ x : deepRegion A, x.val ∈ modelWindow (D + 1)
  window_deep_agrees : ∀ x : deepRegion A, s.windowMap ⟨x.val, deep_in_window x⟩ = s.deepMap x
  profileTip_eq : s.profileTip = collapseTip A
  profileTip_location : s.profileTip ∈ _root_.Set.Ioo (-δ⁻¹) (-2 * A - transitionEnd)
  profile_eq : s.profile = collapseRadius A
  profile_smooth : ContDiff ℝ ∞ s.profile
  profile_monotone : Monotone s.profile
  profile_mapsTo : _root_.Set.MapsTo s.profile (_root_.Set.Icc s.profileTip 0) (_root_.Set.Icc 0 transitionEnd)
  profile_tip : s.profile s.profileTip = 0
  profile_zero : s.profile 0 = transitionEnd
  profile_speed : ∀ z : ℝ, deriv s.profile z ∈ _root_.Set.Icc (0 : ℝ) 1
  profile_linear : ∃ σ : ℝ, 0 < σ ∧ ∀ z : ℝ, z ≤ s.profileTip + σ → s.profile z = z - s.profileTip
  profile_collar : ∀ z ∈ _root_.Set.Icc (-2 * A) 0, s.profile z = conformalRadius z
  originalImage_eq : d.oriented.controlledImage = d.controlledImage
  collapse_eq : s.collapse = d.oriented.positiveSideQuotientCollapseMap hA cut_fit
  collapse_locallyLipschitz : ∀ p, ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
    riemannianEDistOf s.outMetric (s.collapse x) (s.collapse y) ≤
      L * riemannianEDistOf (g.restrictOpen d.oriented.controlledImage) x y
  collapse_retained : ∀ q : Retained δ,
    s.collapse ⟨d.oriented.positiveRetainedMap q, d.oriented.positiveRetainedMap_mem_controlledImage q⟩ =
      s.retainedInclusion q
  collapse_collapsed : ∀ (q : openCylinder δ⁻¹), q.val.2 ≤ s.profileTip →
    s.collapse ⟨d.oriented.controlledMap q, d.oriented.controlledMap_mem_controlledImage q⟩ = s.tip
  collapse_radial : ∀ (q : openCylinder δ⁻¹) (hq : q.val.2 ∈ _root_.Set.Icc s.profileTip 0),
    s.collapse ⟨d.oriented.controlledMap q, d.oriented.controlledMap_mem_controlledImage q⟩ =
      s.capMap (radialCapPoint (s.profile q.val.2) (profile_mapsTo hq) q.val.1)
  collapse_length : ∀ (γ : ℝ → d.oriented.controlledImage) (a b : ℝ), ContinuousOn γ (_root_.Set.Icc a b) →
    DifferentialGeometry.Geometry.riemannianCurveVariation s.outMetric (s.collapse ∘ γ) a b ≤
      DifferentialGeometry.Geometry.riemannianCurveVariation
        (g.restrictOpen d.oriented.controlledImage) γ a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionProperties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionProperties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionProperties ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.StaticInsertionProperties

structure CanonicalStaticInsertionWitness (d : normalizedDatum g x₀ δ k)
    (A : ℝ) (hA : 0 < A) (D : ℝ) (m : ℕ) (ε : ℝ) where
  data : StaticInsertionData d A D
  properties : StaticInsertionProperties d A hA D m ε data

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

def canonicalStaticInsertionWitness (d : normalizedDatum g x₀ δ k)
    (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 < D) (m : ℕ) (ε : ℝ)
    (hAB : 2 * A < δ⁻¹) (hfit : D + 1 ≤ transitionEnd + δ⁻¹)
    (htipLocation : collapseTip A ∈ _root_.Set.Ioo (-δ⁻¹) (-2 * A - transitionEnd))
    (hclose : metricDerivENormSupOn
      {x : modelWindow (D + 1) | (riemannianEDistOf metric 0 x.val).toReal < D} m
      (modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.oriented.positiveSideInsertionMetric hA hAB)))
      (metric.restrictOpen (modelWindow (D + 1))) (metric.restrictOpen (modelWindow (D + 1))) <
        ENNReal.ofReal ε) : CanonicalStaticInsertionWitness d A hA D m ε := by
  let hB := inv_pos.mpr d.precision_pos
  let cap := adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
  let ret := adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
  have hzero : ‖(0 : E3)‖ < D + 1 := by simp only [norm_zero]; linarith
  let s : StaticInsertionData d A D :=
    { quotientDiffeomorph := Diffeomorph.refl (𝓡 3) (Plus d) ∞
      gluingDiffeomorph := radialCapGluingDiffeomorph transitionEnd_pos hB
      capInclusion := cap
      retainedInclusion := ret
      tip := cap capTip
      outMetric := d.oriented.positiveSideInsertionMetric hA hAB
      windowMap := modelWindowMap hB hfit
      capMap := cap
      deepMap := cap ∘ deepCapPoint A
      profileTip := collapseTip A
      profile := collapseRadius A
      collapse := d.oriented.positiveSideQuotientCollapseMap hA hAB }
  refine ⟨s, ?_⟩
  refine
    { secondCountable := radialCapAttachment_secondCountableTopology transitionEnd_pos hB
      boundary_empty := radialCapAttachment_boundary_eq_empty transitionEnd_pos hB
      cut_fit := hAB
      window_fit := hfit
      quotientDiffeomorph_eq := rfl
      gluingDiffeomorph_eq := rfl
      capInclusion_eq := rfl
      retainedInclusion_eq := rfl
      gluing_coherence := radialCapGluingDiffeomorph_coherence transitionEnd_pos hB
      cap_embedding := isSmoothEmbedding_radialCapAttachment_cap transitionEnd_pos hB
      retained_embedding := isSmoothEmbedding_radialCapAttachment_retained transitionEnd_pos hB
      inclusions_cover := radialCapAttachment_inclusions_cover transitionEnd_pos hB
      inclusions_inter := radialCapAttachment_inclusions_inter transitionEnd_pos hB
      tip_eq := rfl
      tip_interior := ⟨capTip, (radialCapAttachment_tip_interior transitionEnd_pos hB).1, rfl⟩
      outMetric_eq := rfl
      retained_metric := d.oriented.positiveSideInsertionMetric_retained hA hAB
      windowMap_eq := rfl
      window_embedding := isSmoothEmbedding_modelWindowMap hB hfit
      window_local := modelWindowMap_isLocalDiffeomorph hB hfit
      window_tip_mem := hzero
      window_pointed := modelWindowMap_agrees_cap hB hfit capTip hzero
      window_close := hclose
      capMap_eq := rfl
      capMap_embedding := isSmoothEmbedding_radialCapAttachment_cap transitionEnd_pos hB
      capMap_image := rfl
      capMap_boundary := adjunction_coherence (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
      capMap_tip := rfl
      deepMap_eq := rfl
      deep_in_window := fun x => (fixed_deep_mem_modelWindow A D hD) x.property
      window_deep_agrees := fun x => modelWindowMap_agrees_cap hB hfit (deepCapPoint A x)
        ((fixed_deep_mem_modelWindow A D hD) x.property)
      profileTip_eq := rfl
      profileTip_location := htipLocation
      profile_eq := rfl
      profile_smooth := contDiff_collapseRadius A
      profile_monotone := monotone_collapseRadius A
      profile_mapsTo := collapseRadius_mapsTo hA
      profile_tip := collapseRadius_tip A
      profile_zero := collapseRadius_zero hA
      profile_speed := deriv_collapseRadius_mem_Icc A
      profile_linear := collapseRadius_linear_germ A
      profile_collar := fun _ hz => collapseRadius_eq_conformalRadius hz.1
      originalImage_eq := d.oriented_controlledImage
      collapse_eq := rfl
      collapse_locallyLipschitz := d.oriented.positiveSideQuotientCollapseMap_local_intrinsic_bound hA hAB
      collapse_retained := d.oriented.positiveSideQuotientCollapseMap_retained hA hAB
      collapse_collapsed := d.oriented.positiveSideQuotientCollapseMap_collapsed hA hAB
      collapse_radial := d.oriented.positiveSideQuotientCollapseMap_radial hA hAB
      collapse_length := ?_ }
  intro γ a b hγ
  exact d.oriented.positiveSideQuotientCollapseMap_eVariationOn_le hA hAB γ a b hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.canonicalStaticInsertionWitness

theorem exists_canonicalStaticInsertionWitness :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧
      ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
        ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
          Nonempty (CanonicalStaticInsertionWitness d A hA D m ε) := by
  obtain ⟨_, _, A, hA, hsmall, hmod⟩ := exists_uniform_positiveCoordinate_static_estimates
  refine ⟨A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, hhalf, hb⟩ := hmod D hD m ε hε
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hle
  obtain ⟨hAB, hfit, htip, hbound⟩ := hb δ hδ hle
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  exact ⟨canonicalStaticInsertionWitness d A hA D hD m ε hAB hfit htip
    (hbound g x₀ d.oriented).1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
