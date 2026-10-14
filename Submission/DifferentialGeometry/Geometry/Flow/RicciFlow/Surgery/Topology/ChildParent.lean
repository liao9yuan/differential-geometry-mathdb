import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Dimension.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable (P : OrientedThreeStage.{u})

theorem component_isOpen (c : ConnectedComponents P.Carrier) :
    IsOpen {x : P.Carrier | ConnectedComponents.mk x = c} := by
  let : LocallyConnectedSpace P.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hs : {y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x} =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [hs]
  exact isOpen_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_isOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_isOpen

def componentOpen (c : ConnectedComponents P.Carrier) : TopologicalSpace.Opens P.Carrier :=
  ⟨{x | ConnectedComponents.mk x = c}, P.component_isOpen c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOpen

theorem component_compact (c : ConnectedComponents P.Carrier) : CompactSpace (P.componentOpen c) := by
  apply isCompact_iff_compactSpace.mp
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsCompact {y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x}
  have hs : {y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x} =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [hs]
  exact isClosed_connectedComponent.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_compact

theorem component_connected (c : ConnectedComponents P.Carrier) : ConnectedSpace (P.componentOpen c) := by
  apply isConnected_iff_connectedSpace.mp
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsConnected {y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x}
  have hs : {y : P.Carrier | ConnectedComponents.mk y = ConnectedComponents.mk x} =
      connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [hs]
  exact isConnected_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_connected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component_connected

section OpenOrientation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

private theorem tangentChartEquiv_restrictOpen (U : TopologicalSpace.Opens M) (p x : U)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hxM : x.1 ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p.1).baseSet) :
    tangentChartEquiv U p x hx = tangentChartEquiv M p.1 x.1 hxM := by
  have hu : x ∈ (chartAt ThreeSpace p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hm : x.1 ∈ (chartAt ThreeSpace p.1).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxM
  have hf : (extChartAt ThreeModel p : U → ThreeSpace) =
      (extChartAt ThreeModel p.1) ∘ (Subtype.val : U → M) := rfl
  have hd : mfderiv ThreeModel ThreeModel (extChartAt ThreeModel p) x =
      mfderiv ThreeModel ThreeModel (extChartAt ThreeModel p.1) x.1 := by
    rw [hf, mfderiv_comp x (mdifferentiableAt_extChartAt hm)
      (DifferentialGeometry.hasMFDerivAt_subtype_val U x).mdifferentiableAt,
      DifferentialGeometry.mfderiv_subtype_val]
    ext v
    rfl
  have hc : (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x =
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p.1).continuousLinearMapAt ℝ x.1 := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hu,
      TangentBundle.continuousLinearMapAt_trivializationAt hm]
    exact hd
  apply LinearEquiv.ext
  intro v
  calc
    tangentChartEquiv U p x hx v =
        (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).continuousLinearMapAt ℝ x v :=
      (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p) hx v).symm
    _ = (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p.1).continuousLinearMapAt ℝ x.1 v :=
      congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A v) hc
    _ = tangentChartEquiv M p.1 x.1 hxM v :=
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p.1) hxM v

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tangentChartEquiv_restrictOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tangentChartEquiv_restrictOpen target :: scope.openDecls } }

private def restrictOrientation (o : TangentOrientationSection M)
    (U : TopologicalSpace.Opens M) : TangentOrientationSection U where
  orientation x := o.orientation x.1
  locally_constant := by
    intro p x hx
    have hxM : x.1 ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p.1).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage] using hx
    obtain ⟨V, hVo, hxV, hVm, hV⟩ := o.locally_constant p.1 x.1 hxM
    let W : Set U := Subtype.val ⁻¹' V
    have hWm : W ⊆ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet := by
      intro y hy
      simpa only [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, _root_.Set.mem_preimage] using hVm hy
    refine ⟨W, hVo.preimage continuous_subtype_val, hxV, hWm, ?_⟩
    intro y hy
    rw [tangentChartEquiv_restrictOpen U p y (hWm hy) (hVm hy),
      tangentChartEquiv_restrictOpen U p x hx hxM]
    exact hV y.1 hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.restrictOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.restrictOrientation target :: scope.openDecls } }

end OpenOrientation

def componentOrientation (c : ConnectedComponents P.Carrier) :
    TangentOrientationSection (P.componentOpen c) where
  orientation x := P.orientation.orientation x.1
  locally_constant := (restrictOrientation P.orientation (P.componentOpen c)).locally_constant

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentOrientation

def component (c : ConnectedComponents P.Carrier) : OrientedThreeStage.{u} where
  Carrier := P.componentOpen c
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  hausdorff := inferInstance
  compact := P.component_compact c
  orientation := P.componentOrientation c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.component

def componentMetric (g : P.Metric) (c : ConnectedComponents P.Carrier) : (P.component c).Metric :=
  g.restrictOpen (P.componentOpen c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.componentMetric

end OrientedThreeStage

namespace CutCoreGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem interior_maximal_chart {e e' : OpenPartialHomeomorph M H} {x : M}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn ℝ ∞ φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, ModelWithCorners.extendCoordChange, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Filter.inter_mem_iff,
      mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex (e'.open_source.mem_nhds hex')
  have hsurj : Function.Surjective (fderiv ℝ φ (e.extend I x)) := by
    rw [← fderivWithin_of_mem_nhds hφx]
    exact (I.isInvertible_fderivWithin_extendCoordChange (by simp) he he'
      (by simp [hex, hex'])).surjective
  have hmem : e'.extend I x ∈ interior (_root_.Set.range I) := by
    rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
    have hd : DifferentiableAt ℝ φ (e.extend I x) :=
      (hφ.differentiableOn (by simp)).differentiableAt hφx
    exact hd.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
      I.nonempty_interior (φ.mapsTo.mono_right (by simp [φ, _root_.Set.inter_assoc])) hsurj
  exact e'.mem_interior_extend_target (by simp [hex']) hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCoreGeometry.interior_maximal_chart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCoreGeometry.interior_maximal_chart target :: scope.openDecls } }

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

omit [IsManifold J ∞ N] in
private theorem immersion_image_mem_nhds {f : M → N} {x : M}
    (hf : _root_.Manifold.IsImmersionAt I J ∞ f x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hx : I.IsInteriorPoint x) {s : Set M} (hs : s ∈ 𝓝 x) :
    f '' s ∈ 𝓝 (f x) := by
  obtain ⟨F, hF, hFR, h⟩ := hf
  let := hF
  let := hFR
  let : FiniteDimensional ℝ (E × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  let : FiniteDimensional ℝ F := Module.Finite.of_surjective
    (LinearMap.snd ℝ E F) (fun z => ⟨(0, z), rfl⟩)
  have hzero : Module.finrank ℝ F = 0 := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, ← hdim] at heq
    omega
  let : Subsingleton F := (Module.finrank_zero_iff).mp hzero
  let : Unique F := ⟨⟨0⟩, fun z => Subsingleton.elim z 0⟩
  let A : E ≃L[ℝ] E' := (ContinuousLinearEquiv.prodUnique ℝ E F).symm.trans h.equiv
  have hA (z : E) : A z = h.equiv (z, 0) := rfl
  have hxi : h.domChart.extend I x ∈ interior (h.domChart.extend I).target :=
    interior_maximal_chart (IsManifold.subset_maximalAtlas (chart_mem_atlas H x))
      h.domChart_mem_maximalAtlas (mem_chart_source H x) h.mem_domChart_source
      ((I.isInteriorPoint_iff).mp hx)
  have hxrange : h.domChart.extend I x ∈ interior (_root_.Set.range I) :=
    interior_mono h.domChart.extend_target_subset_range hxi
  have himage : (h.domChart.extend I) '' (s ∩ h.domChart.source) ∈
      𝓝 (h.domChart.extend I x) :=
    h.domChart.extend_image_nhds_mem_nhds_of_mem_interior_range h.mem_domChart_source
      hxrange (Filter.inter_mem hs (h.domChart.open_source.mem_nhds h.mem_domChart_source))
  have hformula (z : M) (hz : z ∈ h.domChart.source) :
      (h.codChart.extend J) (f z) = A ((h.domChart.extend I) z) := by
    have hze : z ∈ (h.domChart.extend I).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hz
    have hnormal := h.writtenInCharts ((h.domChart.extend I).map_source hze)
    simpa only [Function.comp_apply, OpenPartialHomeomorph.extend_source,
      (h.domChart.extend I).left_inv hze, hA] using hnormal
  have htarget : A '' ((h.domChart.extend I) '' (s ∩ h.domChart.source)) ∈
      𝓝 ((h.codChart.extend J) (f x)) := by
    rw [hformula x h.mem_domChart_source]
    exact A.toHomeomorph.isOpenMap.image_mem_nhds himage
  have hpre := (h.codChart.continuousAt_extend h.mem_codChart_source).preimage_mem_nhds htarget
  filter_upwards [hpre, h.codChart.open_source.mem_nhds h.mem_codChart_source] with y hy hys
  obtain ⟨v, ⟨z, hzs, rfl⟩, heq⟩ := hy
  refine ⟨z, hzs.1, ?_⟩
  have hfzOriginal : f z ∈ h.codChart.source := h.source_subset_preimage_source hzs.2
  have hfz : f z ∈ (h.codChart.extend J).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using hfzOriginal
  have hyc : y ∈ (h.codChart.extend J).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using hys
  apply (h.codChart.extend J).injOn hfz hyc
  exact (hformula z hzs.2).trans heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCoreGeometry.immersion_image_mem_nhds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCoreGeometry.immersion_image_mem_nhds target :: scope.openDecls } }

end CutCoreGeometry

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem removedBand_isOpen (a : E.trace.tubes.Index) :
    IsOpen (E.trace.tubes.removedBand a) := by
  let : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨z, hz, rfl⟩
  apply CutCoreGeometry.immersion_image_mem_nhds
    ((E.tube_smooth a).isImmersion.isImmersionAt z)
  · simp [ThreeSpace, Module.finrank_prod]
  · change z ∈ ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint,
      Icc_isInteriorPoint_interior ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
  · exact ((isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)).mem_nhds hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.removedBand_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.removedBand_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.removedBand_isOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.removedBand_isOpen

theorem core_compact : CompactSpace E.trace.tubes.core := by
  apply isCompact_iff_compactSpace.mp
  exact (isOpen_iUnion E.removedBand_isOpen).isClosed_compl.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_compact

theorem core_locallyConnected : LocallyConnectedSpace E.trace.tubes.core := by
  let := E.coreCharts
  exact ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) E.trace.tubes.core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_locallyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_locallyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_locallyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.core_locallyConnected


def childCoreComponent (c : ConnectedComponents Q.Carrier) :
    ConnectedComponents E.trace.tubes.core :=
  letI := E.core_compact
  letI := E.core_locallyConnected
  E.trace.childCore c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreComponent

def childParent (c : ConnectedComponents Q.Carrier) : ConnectedComponents P.Carrier :=
  letI := E.core_compact
  letI := E.core_locallyConnected
  E.trace.rfs_child_parent c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent

abbrev ChildCore (c : ConnectedComponents Q.Carrier) :=
  ComponentCarrier (E.childCoreComponent c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCore

abbrev ParentCarrier (c : ConnectedComponents Q.Carrier) := ComponentCarrier (E.childParent c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ParentCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ParentCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ParentCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ParentCarrier

abbrev ChildCarrier (_E : SmoothCutCapTransition P Q D N)
    (c : ConnectedComponents Q.Carrier) := ComponentCarrier c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCarrier

theorem childCore_mapsTo_child (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    ∃! y : E.ChildCarrier c,
      E.trace.presentation (E.trace.capping.coreInclusion x.1) = Sum.inl y.1 := by
  classical
  let := E.core_compact
  let := E.core_locallyConnected
  obtain ⟨q, hq⟩ := ConnectedComponents.surjective_coe c
  have hcore : E.trace.capping.componentMap (E.childCoreComponent c) = E.trace.cappedChild c :=
    E.trace.capping.componentEquiv.apply_symm_apply _
  have hx := (congrArg E.trace.capping.componentMap x.2).trans hcore
  have hpres :
      ConnectedComponents.mk (E.trace.presentation (E.trace.capping.coreInclusion x.1)) =
        ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ D.Carrier) := by
    have h := congrArg E.trace.presentation.continuous.connectedComponentsMap hx
    simpa [CutCapTopology.cappedChild, ← hq] using h
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  cases hf : E.trace.presentation (E.trace.capping.coreInclusion x.1) with
  | inl y =>
    have hy : ConnectedComponents.mk y = c := by
      have h := congrArg hret.connectedComponentsMap hpres
      simpa [retraction, hf, hq] using h
    refine ⟨⟨y, hy⟩, rfl, ?_⟩
    intro z hz
    apply Subtype.ext
    exact Sum.inl.inj hz.symm
  | inr d =>
    let tag : Q.Carrier ⊕ D.Carrier → Bool := Sum.elim (fun _ => _root_.Bool.false) (fun _ => _root_.Bool.true)
    have htag : Continuous tag := continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩
    have htagEq : (ConnectedComponents.mk _root_.Bool.true : ConnectedComponents Bool) =
        ConnectedComponents.mk false := by
      simpa [tag, hf] using congrArg htag.connectedComponentsMap hpres
    have hmem := ConnectedComponents.coe_eq_coe'.mp htagEq
    simp at hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mapsTo_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mapsTo_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mapsTo_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mapsTo_child


def childCoreInclusionFun (c : ConnectedComponents Q.Carrier) : E.ChildCore c → E.ChildCarrier c :=
  fun x => Classical.choose (E.childCore_mapsTo_child c x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun

theorem childCoreInclusionFun_eq (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    E.trace.presentation (E.trace.capping.coreInclusion x.1) =
      Sum.inl (E.childCoreInclusionFun c x).1 :=
  (Classical.choose_spec (E.childCore_mapsTo_child c x)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusionFun_eq

theorem childCoreInclusion_continuous (c : ConnectedComponents Q.Carrier) :
    Continuous (E.childCoreInclusionFun c) := by
  obtain ⟨q, _⟩ := ConnectedComponents.surjective_coe c
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  apply continuous_induced_rng.2
  have h : Continuous (fun x : E.ChildCore c =>
      retraction (E.trace.presentation (E.trace.capping.coreInclusion x.1))) :=
    hret.comp (E.trace.presentation.continuous.comp
      (E.trace.capping.coreInclusion.continuous.comp continuous_subtype_val))
  apply h.congr
  intro x
  rw [E.childCoreInclusionFun_eq c x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_continuous


def childCoreInclusion (c : ConnectedComponents Q.Carrier) : C(E.ChildCore c, E.ChildCarrier c) :=
  ⟨E.childCoreInclusionFun c, E.childCoreInclusion_continuous c⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion


theorem childCore_mem_parent (c : ConnectedComponents Q.Carrier) (x : E.ChildCore c) :
    ConnectedComponents.mk (x.1.1 : P.Carrier) = E.childParent c := by
  change continuous_subtype_val.connectedComponentsMap (ConnectedComponents.mk x.1) =
    continuous_subtype_val.connectedComponentsMap (E.childCoreComponent c)
  exact congrArg continuous_subtype_val.connectedComponentsMap x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mem_parent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mem_parent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mem_parent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_mem_parent


def childCoreIntoParent (c : ConnectedComponents Q.Carrier) : C(E.ChildCore c, E.ParentCarrier c) :=
  ⟨fun x => ⟨x.1.1, E.childCore_mem_parent c x⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreIntoParent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreIntoParent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreIntoParent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreIntoParent


abbrev ChildCapBoundary (c : ConnectedComponents Q.Carrier) :=
  {b : E.trace.tubes.Boundary // ∀ y : Sphere 2,
    ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) = E.childCoreComponent c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCapBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ChildCapBoundary

theorem childCap_mapsTo_child (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (x : ThreeBall) :
    ∃! q : E.ChildCarrier c,
      E.trace.presentation (E.trace.capping.cap b.1 x) = Sum.inl q.1 := by
  classical
  let : ConnectedSpace ThreeBall := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  let y : Sphere 2 := ⟨EuclideanSpace.single 0 1, by
    simp [Sphere, PiLp.norm_single]⟩
  let z : E.ChildCore c :=
    ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩
  let q := E.childCoreInclusionFun c z
  have hboundary : E.trace.presentation (E.trace.capping.cap b.1 (sphereToThreeBall y)) =
      Sum.inl q.1 := by
    rw [E.trace.capping.boundary_eq]
    exact E.childCoreInclusionFun_eq c z
  have hball : ConnectedComponents.mk x = ConnectedComponents.mk (sphereToThreeBall y) :=
    Subsingleton.elim _ _
  have hpres : ConnectedComponents.mk (E.trace.presentation (E.trace.capping.cap b.1 x)) =
      ConnectedComponents.mk (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier) := by
    have h := congrArg
      (E.trace.presentation.continuous.comp (E.trace.capping.cap b.1).continuous).connectedComponentsMap
      hball
    exact h.trans (congrArg ConnectedComponents.mk hboundary)
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q.1)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  cases hf : E.trace.presentation (E.trace.capping.cap b.1 x) with
  | inl p =>
    have hp : ConnectedComponents.mk p = c := by
      have h := congrArg hret.connectedComponentsMap hpres
      simpa [retraction, hf, q.2] using h
    refine ⟨⟨p, hp⟩, rfl, ?_⟩
    intro w hw
    exact Subtype.ext (Sum.inl.inj hw.symm)
  | inr d =>
    let tag : Q.Carrier ⊕ D.Carrier → Bool := Sum.elim (fun _ => _root_.Bool.false) (fun _ => _root_.Bool.true)
    have htag : Continuous tag := continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩
    have htagEq : (ConnectedComponents.mk _root_.Bool.true : ConnectedComponents Bool) =
        ConnectedComponents.mk false := by
      simpa [tag, hf] using congrArg htag.connectedComponentsMap hpres
    have hmem := ConnectedComponents.coe_eq_coe'.mp htagEq
    simp at hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mapsTo_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mapsTo_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mapsTo_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_mapsTo_child


def childCapFun (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    ThreeBall → E.ChildCarrier c := fun x => Classical.choose (E.childCap_mapsTo_child c b x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun

theorem childCapFun_eq (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (x : ThreeBall) : E.trace.presentation (E.trace.capping.cap b.1 x) =
      Sum.inl (E.childCapFun c b x).1 :=
  (Classical.choose_spec (E.childCap_mapsTo_child c b x)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_eq

theorem childCapFun_continuous (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Continuous (E.childCapFun c b) := by
  obtain ⟨q, _⟩ := ConnectedComponents.surjective_coe c
  let retraction : Q.Carrier ⊕ D.Carrier → Q.Carrier := Sum.elim id (fun _ => q)
  have hret : Continuous retraction := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
  apply continuous_induced_rng.2
  have h : Continuous (fun x : ThreeBall => retraction
      (E.trace.presentation (E.trace.capping.cap b.1 x))) :=
    hret.comp (E.trace.presentation.continuous.comp (E.trace.capping.cap b.1).continuous)
  apply h.congr
  intro x
  rw [E.childCapFun_eq c b x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCapFun_continuous


def childCap (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    C(ThreeBall, E.ChildCarrier c) := ⟨E.childCapFun c b, E.childCapFun_continuous c b⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap

theorem childCap_isEmbedding (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    Topology.IsEmbedding (E.childCap c b) := by
  have hg : Topology.IsEmbedding (fun q : E.ChildCarrier c =>
      (Sum.inl q.1 : Q.Carrier ⊕ D.Carrier)) :=
    Topology.IsEmbedding.inl.comp Topology.IsEmbedding.subtypeVal
  apply hg.of_comp_iff.mp
  have hf : (fun x : ThreeBall => (Sum.inl (E.childCap c b x).1 : Q.Carrier ⊕ D.Carrier)) =
      E.trace.presentation ∘ E.trace.capping.cap b.1 := by
    funext x
    exact (E.childCapFun_eq c b x).symm
  change Topology.IsEmbedding (fun x : ThreeBall =>
    (Sum.inl (E.childCap c b x).1 : Q.Carrier ⊕ D.Carrier))
  rw [hf]
  exact E.trace.presentation.isEmbedding.comp (E.trace.capping.capEmbedding b.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_isEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_isEmbedding


theorem childCap_boundary_eq (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    (y : Sphere 2) : E.childCap c b (sphereToThreeBall y) =
      E.childCoreInclusion c
        ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩ := by
  apply Subtype.ext
  apply Sum.inl.inj (β := D.Carrier)
  change Sum.inl (E.childCapFun c b (sphereToThreeBall y)).1 = _
  rw [← E.childCapFun_eq c b (sphereToThreeBall y), E.trace.capping.boundary_eq]
  exact E.childCoreInclusionFun_eq c
    ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_boundary_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_boundary_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_boundary_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_boundary_eq

def childCarrierOpenCover (E : SmoothCutCapTransition P Q D N) : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
    ∃ (U V : Set (E.ChildCarrier c)) (x₀ : E.ChildCarrier c),
      IsOpen U ∧ IsOpen V ∧ U ∪ V = _root_.Set.univ ∧ x₀ ∈ U ∧ x₀ ∈ V ∧
      Set.range (E.childCoreInclusion c) ⊆ U ∧
      (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) ⊆ V ∧
      SimplyConnectedSpace U ∧ SimplyConnectedSpace V ∧
      PathConnectedSpace (↑(U ∩ V))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCarrierOpenCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCarrierOpenCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCarrierOpenCover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCarrierOpenCover

theorem child_simplyConnected_of_childCarrierOpenCover (E : SmoothCutCapTransition P Q D N)
    (h : E.childCarrierOpenCover) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier := by
  obtain ⟨U, V, x₀, hU, hV, hcov, hxU, hxV, _, _, hSU, hSV, hpc⟩ := h c inferInstance
  exact @DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_open_cover
    (E.ChildCarrier c) _ U V hU hV hcov x₀ ⟨hxU, hxV⟩ hSU hSV hpc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childCarrierOpenCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childCarrierOpenCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childCarrierOpenCover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_childCarrierOpenCover

theorem childCore_compactSpace (c : ConnectedComponents Q.Carrier) : CompactSpace (E.ChildCore c) := by
  let := E.core_compact
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  have hs : ({y : E.trace.tubes.core | ConnectedComponents.mk y = E.childCoreComponent c} : Set _) =
      connectedComponent x := by
    ext y
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'
  have hc : IsCompact ({y : E.trace.tubes.core |
      ConnectedComponents.mk y = E.childCoreComponent c} : Set _) := by
    rw [hs]
    exact isClosed_connectedComponent.isCompact
  exact isCompact_iff_compactSpace.mp hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_compactSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_compactSpace

theorem childCoreInclusion_injective (c : ConnectedComponents Q.Carrier) :
    Function.Injective (E.childCoreInclusion c) := by
  intro x y h
  have hval : (E.childCoreInclusionFun c x).1 = (E.childCoreInclusionFun c y).1 :=
    congrArg Subtype.val h
  have hpres : E.trace.presentation (E.trace.capping.coreInclusion x.1) =
      E.trace.presentation (E.trace.capping.coreInclusion y.1) := by
    rw [E.childCoreInclusionFun_eq c x, E.childCoreInclusionFun_eq c y, hval]
  exact Subtype.ext (E.trace.capping.coreEmbedding.injective (E.trace.presentation.injective hpres))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_injective

theorem childCoreInclusion_isEmbedding (c : ConnectedComponents Q.Carrier) :
    Topology.IsEmbedding (E.childCoreInclusion c) := by
  let : CompactSpace (E.ChildCore c) := E.childCore_compactSpace c
  exact (Continuous.isClosedEmbedding (E.childCoreInclusion c).continuous
    (E.childCoreInclusion_injective c)).isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_isEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreInclusion_isEmbedding

theorem childCore_range_isSimplyConnected (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (E.ChildCore c)] :
    IsSimplyConnected (Set.range (E.childCoreInclusion c)) :=
  ((E.childCoreInclusion_isEmbedding c).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_range_isSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_range_isSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_range_isSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_range_isSimplyConnected

theorem childCap_range_isSimplyConnected (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    IsSimplyConnected (Set.range (E.childCap c b)) :=
  ((E.childCap_isEmbedding c b).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_range_isSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_range_isSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_range_isSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCap_range_isSimplyConnected

theorem range_childCoreInclusion_union_range_childCap
    (c : ConnectedComponents Q.Carrier) :
    Set.range (E.childCoreInclusion c) ∪
      (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = univ := by
  classical
  have hball : ConnectedSpace ThreeBall :=
    isConnected_iff_connectedSpace.mp
      ((convex_closedBall (0 : ThreeSpace) 1).isConnected ⟨0, by simp⟩)
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe c
  refine Set.eq_univ_of_forall fun v => ?_
  have hv : E.trace.presentation.symm (Sum.inl v.1) ∈
      Set.range E.trace.capping.coreInclusion ∪
        ⋃ b, Set.range (E.trace.capping.cap b) := by
    rw [E.trace.capping.exhaustive]
    trivial
  have hcap0 : E.trace.cappedChild (ConnectedComponents.mk q) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl q)) := by
    rw [CutCapTopology.cappedChild]
    rfl
  have hcapv : ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl v.1)) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl q)) := by
    have h := congrArg (E.trace.presentation.symm.continuous.comp continuous_inl).connectedComponentsMap
      (v.2 : ConnectedComponents.mk v.1 = ConnectedComponents.mk q)
    simpa using h
  have hcap : E.trace.cappedChild (ConnectedComponents.mk q) =
      ConnectedComponents.mk (E.trace.presentation.symm (Sum.inl v.1)) :=
    hcap0.trans hcapv.symm
  have hcoreCompact : CompactSpace E.trace.tubes.core := E.core_compact
  have hcoreConnected : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  have hNt2 : T2Space N.Carrier := N.hausdorff
  have hcore : E.trace.capping.componentMap
      (E.childCoreComponent (ConnectedComponents.mk q)) =
      E.trace.cappedChild (ConnectedComponents.mk q) :=
    E.trace.capping.componentEquiv.apply_symm_apply _
  rcases hv with hv | hv
  · obtain ⟨x, hx⟩ := hv
    have hpres : E.trace.presentation (E.trace.capping.coreInclusion x) = Sum.inl v.1 := by
      rw [hx, Homeomorph.apply_symm_apply]
    have hcap2 : ConnectedComponents.mk (E.trace.capping.coreInclusion x) =
        E.trace.cappedChild (ConnectedComponents.mk q) := by
      rw [hcap, hx]
    have hchild : ConnectedComponents.mk x = E.childCoreComponent (ConnectedComponents.mk q) := by
      apply E.trace.capping.rfs_cap_component_bijection.injective
      rw [Capping.componentMap_mk, hcore]
      exact hcap2
    refine Or.inl ⟨⟨x, hchild⟩, ?_⟩
    apply Subtype.ext
    exact Sum.inl.inj ((E.childCoreInclusionFun_eq (ConnectedComponents.mk q)
      ⟨x, hchild⟩).symm.trans hpres)
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨z, hz⟩ := hb
    have hpres : E.trace.presentation (E.trace.capping.cap b z) = Sum.inl v.1 := by
      rw [hz, Homeomorph.apply_symm_apply]
    have hcap2 : ConnectedComponents.mk (E.trace.capping.cap b z) =
        E.trace.cappedChild (ConnectedComponents.mk q) := by
      rw [hcap, ← hz]
    have hpre : IsPreconnected (Set.range (E.trace.capping.cap b)) :=
      isPreconnected_range (E.trace.capping.cap b).continuous
    have hsame : ∀ y : Sphere 2,
        ConnectedComponents.mk (E.trace.capping.cap b (sphereToThreeBall y)) =
          ConnectedComponents.mk (E.trace.capping.cap b z) := fun y =>
      ConnectedComponents.coe_eq_coe'.mpr
        (hpre.subset_connectedComponent (Set.mem_range_self z)
          (Set.mem_range_self (sphereToThreeBall y)))
    have hbound : ∀ y : Sphere 2,
        ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) =
          E.childCoreComponent (ConnectedComponents.mk q) := by
      intro y
      have hpreB : IsPreconnected (Set.range (E.trace.tubes.coreBoundarySphere b)) := by
        have hsphere : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
          (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
            (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
        exact isPreconnected_range (E.trace.tubes.coreBoundarySphere b).continuous
      have hall : ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b y) =
          ConnectedComponents.mk (E.trace.tubes.coreBoundarySphere b
            (E.trace.capping.attaching b y)) :=
        ConnectedComponents.coe_eq_coe'.mpr
          (hpreB.subset_connectedComponent
            (Set.mem_range_self (E.trace.capping.attaching b y)) (Set.mem_range_self y))
      have hkey : ConnectedComponents.mk (E.trace.capping.coreInclusion
          (E.trace.tubes.coreBoundarySphere b (E.trace.capping.attaching b y))) =
          E.trace.cappedChild (ConnectedComponents.mk q) := by
        rw [← E.trace.capping.boundary_eq b y]
        exact (hsame y).trans hcap2
      rw [hall]
      apply E.trace.capping.rfs_cap_component_bijection.injective
      rw [Capping.componentMap_mk, hcore]
      exact hkey
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨b, hbound⟩, ?_⟩)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact Sum.inl.inj ((E.childCapFun_eq (ConnectedComponents.mk q) ⟨b, hbound⟩ z).symm.trans hpres)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_childCoreInclusion_union_range_childCap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_childCoreInclusion_union_range_childCap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_childCoreInclusion_union_range_childCap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.range_childCoreInclusion_union_range_childCap

theorem retainedBoundary_of_mem_childCapBoundary
    (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    ∀ y : Sphere 2, E.trace.tubes.coreBoundarySphere b.1 y ∈ E.trace.retainedCore := by
  have hcoreCompact : CompactSpace E.trace.tubes.core := E.core_compact
  have hcoreConnected : LocallyConnectedSpace E.trace.tubes.core := E.core_locallyConnected
  have hNt2 : T2Space N.Carrier := N.hausdorff
  intro y
  exact CutCapTopology.childCore_subset_retainedCore E.trace c (b.2 y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedBoundary_of_mem_childCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedBoundary_of_mem_childCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedBoundary_of_mem_childCapBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.retainedBoundary_of_mem_childCapBoundary
end SmoothCutCapTransition

namespace SmoothCutCapTransition

theorem childParent_congr {P Q D N P' Q' D' N' : OrientedThreeStage.{u}}
    (E : SmoothCutCapTransition P Q D N) (F : SmoothCutCapTransition P' Q' D' N')
    (hp : P = P') (hq : Q = Q') (hd : D = D') (hn : N = N') (hEF : HEq E F)
    (c : ConnectedComponents Q.Carrier) :
    (hp ▸ E.childParent c) = F.childParent (hq ▸ c) := by
  cases hp
  cases hq
  cases hd
  cases hn
  cases eq_of_heq hEF
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childParent_congr

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
