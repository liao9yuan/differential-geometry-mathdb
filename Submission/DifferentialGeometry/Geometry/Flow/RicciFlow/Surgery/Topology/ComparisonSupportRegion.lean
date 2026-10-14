import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SupportRegionNeck
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalRegion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

namespace SmoothBoundaryAtlas

variable {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {K : Set M}

theorem isSmoothEmbedding_subtypeVal
    (C : SmoothBoundaryAtlas (𝓡 n) n K) [IsManifold (𝓡 n) ∞ M] :
    letI := C.toChartedSpace
    letI := C.isManifold
    IsSmoothEmbedding (𝓡∂ n) (𝓡 n) ∞ (Subtype.val : K → M) := by
  let := C.toChartedSpace
  let := C.isManifold
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨PUnit, inferInstance, inferInstance, fun x => ?_⟩
  apply IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) PUnit)
    (C.chart x) (C.ambientChart x).toOpenPartialHomeomorph
    (C.mem_source x) (C.mem_source x)
    (IsManifold.chart_mem_maximalAtlas x)
    ((C.ambientChart x).toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      (C.ambientChart x).contMDiffOn_toFun (C.ambientChart x).contMDiffOn_invFun)
    (fun y hy => by
      rw [SmoothBoundaryAtlas.chart, OpenPartialHomeomorph.restrictSubtypes_source] at hy
      exact hy)
  intro z hz
  rw [OpenPartialHomeomorph.extend_target'] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwt : ((𝓡∂ n) w) ∈ (C.ambientChart x).target := by
    rw [SmoothBoundaryAtlas.chart, OpenPartialHomeomorph.restrictSubtypes_target] at hw
    exact hw
  have hst : ((𝓡∂ n) w) ∈
      (C.ambientChart x).toOpenPartialHomeomorph.target := hwt
  have hsymm : (Subtype.val ((C.chart x).symm w) : M) =
      (C.ambientChart x).symm ((𝓡∂ n) w) := by
    rw [SmoothBoundaryAtlas.chart]
    exact OpenPartialHomeomorph.restrictSubtypes_symm_apply _ _ _ _ _ _ _ hst
  have hleft : (𝓡∂ n).symm ((𝓡∂ n) w) = w := (𝓡∂ n).left_inv w
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, hleft, hsymm,
    ContinuousLinearEquiv.prodUnique_apply, modelWithCornersSelf_coe, id_eq]
  exact (C.ambientChart x).toOpenPartialHomeomorph.right_inv hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isSmoothEmbedding_subtypeVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.isSmoothEmbedding_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isSmoothEmbedding_subtypeVal ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.isSmoothEmbedding_subtypeVal

end SmoothBoundaryAtlas

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem mem_neckBuffer_comparisonLevel (b : G.ChildBoundary c) (y : Sphere 2) :
    (y, G.comparisonLevel c b) ∈ neckBuffer (G.static b.1).delta :=
  ⟨by linarith [G.comparisonLevel_lower c b, inv_pos.mpr (G.static b.1).neck.delta_pos],
   by linarith [G.comparisonLevel_negative c b, inv_pos.mpr (G.static b.1).neck.delta_pos]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_neckBuffer_comparisonLevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_neckBuffer_comparisonLevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_neckBuffer_comparisonLevel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_neckBuffer_comparisonLevel

theorem levelSphere_eq_staticNeckPoint (b : G.ChildBoundary c) (y : Sphere 2) :
    levelSphere G c b y = G.staticNeckPoint c b
      ⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ := by
  have harg : (G.collarParameter c b
      (y, ⟨G.comparisonLevel c b, le_rfl, (G.comparisonLevel_negative c b).le⟩)).1 =
      (⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ :
        neckBuffer (G.static b.1).delta) := by
    apply Subtype.ext
    rw [G.collarParameter_apply c b]
  apply Subtype.ext
  rw [levelSphere_apply, G.collarMap_apply]
  exact congrArg (fun w : neckBuffer (G.static b.1).delta =>
    ((G.static b.1).neck.chart w).1) harg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSphere_eq_staticNeckPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSphere_eq_staticNeckPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSphere_eq_staticNeckPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSphere_eq_staticNeckPoint

theorem staticNeckPoint_range_disjoint (b d : G.ChildBoundary c) (h : b ≠ d) :
    Disjoint (Set.range (G.staticNeckPoint c b)) (Set.range (G.staticNeckPoint c d)) := by
  have hidx : b.1.1.1 ≠ d.1.1.1 := by
    intro hidx
    have hbret : (H.event i).RetainedBoundary b.1.1 :=
      G.transition.retainedBoundary_of_mem_childCapBoundary c ⟨b.1.1, b.2⟩
    have hdret : (H.event i).RetainedBoundary d.1.1 :=
      G.transition.retainedBoundary_of_mem_childCapBoundary c ⟨d.1.1, d.2⟩
    have hside : b.1.1.2 = d.1.1.2 :=
      G.retainedBoundary_side_eq (α := d.1.1.1) (hidx ▸ hbret) hdret
    exact h (Subtype.ext (Subtype.ext (Prod.ext hidx hside)))
  refine Set.disjoint_left.mpr fun y hy hz => ?_
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨w, hw⟩ := hz
  have hstage : ((G.static b.1).neck.chart z).1 = ((G.static d.1).neck.chart w).1 :=
    congrArg (fun p : (G.Parent c).Carrier => (p.1 : (H.stage i.castSucc).Carrier)) hw.symm
  have heq : ((G.neck b.1.1.1).chart
      ⟨(z.1.1, (if b.1.1.2 then (1 : ℝ) else -1) * (1 + z.1.2)),
        G.recenter_in_buffer b.1 z⟩).1 =
      ((G.neck d.1.1.1).chart
      ⟨(w.1.1, (if d.1.1.2 then (1 : ℝ) else -1) * (1 + w.1.2)),
        G.recenter_in_buffer d.1 w⟩).1 := by
    rw [← G.staticNeckChart_eq_neckChart b.1 z, hstage,
      G.staticNeckChart_eq_neckChart d.1 w]
  exact Set.disjoint_left.mp (G.buffer_disjoint hidx)
    (Set.mem_range_self _) ⟨_, Subtype.ext heq.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.staticNeckPoint_range_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.staticNeckPoint_range_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.staticNeckPoint_range_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.staticNeckPoint_range_disjoint

theorem exists_smoothBoundaryAtlas_levelSphere_iff :
    ∃ C : DifferentialGeometry.Topology.SmoothBoundaryAtlas ThreeModel 3
        (supportRegion G c),
      ∀ x : (supportRegion G c),
        C.ambientChart x x.val 0 = 0 ↔
          ∃ b : G.ChildBoundary c, x.val ∈ Set.range (levelSphere G c b) := by
  classical
  have hchart : ∀ x : (supportRegion G c),
      ∃ φ : PartialDiffeomorph ThreeModel ThreeModel (G.Parent c).Carrier
          (EuclideanSpace ℝ (Fin 3)) ∞,
        x.val ∈ φ.source ∧
        (φ x.val 0 = 0 ↔ ∃ b : G.ChildBoundary c, x.val ∈ Set.range (levelSphere G c b)) ∧
        ∀ y ∈ φ.source, (y ∈ supportRegion G c ↔ 0 ≤ φ y 0) := by
    intro x
    by_cases hx : ∃ b : G.ChildBoundary c, x.val ∈ Set.range (G.staticNeckPoint c b)
    · obtain ⟨b, z₀, hz₀⟩ := hx
      obtain ⟨φ, hφ, hcoord, hmem⟩ := G.exists_ambientChart_staticNeckImage c b z₀
      have hsrc : x.val ∈ φ.source := hz₀ ▸ hφ
      refine ⟨φ, hsrc, ?_, hmem⟩
      rw [← hz₀, hcoord]
      constructor
      · intro h0
        have hz2 : z₀.1.2 = G.comparisonLevel c b := by linarith
        have hz02 : z₀ = (⟨(z₀.1.1, G.comparisonLevel c b), by
            refine ⟨?_, ?_⟩ <;>
              linarith [G.comparisonLevel_lower c b, G.comparisonLevel_negative c b,
                inv_pos.mpr (G.static b.1).neck.delta_pos]⟩ :
            neckBuffer (G.static b.1).delta) := by
          apply Subtype.ext
          exact Prod.ext rfl hz2
        refine ⟨b, z₀.1.1, ?_⟩
        rw [G.levelSphere_eq_staticNeckPoint c b z₀.1.1]
        exact congrArg (G.staticNeckPoint c b) hz02.symm
      · rintro ⟨b', y, hy⟩
        rcases eq_or_ne b b' with hbb | hne
        · rw [← hbb] at hy
          rw [G.levelSphere_eq_staticNeckPoint c b y] at hy
          have hzy := (G.staticNeckPoint_isSmoothEmbedding c b).isEmbedding.injective hy
          have h2 : (⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ :
              neckBuffer (G.static b.1).delta).1.2 = z₀.1.2 :=
            congrArg (fun q : neckBuffer (G.static b.1).delta => q.1.2) hzy
          linarith
        · rw [G.levelSphere_eq_staticNeckPoint c b' y] at hy
          let q : neckBuffer (G.static b'.1).delta :=
            ⟨(y, G.comparisonLevel c b'), G.mem_neckBuffer_comparisonLevel c b' y⟩
          have hy' : G.staticNeckPoint c b' q = G.staticNeckPoint c b z₀ :=
            (congrArg (G.staticNeckPoint c b') (Subtype.ext rfl)).symm.trans hy
          exact absurd ⟨z₀, hy'.symm⟩ (Set.disjoint_left.mp
            (G.staticNeckPoint_range_disjoint c b' b (Ne.symm hne))
            (Set.mem_range_self q))
    · have hcore : x.val ∈ Set.range (G.transition.childCoreIntoParent c) :=
        G.mem_childCore_range_of_notMem_staticNeckImage c x.val x.2 (by
          intro b hb
          exact hx ⟨b, hb⟩)
      obtain ⟨x', hx'⟩ := hcore
      obtain ⟨V, hVopen, hx'V, hVsub⟩ :=
        G.exists_isOpen_subset_supportRegion_of_childCore_notMem_staticNeckImage c x' (by
          intro b hb
          exact hx ⟨b, hx' ▸ hb⟩)
      obtain ⟨φ, hxin, hsub, hpos⟩ :=
        DifferentialGeometry.Topology.exists_positiveChart_of_mem_open (n := 3) hVopen
          (hx' ▸ hx'V)
      refine ⟨φ, hxin, ?_, ?_⟩
      · constructor
        · intro h0
          exact absurd h0 (ne_of_gt (hpos x.val hxin))
        · rintro ⟨b', hb'⟩
          obtain ⟨y, hy⟩ := hb'
          let q : neckBuffer (G.static b'.1).delta :=
            ⟨(y, G.comparisonLevel c b'), G.mem_neckBuffer_comparisonLevel c b' y⟩
          exact absurd ⟨b', ⟨q, (congrArg (G.staticNeckPoint c b') (Subtype.ext rfl)).trans
            ((G.levelSphere_eq_staticNeckPoint c b' y).symm.trans hy)⟩⟩ hx
      · intro y hy
        exact iff_of_true (hVsub (hsub hy)) (hpos y hy).le
  choose φ hφsrc hφbdry hφiff using hchart
  exact ⟨{ ambientChart := φ, mem_source := hφsrc, mem_iff := hφiff }, hφbdry⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothBoundaryAtlas_levelSphere_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothBoundaryAtlas_levelSphere_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothBoundaryAtlas_levelSphere_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothBoundaryAtlas_levelSphere_iff

noncomputable def translateChart (t : ℝ) : OpenPartialHomeomorph ℝ ℝ :=
  PartialDiffeomorph.toOpenPartialHomeomorph
    (DifferentialGeometry.Topology.translateDiffeomorph t).toPartialDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart

@[simp]
theorem translateChart_apply (t r : ℝ) : translateChart t r = r + t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_apply

theorem translateChart_mem_maximalAtlas (t : ℝ) :
    translateChart t ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℝ)) ∞ ℝ := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contDiff_id.add contDiff_const).contMDiff.contMDiffOn
  · exact (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_mem_maximalAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_mem_maximalAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_mem_maximalAtlas ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.translateChart_mem_maximalAtlas

theorem levelSlice_isSmoothEmbedding (b : G.ChildBoundary c) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞
      (fun y : Sphere 2 => ((y, G.comparisonLevel c b) : NeckCylinder)) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) (Sphere 2 × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 2)) (Sphere 2) ℝ ℝ
  refine ⟨?_, isEmbedding_prodMkLeft (G.comparisonLevel c b)⟩
  refine ⟨ℝ, inferInstance, inferInstance, fun y => ?_⟩
  apply IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
    (chartAt (EuclideanSpace ℝ (Fin 2)) y)
    ((chartAt (EuclideanSpace ℝ (Fin 2)) y).prod
      (translateChart (-(G.comparisonLevel c b))))
    (mem_chart_source _ y)
    ⟨mem_chart_source _ y, _root_.Set.mem_univ _⟩
    (IsManifold.chart_mem_maximalAtlas y)
    (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas y)
      (translateChart_mem_maximalAtlas (-(G.comparisonLevel c b))))
    (fun z hz => by refine ⟨by simpa using hz, _root_.Set.mem_univ _⟩)
  intro z hz
  rw [Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.extend_prod]
  rw [PartialEquiv.prod_coe]
  simp only [Function.comp_apply, ContinuousLinearEquiv.refl_apply]
  rw [((chartAt (EuclideanSpace ℝ (Fin 2)) y).extend (𝓡 2)).right_inv hz]
  refine Prod.ext rfl ?_
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    modelWithCornersSelf_coe, id_eq]
  change translateChart (-(G.comparisonLevel c b)) (G.comparisonLevel c b) = 0
  rw [translateChart_apply]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_isSmoothEmbedding

theorem levelSlice_neckBuffer_isSmoothEmbedding (b : G.ChildBoundary c) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) NeckCylinderModel ∞
      (fun y : Sphere 2 => (⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ :
        ↥(neckBuffer (G.static b.1).delta))) :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    (𝓡 2) (NeckCylinderModel) (neckBuffer (G.static b.1).delta) _
    (G.levelSlice_isSmoothEmbedding c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_neckBuffer_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_neckBuffer_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_neckBuffer_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.levelSlice_neckBuffer_isSmoothEmbedding

theorem sphereFun_isSmoothEmbedding (b : G.ChildBoundary c) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (fun y : Sphere 2 => (sphereFun G c b y).1) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcomp : _root_.Manifold.IsSmoothEmbedding (𝓡 2) ThreeModel ∞
      (G.staticNeckPoint c b ∘
        fun y : Sphere 2 => (⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ :
          ↥(neckBuffer (G.static b.1).delta))) :=
    IsSmoothEmbedding.comp (G.staticNeckPoint_isSmoothEmbedding c b)
      (G.levelSlice_neckBuffer_isSmoothEmbedding c b) hn
  have heq : (fun y : Sphere 2 => (sphereFun G c b y).1) =
      (G.staticNeckPoint c b ∘
        fun y : Sphere 2 => (⟨(y, G.comparisonLevel c b), G.mem_neckBuffer_comparisonLevel c b y⟩ :
          ↥(neckBuffer (G.static b.1).delta))) := by
    funext y
    rw [Function.comp_apply, sphereFun_apply, G.levelSphere_eq_staticNeckPoint c b y]
  simpa only [heq] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.sphereFun_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.sphereFun_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.sphereFun_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.sphereFun_isSmoothEmbedding

theorem mem_range_sphereFun_iff (b : G.ChildBoundary c) (x : supportRegion G c) :
    x ∈ Set.range (sphereFun G c b) ↔ x.val ∈ Set.range (levelSphere G c b) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_range_sphereFun_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_range_sphereFun_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_range_sphereFun_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.mem_range_sphereFun_iff

theorem exists_smoothSphericalRegion_supportRegion :
    ∃ (S : SmoothSphericalRegion (G.Parent c)) (hlabel : G.ChildBoundary c ≃ S.Boundary),
      S.region = supportRegion G c ∧
      (∀ b : G.ChildBoundary c,
        (Subtype.val : S.region → (G.Parent c).Carrier) '' Set.range (S.sphere (hlabel b)) =
          Set.range fun y : Sphere 2 => G.collarMap c b (y,
            ⟨G.comparisonLevel c b, le_rfl, (G.comparisonLevel_negative c b).le⟩)) := by
  obtain ⟨C, hC⟩ := G.exists_smoothBoundaryAtlas_levelSphere_iff c
  let : ChartedSpace (EuclideanHalfSpace 3) (supportRegion G c) := C.toChartedSpace
  let : IsManifold (𝓡∂ 3) ∞ (supportRegion G c) := C.isManifold
  refine ⟨{ region := supportRegion G c
            compact := isCompact_supportRegion G c
            connected := isConnected_supportRegion G c
            charts := C.toChartedSpace
            smooth := C.isManifold
            induced :=
              DifferentialGeometry.Topology.SmoothBoundaryAtlas.isSmoothEmbedding_subtypeVal C
            interior_connected := isConnected_interiorImage_supportRegion G c C
            Boundary := G.ChildBoundary c
            finiteBoundary := Fintype.ofFinite (G.ChildBoundary c)
            sphere := sphereFun G c
            sphere_smooth := fun b => G.sphereFun_isSmoothEmbedding c b
            sphere_disjoint := G.sphereFun_pairwise_disjoint c
            boundary_eq := ?_ }, Equiv.refl (G.ChildBoundary c), rfl, ?_⟩
  · ext x
    rw [Set.mem_iUnion, ModelWithCorners.boundary, Set.mem_ofPred_eq]
    exact (G.isBoundaryPoint_iff_exists_levelSphere c C hC x).trans
      (exists_congr fun b => (G.mem_range_sphereFun_iff c b x).symm)
  · intro b
    rw [← Set.range_comp]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothSphericalRegion_supportRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothSphericalRegion_supportRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothSphericalRegion_supportRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.exists_smoothSphericalRegion_supportRegion

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
