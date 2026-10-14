import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonSupportRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonDefs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExteriorRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore
import Submission.DifferentialGeometry.Topology.Manifold.InteriorImage
import Submission.DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.SphereSeparation.SideClosureDisjoint
import Submission.DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

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

theorem sphereTwo_connectedSpace : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwo_connectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwo_connectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwo_connectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereTwo_connectedSpace

theorem riemannianCurveLength_eq_zero_of_apply_eq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {a b : ℝ} {q : M}
    (h : ∀ t ∈ _root_.Set.Icc a b, γ t = q) : riemannianCurveLength g γ a b = 0 := by
  exact DifferentialGeometry.Geometry.riemannianCurveVariation_eq_zero_of_apply_eq_const g γ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_zero_of_apply_eq_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_zero_of_apply_eq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_zero_of_apply_eq_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_zero_of_apply_eq_const

theorem rfs_exterior_branches (P : OrientedThreeStage.{u}) [ConnectedSpace P.Carrier]
    [SimplyConnectedSpace P.Carrier] (C : SmoothSphericalRegion P) :
    Nonempty (ExteriorRegions C) :=
  exists_exteriorRegions P C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_exterior_branches then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_exterior_branches"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_exterior_branches ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_exterior_branches

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

theorem capPoint_mem_child (b : G.ChildBoundary c) (t : ThreeBall) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.cap t) :
      (H.stage i.succ).Carrier) = c := by
  obtain ⟨q, hq, -⟩ := G.transition.childCap_mapsTo_child c ⟨b.1.1, b.2⟩ t
  have hcap := (G.static b.1).cap_eq t
  rw [hcap] at hq
  have hinj : (G.static b.1).inclusion ((G.static b.1).witness.cap t) = q.1 := Sum.inl.inj hq
  rw [hinj]
  exact q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capPoint_mem_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capPoint_mem_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capPoint_mem_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capPoint_mem_child

theorem tipPoint_mem_child (b : G.ChildBoundary c) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.tip) :
      (H.stage i.succ).Carrier) = c := by
  obtain ⟨t, -, ht⟩ := (G.static b.1).witness.tip_interior
  rw [← ht]
  exact G.capPoint_mem_child c b t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_mem_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_mem_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_mem_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_mem_child

abbrev spherePoint : Sphere 2 := DifferentialGeometry.Topology.sphereTwoNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint

theorem spherePoint_norm (y : Sphere 2) : ‖(y : ThreeSpace)‖ = 1 := by
  have h : _root_.Dist.dist (y : ThreeSpace) 0 = 1 := Metric.mem_sphere.mp y.2
  rwa [dist_eq_norm, sub_zero] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.spherePoint_norm

theorem capCentralDomain_preconnectedSpace (b : G.ChildBoundary c) :
    PreconnectedSpace ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralDomain_preconnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralDomain_preconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralDomain_preconnectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralDomain_preconnectedSpace

def capCentralElement (b : G.ChildBoundary c) :
    Sphere 2 × ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) →
      neckCentralDomain (G.static b.1).delta :=
  fun p => ⟨⟨(p.1, p.2.1), by
      obtain ⟨h1, h2⟩ := p.2.2
      exact ⟨by linarith, by linarith⟩⟩, p.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement

theorem capCentralElement_continuous (b : G.ChildBoundary c) :
    Continuous (G.capCentralElement c b) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralElement_continuous

theorem tipCoordinate_negative (b : G.ChildBoundary c) :
    (G.static b.1).witness.tipCoordinate < 0 := by
  have h2 := (G.static b.1).witness.tipCoordinate_upper
  have h3 := parameters.fixed.collar_pos
  have h4 : 0 < standardCapL := standardCapL_pos
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipCoordinate_negative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipCoordinate_negative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipCoordinate_negative ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipCoordinate_negative

theorem radialZero_mem_closedCore (b : G.ChildBoundary c) (y : Sphere 2) :
    (G.static b.1).witness.radial 0 • (y : ThreeSpace) ∈ standardCapClosedCore := by
  have htip := G.tipCoordinate_negative c b
  have h0mem : (0 : ℝ) ∈ _root_.Set.Icc (G.static b.1).witness.tipCoordinate 0 := ⟨htip.le, le_rfl⟩
  obtain ⟨hnn, hle⟩ := (G.static b.1).witness.radial_range h0mem
  rw [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right, norm_smul, spherePoint_norm y,
    mul_one, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.radialZero_mem_closedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.radialZero_mem_closedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.radialZero_mem_closedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.radialZero_mem_closedCore

def capCentralZero (b : G.ChildBoundary c) :
    ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  ⟨0, ⟨neg_lt_zero.mpr (inv_pos.mpr (G.static b.1).neck.delta_pos),
    inv_pos.mpr (G.static b.1).neck.delta_pos⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralZero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralZero

def capCentralBase (b : G.ChildBoundary c) (y : Sphere 2) :
    Sphere 2 × ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
  (y, G.capCentralZero c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralBase ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCentralBase

def capCollapseMap (b : G.ChildBoundary c) :
    Sphere 2 × ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) →
      (H.stage i.succ).Carrier :=
  fun p => (G.static b.1).inclusion ((G.static b.1).witness.collapse (G.capCentralElement c b p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap

theorem capCollapseMap_continuous (b : G.ChildBoundary c) :
    Continuous (G.capCollapseMap c b) :=
  (G.static b.1).inclusion.continuous.comp
    ((G.static b.1).witness.collapse.continuous.comp (G.capCentralElement_continuous c b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_continuous

theorem capCollapse_zero_eq (b : G.ChildBoundary c) (y : Sphere 2) :
    (G.static b.1).witness.collapse (G.capCentralElement c b (G.capCentralBase c b y)) =
      (G.static b.1).witness.capChart
        ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
          G.radialZero_mem_closedCore c b y⟩ :=
  (G.static b.1).witness.collapse_radial _ (G.tipCoordinate_negative c b) le_rfl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapse_zero_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapse_zero_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapse_zero_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapse_zero_eq

theorem capCollapseMap_base_eq_capChart (b : G.ChildBoundary c) (y : Sphere 2) :
    G.capCollapseMap c b (G.capCentralBase c b y) =
      (G.static b.1).inclusion ((G.static b.1).witness.capChart
        ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
          G.radialZero_mem_closedCore c b y⟩) :=
  congrArg (G.static b.1).inclusion (G.capCollapse_zero_eq c b y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_eq_capChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_eq_capChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_eq_capChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_eq_capChart

theorem capCollapseMap_base_mem_child (b : G.ChildBoundary c) (y : Sphere 2) :
    ConnectedComponents.mk (G.capCollapseMap c b (G.capCentralBase c b y)) = c := by
  rw [G.capCollapseMap_base_eq_capChart c b y]
  have hmem : (G.static b.1).witness.capChart
      ⟨(G.static b.1).witness.radial 0 • (y : ThreeSpace),
        G.radialZero_mem_closedCore c b y⟩ ∈ Set.range (G.static b.1).witness.cap := by
    rw [← (G.static b.1).witness.capChart_range]
    exact Set.mem_range_self _
  obtain ⟨t, ht⟩ := hmem
  rw [← ht]
  exact G.capPoint_mem_child c b t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_mem_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_mem_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_mem_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_base_mem_child

theorem connectedComponents_mk_eq_of_mem_preconnected {α : Type*} [TopologicalSpace α] {s : Set α}
    (h : IsPreconnected s) {p q : α} (hp : p ∈ s) (hq : q ∈ s) :
    ConnectedComponents.mk p = ConnectedComponents.mk q :=
  ConnectedComponents.coe_eq_coe'.mpr ((h.subset_connectedComponent hq) hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.connectedComponents_mk_eq_of_mem_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.connectedComponents_mk_eq_of_mem_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.connectedComponents_mk_eq_of_mem_preconnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.connectedComponents_mk_eq_of_mem_preconnected

theorem capCollapseMap_preconnected (b : G.ChildBoundary c) :
    IsPreconnected (Set.range (G.capCollapseMap c b)) := by
  have : PreconnectedSpace (Sphere 2) := sphereTwo_connectedSpace.toPreconnectedSpace
  have : PreconnectedSpace ↑(_root_.Set.Ioo (-(G.static b.1).delta⁻¹) (G.static b.1).delta⁻¹) :=
    G.capCentralDomain_preconnectedSpace c b
  exact isPreconnected_range (G.capCollapseMap_continuous c b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_preconnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.capCollapseMap_preconnected

theorem collapsePoint_mem_child (b : G.ChildBoundary c)
    (x : neckCentralDomain (G.static b.1).delta) :
    ConnectedComponents.mk ((G.static b.1).inclusion ((G.static b.1).witness.collapse x) :
      (H.stage i.succ).Carrier) = c := by
  have hxmem : (G.static b.1).inclusion ((G.static b.1).witness.collapse x) ∈
      Set.range (G.capCollapseMap c b) := by
    refine ⟨(x.1.1.1, ⟨x.1.1.2, x.2.1, x.2.2⟩), ?_⟩
    have hxeq : G.capCentralElement c b (x.1.1.1, ⟨x.1.1.2, x.2.1, x.2.2⟩) = x :=
      Subtype.ext (Subtype.ext rfl)
    rw [capCollapseMap, hxeq]
  exact (connectedComponents_mk_eq_of_mem_preconnected (G.capCollapseMap_preconnected c b)
    hxmem (Set.mem_range_self (spherePoint, G.capCentralZero c b))).trans
    (G.capCollapseMap_base_mem_child c b spherePoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collapsePoint_mem_child then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collapsePoint_mem_child"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collapsePoint_mem_child ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collapsePoint_mem_child

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (c : ConnectedComponents (H.stage i.succ).Carrier)

def localCollapseMap (b : G.ChildBoundary c) :
    C(neckCentralDomain (G.static b.1).delta, (G.Child c).Carrier) :=
  ⟨fun x => ⟨(G.static b.1).inclusion ((G.static b.1).witness.collapse x),
      G.collapsePoint_mem_child c b x⟩,
    Continuous.subtype_mk
      ((G.static b.1).inclusion.continuous.comp (G.static b.1).witness.collapse.continuous)
      (fun x => G.collapsePoint_mem_child c b x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap

theorem localCollapseMap_apply (b : G.ChildBoundary c) (x : neckCentralDomain (G.static b.1).delta) :
    (G.localCollapseMap c b x).1 =
      (G.static b.1).inclusion ((G.static b.1).witness.collapse x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.localCollapseMap_apply

def tipPoint (b : G.ChildBoundary c) : (G.Child c).Carrier :=
  ⟨(G.static b.1).inclusion ((G.static b.1).witness.tip), G.tipPoint_mem_child c b⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint

theorem tipPoint_apply (b : G.ChildBoundary c) :
    (G.tipPoint c b).1 = (G.static b.1).inclusion ((G.static b.1).witness.tip) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.tipPoint_apply

theorem collarMap_inter_childCore_range_of_subset_ne_zero
    (hsubset : ∀ (b : G.ChildBoundary c) (y : Sphere 2)
      (t : ↑(_root_.Set.Icc (G.comparisonLevel c b) 0)),
      G.collarMap c b (y, t) ∈ Set.range (G.transition.childCoreIntoParent c) → (t : ℝ) = 0)
    (b : G.ChildBoundary c) :
    Set.range (G.collarMap c b) ∩ Set.range (G.transition.childCoreIntoParent c) =
      Set.range (fun y : Sphere 2 =>
        G.collarMap c b (y, ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩)) := by
  ext p
  constructor
  · rintro ⟨hp, hcore⟩
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, t⟩ := x
    have ht : (t : ℝ) = 0 := hsubset b y t hcore
    have ht' : t = ⟨0, (G.comparisonLevel_negative c b).le, le_rfl⟩ := Subtype.ext ht
    refine ⟨y, ?_⟩
    rw [ht']
  · rintro ⟨y, rfl⟩
    exact ⟨Set.mem_range_self _, G.collarMap_zero_mem_childCore_range c b y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collarMap_inter_childCore_range_of_subset_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collarMap_inter_childCore_range_of_subset_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collarMap_inter_childCore_range_of_subset_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.collarMap_inter_childCore_range_of_subset_ne_zero

theorem support_terminal_of_region (S : SmoothSphericalRegion (G.Parent c))
    (hregion : S.region = Set.range (G.transition.childCoreIntoParent c) ∪
      ⋃ b, Set.range (G.collarMap c b)) :
    ∀ x ∈ S.region, x.1 ∈ (H.event i).incoming.terminalRegularRegion := by
  intro x hx
  rw [hregion] at hx
  rcases hx with hx | hx
  · obtain ⟨y, rfl⟩ := hx
    exact G.childCoreIntoParent_terminal c y
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    obtain ⟨w, rfl⟩ := hb
    exact G.collarMap_terminal c b w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.support_terminal_of_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.support_terminal_of_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.support_terminal_of_region ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.support_terminal_of_region

theorem rfs_comparison_support_of_region_data
    [SimplyConnectedSpace (G.Parent c).Carrier]
    (S : SmoothSphericalRegion (G.Parent c))
    (hregion : S.region = Set.range (G.transition.childCoreIntoParent c) ∪
      ⋃ b, Set.range (G.collarMap c b))
    (hlabel : G.ChildBoundary c ≃ S.Boundary)
    (hboundary : ∀ b : G.ChildBoundary c,
      (Subtype.val : S.region → (G.Parent c).Carrier) '' Set.range (S.sphere (hlabel b)) =
        Set.range (fun y : Sphere 2 => G.collarMap c b
          (y, ⟨G.comparisonLevel c b, le_rfl, (G.comparisonLevel_negative c b).le⟩))) :
    Nonempty (G.ComparisonSupport c) :=
  ⟨{ level := G.comparisonLevel c
     level_lower := G.comparisonLevel_lower c
     level_below_tip := G.comparisonLevel_below_tip c
     level_negative := G.comparisonLevel_negative c
     collarParameter := G.collarParameter c
     collarParameter_eq := G.collarParameter_apply c
     collar := G.collarMap c
     collar_eq := G.collarMap_apply c
     collar_core_intersection := G.collarMap_inter_childCore_range_of_subset_ne_zero c (by
       intro b y t ht
       by_contra hne
       obtain ⟨z, hz⟩ := ht
       have hzval : (z.1.1 : (H.stage i.castSucc).Carrier) =
           ((G.static b.1).neck.chart (G.collarParameter c b (y, t)).1).1 := by
         have h1 : (G.transition.childCoreIntoParent c z).1 = (G.collarMap c b (y, t)).1 :=
           congrArg Subtype.val hz
         exact h1.trans (G.collarMap_apply c b (y, t))
       have hneg : (G.collarParameter c b (y, t)).1.1.2 < 0 := by
         rw [G.collarParameter_apply c b (y, t)]
         exact lt_of_le_of_ne t.2.2 hne
       exact G.staticNeckChart_ne_childCore_of_coordinate_negative b.1 c b.2
         (G.collarParameter c b (y, t)).1 hneg z hzval.symm)
     collar_disjoint := G.collarMap_pairwise_disjoint c
     support := S
     support_eq := hregion
     support_terminal := G.support_terminal_of_region c S hregion
     boundaryLabel := hlabel
     boundary_eq := hboundary
     exterior := Classical.choice (rfs_exterior_branches (G.Parent c) S)
     localCollapse := G.localCollapseMap c
     localCollapse_eq := fun _ _ => rfl
     tip := G.tipPoint c
     tip_eq := fun _ => rfl }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support_of_region_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support_of_region_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support_of_region_data ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support_of_region_data

theorem rfs_comparison_support
    [SimplyConnectedSpace (G.Parent c).Carrier] : Nonempty (G.ComparisonSupport c) := by
  obtain ⟨S, hlabel, hregion, hboundary⟩ := G.exists_smoothSphericalRegion_supportRegion c
  exact rfs_comparison_support_of_region_data G c S hregion hlabel hboundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_comparison_support

namespace ComparisonSupport

variable {G c} (K : G.ComparisonSupport c)


def IsWholeParentMap (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  (∀ x : G.transition.ChildCore c,
    f (G.transition.childCoreIntoParent c x) = G.transition.childCoreInclusion c x) ∧
  (∀ b x, f (K.collar b x) = K.localCollapse b (K.collarParameter b x)) ∧
  (∀ b x, x ∈ (K.exterior.exterior (K.boundaryLabel b)).region → f x = K.tip b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.IsWholeParentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.IsWholeParentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.IsWholeParentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.IsWholeParentMap

def childCoreIntoParentFun : G.transition.ChildCore c → (G.Parent c).Carrier :=
  ⇑(G.transition.childCoreIntoParent c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun

noncomputable def childCoreInclusionCoe : G.transition.ChildCore c → (G.Child c).Carrier :=
  ⇑(G.transition.childCoreInclusion c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreInclusionCoe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreInclusionCoe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreInclusionCoe ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreInclusionCoe

theorem childCoreIntoParent_isEmbedding :
    Topology.IsEmbedding (G.transition.childCoreIntoParent c) := by
  have hcomp : Topology.IsEmbedding (fun x : G.transition.ChildCore c =>
      (x.1.1 : (H.stage i.castSucc).Carrier)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hcomp' : Topology.IsEmbedding (Subtype.val ∘ ⇑(G.transition.childCoreIntoParent c)) :=
    hcomp
  exact (Topology.IsEmbedding.of_comp_iff
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (Subtype.val : (G.Parent c).Carrier → (H.stage i.castSucc).Carrier))).mp hcomp'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParent_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParent_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParent_isEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParent_isEmbedding

theorem collar_injective (b : G.ChildBoundary c) : Function.Injective (K.collar b) := by
  intro x y hxy
  have h1 : ((G.static b.1).neck.chart (K.collarParameter b x).1).1 =
      ((G.static b.1).neck.chart (K.collarParameter b y).1).1 := by
    rw [← K.collar_eq b x, ← K.collar_eq b y]
    exact congrArg (fun z : (G.Parent c).Carrier => (z.1 : (H.stage i.castSucc).Carrier)) hxy
  have h2 : (G.static b.1).neck.chart (K.collarParameter b x).1 =
      (G.static b.1).neck.chart (K.collarParameter b y).1 := Subtype.ext h1
  have h3 : (K.collarParameter b x).1 = (K.collarParameter b y).1 :=
    ((G.static b.1).neck.chart_smooth).isEmbedding.injective h2
  have h4 : K.collarParameter b x = K.collarParameter b y := Subtype.ext h3
  have h7 : (K.collarParameter b x).1.1 = (K.collarParameter b y).1.1 :=
    congrArg (fun z : ↑(neckCentralDomain (G.static b.1).delta) => z.1.1) h4
  rw [K.collarParameter_eq b x, K.collarParameter_eq b y] at h7
  obtain ⟨hx1, hx2⟩ := Prod.ext_iff.mp h7
  exact Prod.ext hx1 (Subtype.ext hx2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_injective

theorem collar_isClosedEmbedding (b : G.ChildBoundary c) :
    Topology.IsClosedEmbedding (K.collar b) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (K.collar b).continuous (K.collar_injective b)
    (fun _s hs => (hs.isCompact.image (K.collar b).continuous).isClosed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_isClosedEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_isClosedEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_isClosedEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collar_isClosedEmbedding

theorem collarParameter_continuous (b : G.ChildBoundary c) :
    Continuous (K.collarParameter b) := by
  have h2 : Continuous (fun x : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
      (K.collarParameter b x).1.1) := by
    have heq : (fun x : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
        (K.collarParameter b x).1.1) =
        fun x => (x.1, ((x.2 : ↑(Icc (K.level b) 0)) : ℝ)) := by
      funext x
      exact K.collarParameter_eq b x
    rw [heq]
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact Continuous.subtype_mk (Continuous.subtype_mk h2 (fun x => (K.collarParameter b x).1.2))
    (fun x => (K.collarParameter b x).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_continuous

theorem exterior_exists (x : (G.Parent c).Carrier) (hx : x ∉ K.support.region) :
    ∃ b : G.ChildBoundary c, x ∈ (K.exterior.exterior (K.boundaryLabel b)).region := by
  have hx' : x ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
    rw [K.exterior.cover]
    trivial
  rcases hx' with hR | hU
  · exact absurd hR hx
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
    refine ⟨K.boundaryLabel.symm e, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exterior_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exterior_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exterior_exists ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exterior_exists

theorem localCollapse_level_zero_eq_childCoreInclusion
    (b : G.ChildBoundary c) (y : Sphere 2) (y' : G.transition.ChildCore c)
    (hy' : G.transition.childCoreIntoParent c y' =
      K.collar b (y, ⟨0, (K.level_negative b).le, le_rfl⟩)) :
    K.localCollapse b (K.collarParameter b (y, ⟨0, (K.level_negative b).le, le_rfl⟩)) =
      G.transition.childCoreInclusion c y' := by
  set x0 : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) := (y, ⟨0, (K.level_negative b).le, le_rfl⟩) with hx0
  set p : ↑(neckCentralDomain (G.static b.1).delta) := K.collarParameter b x0 with hp
  have hp1 : p.1.1 = (y, (0 : ℝ)) := by
    rw [hp, K.collarParameter_eq b x0]
  have hp2 : p.1.1.2 = (0 : ℝ) := congrArg Prod.snd hp1
  have hz0 : 0 ≤ p.1.1.2 := by rw [hp2]
  set zz : neckRetainedCollar (G.static b.1).delta := ⟨p.1.1, hz0, p.2.2⟩ with hzz
  have hcollapse : (G.static b.1).witness.collapse p =
      (G.static b.1).witness.retained zz := by
    rw [hzz]
    exact (G.static b.1).witness.collapse_retained p hz0
  have hlc : (K.localCollapse b p).1 =
      (G.static b.1).inclusion ((G.static b.1).witness.retained zz) := by
    rw [K.localCollapse_eq b p, hcollapse]
  have hpres : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion ((G.static b.1).retainedPoint zz).1)
      = Sum.inl ((K.localCollapse b p).1) := by
    rw [hlc]
    exact (G.static b.1).retained_eq zz
  have hpt : ((G.static b.1).retainedPoint zz).1.1 = (K.collar b x0).1 := by
    rw [(G.static b.1).retained_point_eq zz p.1.2, K.collar_eq b x0]
  have hy1 : y'.1.1 = (K.collar b x0).1 :=
    congrArg (fun z : (G.Parent c).Carrier => (z.1 : (H.stage i.castSucc).Carrier)) hy'
  have hcore : ((G.static b.1).retainedPoint zz).1 = y'.1 :=
    Subtype.ext (hpt.trans hy1.symm)
  have hpres' : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion y'.1)
      = Sum.inl ((K.localCollapse b p).1) := by
    rw [← hcore]
    exact hpres
  have hcc := G.transition.childCoreInclusionFun_eq c y'
  have hinl : Sum.inl ((K.localCollapse b p).1) =
      Sum.inl ((G.transition.childCoreInclusionFun c y').1) := hpres'.symm.trans hcc
  exact Subtype.ext (Sum.inl.inj hinl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_zero_eq_childCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_zero_eq_childCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_zero_eq_childCoreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_zero_eq_childCoreInclusion

theorem localCollapse_level_eq_tip (b : G.ChildBoundary c) (y : Sphere 2) :
    K.localCollapse b (K.collarParameter b
      (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)) = K.tip b := by
  have hlt : (K.collarParameter b
      (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩)).1.1.2 = K.level b := by
    rw [K.collarParameter_eq b _]
  have hc : (G.static b.1).witness.collapse
      (K.collarParameter b (y, ⟨K.level b, le_rfl, (K.level_negative b).le⟩))
      = (G.static b.1).witness.tip :=
    (G.static b.1).witness.collapse_tip _
      (by
        rw [hlt]
        exact (K.level_below_tip b).le)
  apply Subtype.ext
  rw [K.localCollapse_eq b _, K.tip_eq b, hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_eq_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_eq_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_eq_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localCollapse_level_eq_tip

theorem childCoreIntoParentFun_injective :
    Function.Injective (childCoreIntoParentFun (G := G) (c := c)) :=
  fun _ _ h => (childCoreIntoParent_isEmbedding (G := G) (c := c)).injective h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_injective

theorem exists_collarValue (x : (G.Parent c).Carrier)
    (h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)),
      K.collar b w = x) :
    ∃ v : (G.Child c).Carrier, ∀ (b : G.ChildBoundary c)
      (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)),
      K.collar b w = x → v = K.localCollapse b (K.collarParameter b w) := by
  obtain ⟨b₀, w₀, hw₀⟩ := h
  refine ⟨K.localCollapse b₀ (K.collarParameter b₀ w₀), fun b w hw => ?_⟩
  have hb : b₀ = b := by
    by_contra hne
    exact (Set.disjoint_left.mp (K.collar_disjoint hne)) ⟨_, hw₀⟩ ⟨_, hw⟩
  subst hb
  have hw' : w₀ = w := K.collar_injective _ (hw₀.trans hw.symm)
  subst hw'
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarValue ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarValue

noncomputable def collarChoiceValue (x : (G.Parent c).Carrier)
    (h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)),
      K.collar b w = x) : (G.Child c).Carrier :=
  Classical.choose (K.exists_collarValue x h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue

theorem collarChoiceValue_eq {x : (G.Parent c).Carrier}
    {h : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)),
      K.collar b w = x} {b : G.ChildBoundary c}
    {w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)} (hw : K.collar b w = x) :
    K.collarChoiceValue x h = K.localCollapse b (K.collarParameter b w) :=
  Classical.choose_spec (K.exists_collarValue x h) b w hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarChoiceValue_eq

noncomputable def supportFun (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    (G.Child c).Carrier := by
  classical
  exact if h : ∃ y : G.transition.ChildCore c, childCoreIntoParentFun y = x then
    childCoreInclusionCoe (Classical.choose h)
  else if h' : ∃ (b : G.ChildBoundary c) (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)),
      K.collar b w = x then
    K.collarChoiceValue x h'
  else d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun

theorem supportFun_core (d : (G.Child c).Carrier) (y : G.transition.ChildCore c) :
    K.supportFun d (childCoreIntoParentFun y) = childCoreInclusionCoe y := by
  have h : ∃ y' : G.transition.ChildCore c,
      childCoreIntoParentFun y' = childCoreIntoParentFun y := ⟨y, rfl⟩
  rw [supportFun, dif_pos h]
  exact congrArg childCoreInclusionCoe
    (childCoreIntoParentFun_injective (G := G) (c := c) (Classical.choose_spec h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_core

theorem supportFun_collar (d : (G.Child c).Carrier) (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)) :
    K.supportFun d (K.collar b w) = K.localCollapse b (K.collarParameter b w) := by
  by_cases h : ∃ y : G.transition.ChildCore c, childCoreIntoParentFun y = K.collar b w
  · rw [supportFun, dif_pos h]
    have hmem : K.collar b w ∈ Set.range (K.collar b) ∩
        Set.range (G.transition.childCoreIntoParent c) :=
      ⟨Set.mem_range_self w, ⟨Classical.choose h, Classical.choose_spec h⟩⟩
    rw [K.collar_core_intersection b] at hmem
    obtain ⟨y', hy'⟩ := Set.mem_range.mp hmem
    have hw : w = (y', ⟨0, (K.level_negative b).le, le_rfl⟩) :=
      (K.collar_injective b hy').symm
    have hpp : K.collarParameter b w =
        K.collarParameter b (y', ⟨0, (K.level_negative b).le, le_rfl⟩) := by
      apply Subtype.ext
      apply Subtype.ext
      rw [K.collarParameter_eq b w,
        K.collarParameter_eq b (y', ⟨0, (K.level_negative b).le, le_rfl⟩), hw]
    rw [hpp]
    refine (K.localCollapse_level_zero_eq_childCoreInclusion b y' (Classical.choose h) ?_).symm
    exact (Classical.choose_spec h).trans (congrArg (K.collar b) hw)
  · have h' : ∃ (b' : G.ChildBoundary c) (w' : Sphere 2 × ↑(_root_.Set.Icc (K.level b') 0)),
        K.collar b' w' = K.collar b w := ⟨b, w, rfl⟩
    rw [supportFun, dif_neg h, dif_pos h']
    exact K.collarChoiceValue_eq rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.supportFun_collar

theorem childCoreIntoParentFun_continuous :
    Continuous (childCoreIntoParentFun (G := G) (c := c)) :=
  (G.transition.childCoreIntoParent c).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCoreIntoParentFun_continuous

theorem isClosed_range_childCoreIntoParentFun :
    IsClosed (Set.range (childCoreIntoParentFun (G := G) (c := c))) := by
  have hcl : IsClosed {z : (H.event i).transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} := by
    obtain ⟨z₀, hz₀⟩ := ConnectedComponents.surjective_coe (G.transition.childCoreComponent c)
    have hset : {z : (H.event i).transition.trace.tubes.core |
        ConnectedComponents.mk z = G.transition.childCoreComponent c} = connectedComponent z₀ := by
      ext z
      rw [← ConnectedComponents.coe_eq_coe', hz₀]
      exact Iff.rfl
    rw [hset]
    exact isClosed_connectedComponent
  have hcompact : IsCompact {z : (H.event i).transition.trace.tubes.core |
      ConnectedComponents.mk z = G.transition.childCoreComponent c} :=
    @IsClosed.isCompact _ _ _ G.transition.core_compact hcl
  have hsub : CompactSpace (G.transition.ChildCore c) := isCompact_iff_compactSpace.mp hcompact
  exact (@isCompact_range _ _ _ _ hsub _
    (childCoreIntoParentFun_continuous (G := G) (c := c))).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.isClosed_range_childCoreIntoParentFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.isClosed_range_childCoreIntoParentFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.isClosed_range_childCoreIntoParentFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.isClosed_range_childCoreIntoParentFun

theorem continuousOn_supportFun_range_core (d : (G.Child c).Carrier) :
    ContinuousOn (K.supportFun d) (Set.range (childCoreIntoParentFun (G := G) (c := c))) := by
  have hind : Topology.IsInducing (childCoreIntoParentFun (G := G) (c := c)) :=
    (childCoreIntoParent_isEmbedding (G := G) (c := c)).isInducing
  rw [← Set.image_univ, hind.continuousOn_image_iff, continuousOn_univ]
  exact (G.transition.childCoreInclusion c).continuous.congr
    fun y => (K.supportFun_core d y).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_core

theorem continuousOn_supportFun_range_collar (d : (G.Child c).Carrier) (b : G.ChildBoundary c) :
    ContinuousOn (K.supportFun d) (Set.range (K.collar b)) := by
  have hind : Topology.IsInducing (K.collar b) :=
    (K.collar_isClosedEmbedding b).isEmbedding.isInducing
  rw [← Set.image_univ, hind.continuousOn_image_iff, continuousOn_univ]
  exact ((K.localCollapse b).continuous.comp (K.collarParameter_continuous b)).congr
    fun w => (K.supportFun_collar d b w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_range_collar

theorem continuousOn_supportFun_region (d : (G.Child c).Carrier) :
    ContinuousOn (K.supportFun d) K.support.region := by
  classical
  let piece : Option (G.ChildBoundary c) → Set (G.Parent c).Carrier := fun o =>
    match o with
    | none => Set.range (childCoreIntoParentFun (G := G) (c := c))
    | some b => Set.range (K.collar b)
  have hcover : ⋃ o, piece o = K.support.region := by
    rw [Set.iUnion_option piece]
    simp only [piece, K.support_eq]
    rfl
  rw [← hcover]
  refine (locallyFinite_of_finite piece).continuousOn_iUnion ?_ ?_
  · intro o
    cases o with
    | none => exact isClosed_range_childCoreIntoParentFun (G := G) (c := c)
    | some b => exact (K.collar_isClosedEmbedding b).isClosed_range
  · intro o
    cases o with
    | none => exact K.continuousOn_supportFun_range_core d
    | some b => exact K.continuousOn_supportFun_range_collar d b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_region ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.continuousOn_supportFun_region

noncomputable def wholeParentMapFun (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    (G.Child c).Carrier := by
  classical
  exact if hx : x ∈ K.support.region then K.supportFun d x
    else K.tip (Classical.choose (K.exterior_exists x hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun

theorem wholeParentMapFun_of_mem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∈ K.support.region) :
    K.wholeParentMapFun d x = K.supportFun d x := by
  rw [wholeParentMapFun, dif_pos hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_mem

theorem wholeParentMapFun_of_notMem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∉ K.support.region) :
    K.wholeParentMapFun d x = K.tip (Classical.choose (K.exterior_exists x hx)) := by
  rw [wholeParentMapFun, dif_neg hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_notMem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_of_notMem

theorem wholeParentMapFun_continuousOn_region (d : (G.Child c).Carrier) :
    ContinuousOn (K.wholeParentMapFun d) K.support.region :=
  (K.continuousOn_supportFun_region d).congr fun _ hx => K.wholeParentMapFun_of_mem d hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_region ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_region

theorem wholeParentMapFun_eq_tip_of_mem_exterior (d : (G.Child c).Carrier)
    {e : K.support.Boundary} {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior e).region) :
    K.wholeParentMapFun d x = K.tip (K.boundaryLabel.symm e) := by
  by_cases hR : x ∈ K.support.region
  · have hxint : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        Set.range (K.support.sphere e) := by
      rw [← K.exterior.intersection e]
      exact ⟨hx, hR⟩
    have hx' : x ∈ (Subtype.val : K.support.region → (G.Parent c).Carrier) ''
        Set.range (K.support.sphere (K.boundaryLabel (K.boundaryLabel.symm e))) := by
      rw [Equiv.apply_symm_apply]
      exact hxint
    rw [K.boundary_eq (K.boundaryLabel.symm e)] at hx'
    obtain ⟨y', hy'⟩ := hx'
    rw [K.wholeParentMapFun_of_mem d hR, ← hy',
      K.supportFun_collar d (K.boundaryLabel.symm e)]
    exact K.localCollapse_level_eq_tip (K.boundaryLabel.symm e) y'
  · have heq : K.boundaryLabel (Classical.choose (K.exterior_exists x hR)) = e := by
      by_contra hne
      exact (Set.disjoint_left.mp (K.exterior.disjoint hne))
        (Classical.choose_spec (K.exterior_exists x hR)) hx
    have hb : Classical.choose (K.exterior_exists x hR) = K.boundaryLabel.symm e :=
      K.boundaryLabel.injective (heq.trans (Equiv.apply_symm_apply K.boundaryLabel e).symm)
    rw [K.wholeParentMapFun_of_notMem d hR, hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_eq_tip_of_mem_exterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_eq_tip_of_mem_exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_eq_tip_of_mem_exterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_eq_tip_of_mem_exterior

theorem wholeParentMapFun_continuousOn_exterior (d : (G.Child c).Carrier)
    (e : K.support.Boundary) :
    ContinuousOn (K.wholeParentMapFun d) (K.exterior.exterior e).region :=
  continuousOn_const.congr fun _ hx => K.wholeParentMapFun_eq_tip_of_mem_exterior d hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_exterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_exterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuousOn_exterior

theorem wholeParentMapFun_continuous (d : (G.Child c).Carrier) :
    Continuous (K.wholeParentMapFun d) := by
  classical
  let finBoundary : Fintype K.support.Boundary := K.support.finiteBoundary
  let piece : Option K.support.Boundary → Set (G.Parent c).Carrier := fun o =>
    match o with
    | none => K.support.region
    | some e => (K.exterior.exterior e).region
  refine (locallyFinite_of_finite piece).continuous ?_ ?_ ?_
  · rw [Set.iUnion_option piece]
    simp only [piece]
    exact K.exterior.cover
  · intro o
    cases o with
    | none => exact K.support.compact.isClosed
    | some e => exact (K.exterior.exterior e).compact.isClosed
  · intro o
    cases o with
    | none => exact K.wholeParentMapFun_continuousOn_region d
    | some e => exact K.wholeParentMapFun_continuousOn_exterior d e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMapFun_continuous

noncomputable def wholeParentMap (d : (G.Child c).Carrier) :
    C((G.Parent c).Carrier, (G.Child c).Carrier) :=
  ⟨K.wholeParentMapFun d, K.wholeParentMapFun_continuous d⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap

@[simp] theorem wholeParentMap_apply (d : (G.Child c).Carrier) (x : (G.Parent c).Carrier) :
    K.wholeParentMap d x = K.wholeParentMapFun d x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_apply

theorem wholeParentMap_of_mem (d : (G.Child c).Carrier) {x : (G.Parent c).Carrier}
    (hx : x ∈ K.support.region) :
    K.wholeParentMap d x = K.supportFun d x := by
  rw [wholeParentMap_apply, K.wholeParentMapFun_of_mem d hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_of_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_of_mem

theorem wholeParentMap_isWholeParentMap (d : (G.Child c).Carrier) :
    K.IsWholeParentMap (K.wholeParentMap d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine (K.wholeParentMap_of_mem d ?_).trans (K.supportFun_core d y)
    rw [K.support_eq]
    exact Or.inl ⟨y, rfl⟩
  · intro b w
    refine (K.wholeParentMap_of_mem d ?_).trans (K.supportFun_collar d b w)
    rw [K.support_eq]
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self w⟩)
  · intro b x hx
    rw [K.wholeParentMap_apply, K.wholeParentMapFun_eq_tip_of_mem_exterior d hx,
      Equiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_isWholeParentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_isWholeParentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_isWholeParentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_isWholeParentMap

theorem exists_unique_wholeParentMap :
    ∃! f : C((G.Parent c).Carrier, (G.Child c).Carrier), K.IsWholeParentMap f := by
  classical
  obtain ⟨q₀, hq₀⟩ := ConnectedComponents.surjective_coe c
  let d : (G.Child c).Carrier := ⟨q₀, hq₀⟩
  refine ⟨K.wholeParentMap d, K.wholeParentMap_isWholeParentMap d, ?_⟩
  · intro g hg
    apply ContinuousMap.ext
    intro x
    rw [K.wholeParentMap_apply]
    have hx' : x ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
      rw [K.exterior.cover]
      trivial
    rcases hx' with hR | hU
    · have hmem : x ∈ Set.range (G.transition.childCoreIntoParent c) ∪
          ⋃ b, Set.range (K.collar b) := by
        rw [← K.support_eq]
        exact hR
      rcases hmem with hc | hcoll
      · obtain ⟨y, hy⟩ := Set.mem_range.mp hc
        have hxR : G.transition.childCoreIntoParent c y ∈ K.support.region := by
          rw [K.support_eq]
          exact Or.inl ⟨y, rfl⟩
        have hwv : K.wholeParentMapFun d (G.transition.childCoreIntoParent c y) =
            childCoreInclusionCoe y :=
          (K.wholeParentMapFun_of_mem d hxR).trans (K.supportFun_core d y)
        rw [← hy]
        exact (hg.1 y).trans hwv.symm
      · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcoll
        obtain ⟨w, hw⟩ := Set.mem_range.mp hb
        have hxR : K.collar b w ∈ K.support.region := by
          rw [K.support_eq]
          exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self w⟩)
        have hwv : K.wholeParentMapFun d (K.collar b w) =
            K.localCollapse b (K.collarParameter b w) :=
          (K.wholeParentMapFun_of_mem d hxR).trans (K.supportFun_collar d b w)
        rw [← hw]
        exact (hg.2.1 b w).trans hwv.symm
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      have hge : g x = K.tip (K.boundaryLabel.symm e) := by
        refine hg.2.2 (K.boundaryLabel.symm e) x ?_
        rwa [Equiv.apply_symm_apply]
      rw [hge, K.wholeParentMapFun_eq_tip_of_mem_exterior d he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_unique_wholeParentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_unique_wholeParentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_unique_wholeParentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_unique_wholeParentMap

def rfs_whole_parent_map : C((G.Parent c).Carrier, (G.Child c).Carrier) :=
  Classical.choose K.exists_unique_wholeParentMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map

theorem wholeParentMap_spec : K.IsWholeParentMap K.rfs_whole_parent_map :=
  (Classical.choose_spec K.exists_unique_wholeParentMap).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.wholeParentMap_spec

theorem rfs_whole_parent_map_eq_wholeParentMap (d : (G.Child c).Carrier) :
    K.rfs_whole_parent_map = K.wholeParentMap d :=
  ((Classical.choose_spec K.exists_unique_wholeParentMap).2 _
    (K.wholeParentMap_isWholeParentMap d)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_wholeParentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_wholeParentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_wholeParentMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_wholeParentMap

theorem rfs_whole_parent_map_childCore (x : G.transition.ChildCore c) :
    K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
      G.transition.childCoreInclusion c x :=
  K.wholeParentMap_spec.1 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_childCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_childCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_childCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_childCore

theorem rfs_whole_parent_map_collar (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)) :
    K.rfs_whole_parent_map (K.collar b w) =
      K.localCollapse b (K.collarParameter b w) :=
  K.wholeParentMap_spec.2.1 b w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_collar

theorem rfs_whole_parent_map_eq_tip_of_mem_exterior (b : G.ChildBoundary c)
    {x : (G.Parent c).Carrier}
    (hx : x ∈ (K.exterior.exterior (K.boundaryLabel b)).region) :
    K.rfs_whole_parent_map x = K.tip b :=
  K.wholeParentMap_spec.2.2 b x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_tip_of_mem_exterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_tip_of_mem_exterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_tip_of_mem_exterior ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_eq_tip_of_mem_exterior

theorem rfs_whole_parent_map_locallyConstant_of_notMem {x : (G.Parent c).Carrier}
    (hx : x ∉ K.support.region) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, K.rfs_whole_parent_map y = K.rfs_whole_parent_map x := by
  classical
  let : Fintype K.support.Boundary := K.support.finiteBoundary
  obtain ⟨b₀, hb₀⟩ := K.exterior_exists x hx
  have hxS : x ∈ (K.exterior.exterior (K.boundaryLabel b₀)).region := hb₀
  have hclosed : IsClosed (K.support.region ∪
      ⋃ e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀},
        (K.exterior.exterior e.1).region) :=
    K.support.compact.isClosed.union
      (isClosed_iUnion_of_finite fun e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀} =>
        (K.exterior.exterior e.1).compact.isClosed)
  have hxU : x ∈ (K.support.region ∪
      ⋃ e : {e' : K.support.Boundary // e' ≠ K.boundaryLabel b₀},
        (K.exterior.exterior e.1).region)ᶜ := by
    intro hmem
    rcases hmem with hR | hU
    · exact hx hR
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      exact (Set.disjoint_left.mp (K.exterior.disjoint (Ne.symm e.2))) hxS he
  refine ⟨_, hclosed.isOpen_compl.mem_nhds hxU, ?_⟩
  intro y hy
  have hyS : y ∈ (K.exterior.exterior (K.boundaryLabel b₀)).region := by
    have hcover : y ∈ K.support.region ∪ ⋃ e, (K.exterior.exterior e).region := by
      rw [K.exterior.cover]
      trivial
    rcases hcover with hR | hU
    · exact absurd hR (fun h => hy (Or.inl h))
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hU
      by_cases hee : e = K.boundaryLabel b₀
      · rwa [hee] at he
      · exact absurd (Set.mem_iUnion.mpr ⟨⟨e, hee⟩, he⟩) (fun h => hy (Or.inr h))
  rw [K.rfs_whole_parent_map_eq_tip_of_mem_exterior b₀ hxS,
    K.rfs_whole_parent_map_eq_tip_of_mem_exterior b₀ hyS]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_locallyConstant_of_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_locallyConstant_of_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_locallyConstant_of_notMem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_locallyConstant_of_notMem

theorem rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl
    {γ : ℝ → (G.Parent c).Carrier} {a b : ℝ}
    (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (hmap : ∀ t ∈ _root_.Set.Icc a b, γ t ∉ K.support.region) :
    riemannianCurveLength (H.event i).outputMetric
      (fun t => (K.rfs_whole_parent_map (γ t)).1) a b = 0 := by
  by_cases hab : a ≤ b
  · refine riemannianCurveLength_eq_zero_of_apply_eq_const _ _
      (q := (K.rfs_whole_parent_map (γ a)).1) ?_
    let γ' : _root_.Set.Icc a b → (G.Parent c).Carrier := fun t => γ t
    have hcont : Continuous γ' := hγ.domRestrict
    have hlc : IsLocallyConstant (fun t : _root_.Set.Icc a b => K.rfs_whole_parent_map (γ' t)) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro t
      have ht : γ t ∉ K.support.region := hmap t t.2
      obtain ⟨U, hU, hfU⟩ := K.rfs_whole_parent_map_locallyConstant_of_notMem ht
      obtain ⟨V, hVU, hVo, htV⟩ := mem_nhds_iff.mp hU
      exact ⟨γ' ⁻¹' V, hcont.isOpen_preimage V hVo, htV,
        fun s hs => hfU (γ' s) (hVU hs)⟩
    have hpre : PreconnectedSpace (_root_.Set.Icc a b) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hconst := congrFun (@IsLocallyConstant.eq_const (_root_.Set.Icc a b)
      ((G.Child c).Carrier) inferInstance hpre
      (fun t : _root_.Set.Icc a b => K.rfs_whole_parent_map (γ' t)) hlc ⟨a, left_mem_Icc.mpr hab⟩)
    intro t ht
    exact congrArg Subtype.val (hconst ⟨t, ht⟩)
  · exact riemannianCurveLength_eq_zero_of_apply_eq_const _ _
      (q := (K.rfs_whole_parent_map (γ a)).1)
      (fun t ht => absurd (ht.1.trans ht.2) hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_curveLength_eq_zero_of_mapsTo_compl

theorem rfs_whole_parent_map_surjective_of_cover
    (hcov : Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = _root_.Set.univ) :
    Function.Surjective K.rfs_whole_parent_map := by
  intro v
  have hv : v ∈ Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) := by
    rw [hcov]
    trivial
  rcases hv with hcore | hcollar
  · obtain ⟨y, rfl⟩ := hcore
    exact ⟨G.transition.childCoreIntoParent c y, K.rfs_whole_parent_map_childCore y⟩
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hcollar
    obtain ⟨w, rfl⟩ := hb
    exact ⟨K.collar b w, K.rfs_whole_parent_map_collar b w⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_surjective_of_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_surjective_of_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_surjective_of_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_surjective_of_cover

def LocalTerminalLengthControl (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  ∀ x ∈ K.support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    (∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf (H.event i).outputMetric (f y).1 (f z).1 ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩) ∧
    (∀ (γ : ℝ → (H.event i).incoming.terminalRegularOpen)
      (hparent : ∀ t, ConnectedComponents.mk (γ t).1 = G.transition.childParent c)
      (a b : ℝ), a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) →
      (∀ t ∈ _root_.Set.Icc a b, (⟨(γ t).1, hparent t⟩ : (G.Parent c).Carrier) ∈ U) →
      riemannianCurveLength (H.event i).terminal.metric γ a b ≠ ⊤ →
      riemannianCurveLength (H.event i).outputMetric
        (fun t => (f ⟨(γ t).1, hparent t⟩).1) a b ≤
          riemannianCurveLength (H.event i).terminal.metric γ a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalLengthControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalLengthControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalLengthControl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalLengthControl

theorem rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz
    (hf : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map := by
  intro x hx
  refine ⟨{y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      (K.support_terminal x hx),
    fun _ hy => hy, fun y _ z _ hy hz => hf y z hy hz, ?_⟩
  intro γ hparent a b hab hγ hU hlen
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_iSup (fun q : ℕ ×
    {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ _root_.Set.Icc a b} =>
      ∑ j ∈ Finset.range q.1, riemannianEDistOf (H.event i).terminal.metric
        (γ (q.2.1 (j + 1))) (γ (q.2.1 j))) p)
  exact hf ⟨(γ (p.2.1 (k + 1))).1, hparent (p.2.1 (k + 1))⟩
    ⟨(γ (p.2.1 k)).1, hparent (p.2.1 k)⟩ (γ (p.2.1 (k + 1))).2 (γ (p.2.1 k)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz

theorem rfs_collapse_degree_of_local_inputs
    (hlip : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)
    (hcov : Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = _root_.Set.univ) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    Function.Surjective K.rfs_whole_parent_map :=
  ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_lipschitz hlip,
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    fun x => K.rfs_whole_parent_map_childCore x,
    K.rfs_whole_parent_map_surjective_of_cover hcov⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_local_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_local_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_local_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_local_inputs

theorem collarParameter_fst (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)) :
    (K.collarParameter b w).1.1.1 = w.1 :=
  congrArg Prod.fst (K.collarParameter_eq b w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_fst ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_fst

theorem collarParameter_snd (b : G.ChildBoundary c)
    (w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0)) :
    (K.collarParameter b w).1.1.2 = (w.2 : ℝ) :=
  congrArg (fun p : Sphere 2 × ℝ => p.2) (K.collarParameter_eq b w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_snd ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.collarParameter_snd

private theorem standardCapL_pos : (0 : ℝ) < standardCapL := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h : 0 < Real.pi / Real.sqrt 2 := div_pos hpi hsqrt
  simp only [standardCapL, standardCapA0]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.standardCapL_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.standardCapL_pos target :: scope.openDecls } }

theorem exists_collarParameter_collapse_eq_cap (b : G.ChildBoundary c) (x : ThreeBall) :
    ∃ w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0),
      (K.localCollapse b (K.collarParameter b w)).1 =
        (G.static b.1).inclusion ((G.static b.1).witness.cap x) := by
  classical
  have hmem : (G.static b.1).witness.cap x ∈
      Set.range (G.static b.1).witness.capChart := by
    rw [(G.static b.1).witness.capChart_range]
    exact Set.mem_range_self x
  obtain ⟨x₀, hx₀⟩ := hmem
  have hnorm_le : ‖x₀.1‖ ≤ standardCapL := by
    simpa [standardCapClosedCore, Metric.mem_closedBall, dist_eq_norm] using x₀.2
  by_cases hzero : x₀.1 = 0
  · refine ⟨((G.static b.1).neck.sphereMark,
      ⟨K.level b, le_rfl, (K.level_negative b).le⟩), ?_⟩
    have hx0eq : x₀ = (⟨0, by simpa [standardCapClosedCore, hzero] using x₀.2⟩ :
        standardCapClosedCore) := Subtype.ext hzero
    have hcap : (G.static b.1).witness.cap x = (G.static b.1).witness.tip := by
      rw [← hx₀, hx0eq]
      exact (G.static b.1).witness.capChart_tip _
    have hcoll : (G.static b.1).witness.collapse
        (K.collarParameter b ((G.static b.1).neck.sphereMark,
          ⟨K.level b, le_rfl, (K.level_negative b).le⟩)) =
        (G.static b.1).witness.tip := by
      refine (G.static b.1).witness.collapse_tip _ ?_
      rw [K.collarParameter_snd b _]
      exact (K.level_below_tip b).le
    rw [K.localCollapse_eq b _, hcoll, hcap]
  · have hpos : 0 < ‖x₀.1‖ := norm_pos_iff.mpr hzero
    let y : Sphere 2 :=
      ⟨(‖x₀.1‖⁻¹ : ℝ) • x₀.1, by
        rw [Metric.mem_sphere, dist_zero_right]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x₀.1))]
        exact inv_mul_cancel₀ (ne_of_gt hpos)⟩
    have htip_le : (G.static b.1).witness.tipCoordinate ≤ 0 := by
      have h1 := (G.static b.1).witness.tipCoordinate_upper
      have h2 := parameters.fixed.collar_pos
      have h3 := standardCapL_pos
      linarith
    obtain ⟨zz, hzz, hzzr⟩ : ∃ zz ∈ Set.Icc (G.static b.1).witness.tipCoordinate 0,
        (G.static b.1).witness.radial zz = ‖x₀.1‖ := by
      have hsub := intermediate_value_Icc htip_le (G.static b.1).witness.radial_continuous
      have hmem' : ‖x₀.1‖ ∈ Set.Icc
          ((G.static b.1).witness.radial (G.static b.1).witness.tipCoordinate)
          ((G.static b.1).witness.radial 0) := by
        rw [(G.static b.1).witness.radial_tip, (G.static b.1).witness.radial_boundary]
        exact ⟨norm_nonneg _, hnorm_le⟩
      exact hsub hmem'
    have hzz_gt : (G.static b.1).witness.tipCoordinate < zz := by
      rcases lt_trichotomy zz (G.static b.1).witness.tipCoordinate with h | h | h
      · exact absurd h (not_lt.mpr hzz.1)
      · rw [h, (G.static b.1).witness.radial_tip] at hzzr
        exact absurd hzzr.symm (ne_of_gt hpos)
      · exact h
    have hsmul : (G.static b.1).witness.radial zz • y.1 = x₀.1 := by
      rw [hzzr]
      exact smul_inv_smul₀ (ne_of_gt hpos) x₀.1
    have hlevel : K.level b ≤ (⟨zz, (lt_trans (K.level_below_tip b) hzz_gt).le, hzz.2⟩ :
        ↑(_root_.Set.Icc (K.level b) 0)) := (lt_trans (K.level_below_tip b) hzz_gt).le
    refine ⟨(y, ⟨zz, hlevel, hzz.2⟩), ?_⟩
    have hball : (G.static b.1).witness.radial
        ((K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2) •
        ((K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.1.1) ∈ standardCapClosedCore := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩),
        K.collarParameter_fst b (y, ⟨zz, hlevel, hzz.2⟩), hsmul]
      exact x₀.2
    have hgt : (G.static b.1).witness.tipCoordinate <
        (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2 := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hzz_gt
    have hle : (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)).1.1.2 ≤ 0 := by
      rw [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hzz.2
    have hcollapse : (G.static b.1).witness.collapse
        (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)) =
        (G.static b.1).witness.capChart x₀ := by
      rw [(G.static b.1).witness.collapse_radial (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩))
        hgt hle hball]
      refine congrArg (G.static b.1).witness.capChart (Subtype.ext ?_)
      simp only [K.collarParameter_snd b (y, ⟨zz, hlevel, hzz.2⟩),
        K.collarParameter_fst b (y, ⟨zz, hlevel, hzz.2⟩)]
      exact hsmul
    rw [K.localCollapse_eq b (K.collarParameter b (y, ⟨zz, hlevel, hzz.2⟩)), hcollapse, hx₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarParameter_collapse_eq_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarParameter_collapse_eq_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarParameter_collapse_eq_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.exists_collarParameter_collapse_eq_cap

theorem rfs_collapse_cover :
    Set.range (G.transition.childCoreInclusion c) ∪
      (⋃ b : G.ChildBoundary c, Set.range (fun w : Sphere 2 × ↑(_root_.Set.Icc (K.level b) 0) =>
        K.localCollapse b (K.collarParameter b w))) = univ := by
  have hcov := G.transition.range_childCoreInclusion_union_range_childCap c
  refine Set.eq_univ_of_forall fun v => ?_
  have hv : v ∈ Set.range (G.transition.childCoreInclusion c) ∪
      ⋃ b : G.transition.ChildCapBoundary c, Set.range (G.transition.childCap c b) := by
    rw [hcov]
    trivial
  rcases hv with h | h
  · exact Or.inl h
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
    obtain ⟨z, hz⟩ := hb
    have hbRet : (H.event i).RetainedBoundary b.1 :=
      G.transition.retainedBoundary_of_mem_childCapBoundary c b
    obtain ⟨w, hw⟩ := K.exists_collarParameter_collapse_eq_cap
      (⟨⟨b.1, hbRet⟩, b.2⟩ : G.ChildBoundary c) z
    refine Or.inr (Set.mem_iUnion.mpr ⟨(⟨⟨b.1, hbRet⟩, b.2⟩ : G.ChildBoundary c), ?_⟩)
    refine ⟨w, Subtype.ext ?_⟩
    have hz1 : (G.transition.childCap c b z).1 =
        (G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).inclusion
          ((G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).witness.cap z) :=
      Sum.inl.inj ((G.transition.childCapFun_eq c b z).symm.trans
        ((G.static (⟨b.1, hbRet⟩ : (H.event i).RetainedBoundaryIndex)).cap_eq z))
    exact hw.trans (hz1.symm.trans (congrArg Subtype.val hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_cover


theorem childCore_subset_old (x : G.transition.ChildCore c) : x.1 ∈ (H.event i).old := by
  have hcoreCompact : CompactSpace G.transition.trace.tubes.core := G.transition.core_compact
  have hcoreConnected : LocallyConnectedSpace G.transition.trace.tubes.core :=
    G.transition.core_locallyConnected
  have h := CutCapTopology.childCore_subset_retainedCore (E := G.transition.trace) c x.2
  rw [G.old_eq_retained]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCore_subset_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCore_subset_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCore_subset_old ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.childCore_subset_old

theorem oldOutput_eq_childCoreInclusion (x : G.transition.ChildCore c) :
    (H.event i).oldOutput ⟨x.1, childCore_subset_old x⟩ =
      (G.transition.childCoreInclusion c x).1 :=
  Sum.inl.inj (((H.event i).oldOutput_eq
    ⟨x.1, childCore_subset_old x⟩).symm.trans (G.transition.childCoreInclusionFun_eq c x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.oldOutput_eq_childCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.oldOutput_eq_childCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.oldOutput_eq_childCoreInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.oldOutput_eq_childCoreInclusion

theorem rfs_collapse_degree_of_lipschitz_and_degree
    (hlip : ∀ (y z : (G.Parent c).Carrier),
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
        (K.rfs_whole_parent_map z).1 ≤
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)
    (hclass : integralHomologyMap 3 K.rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.rfs_whole_parent_map := by
  obtain ⟨h1, h2, h3, h4⟩ := K.rfs_collapse_degree_of_local_inputs hlip K.rfs_collapse_cover
  exact ⟨h1, h2, h3, hclass, h4⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_lipschitz_and_degree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_lipschitz_and_degree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_lipschitz_and_degree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_lipschitz_and_degree

end ComparisonSupport

theorem rfs_child_comparison_of_local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hdegree : ∀ c, integralHomologyMap 3 (Kc c).rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation)
    (hlocal : ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region,
        ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
          riemannianCurveLength ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s)
            (G.transition.childParent c)) γ a b ≠ ⊤ →
          riemannianCurveLength
            ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength
            ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₀, hs₀, ell, hell, htend, hloc⟩ := hlocal
  refine ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => ⟨Kc c, rfl⟩,
    fun c => hdegree c, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x y
  let gs : SmoothRiemannianMetric ThreeModel (G.Parent c).Carrier :=
    (H.stage i.castSucc).componentMetric ((H.event i).incoming.flow.base.metric s)
      (G.transition.childParent c)
  let hc : SmoothRiemannianMetric ThreeModel (G.Child c).Carrier :=
    (H.stage i.succ).componentMetric (H.event i).outputMetric c
  have hL : (0 : ℝ) ≤ ell s := le_trans zero_le_one (hell s hs)
  have hlocFull : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
      ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
        riemannianCurveLength gs γ a b ≠ ⊤ →
        riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength gs γ a b := by
    intro x
    by_cases hx : x ∈ (Kc c).support.region
    · obtain ⟨U, hU, hU'⟩ := hloc c s hs x hx
      exact ⟨U, hU, hU'⟩
    · obtain ⟨U, hU, hconst⟩ := (Kc c).rfs_whole_parent_map_locallyConstant_of_notMem hx
      refine ⟨U, hU, fun a b γ hab hγ hmap hfin => ?_⟩
      have hone : ∀ t ∈ _root_.Set.Icc a b, (fun t => (Kc c).rfs_whole_parent_map (γ t)) t =
          (Kc c).rfs_whole_parent_map x :=
        fun t ht => hconst (γ t) (hmap ht)
      have hzero := riemannianCurveLength_eq_zero_of_apply_eq_const (g := hc)
        (γ := fun t => (Kc c).rfs_whole_parent_map (γ t))
        (a := a) (b := b) (q := (Kc c).rfs_whole_parent_map x) hone
      rw [hzero]
      exact bot_le
  let : SecondCountableTopology (G.Parent c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Parent c).Carrier
  let : SecondCountableTopology (G.Child c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Child c).Carrier
  by_cases hfin : riemannianEDistOf gs x y = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (hell s hs))))]
    exact le_top
  · have hlocCoe : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
        ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
          riemannianCurveLength gs γ a b ≠ ⊤ →
          riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
            ↑(NNReal.mk (ell s) hL) * riemannianCurveLength gs γ a b :=
      fun x => by
        obtain ⟨U, hU, hU'⟩ := hlocFull x
        exact ⟨U, hU, fun a b γ hab hγ hmap hfin => by
          simpa only [ENNReal.ofReal_eq_coe_nnreal hL] using hU' a b γ hab hγ hmap hfin⟩
    have h := rfs_local_to_global_length_of_ne_top gs hc
      ((Kc c).rfs_whole_parent_map) (NNReal.mk (ell s) hL) hlocCoe hfin
    rwa [ENNReal.ofReal_eq_coe_nnreal hL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_local_length_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_local_length_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_local_length_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_local_length_comparison


theorem rfs_child_comparison_maps_of_inputs
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
      ∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map :=
  ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => ⟨Kc c, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_maps_of_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_maps_of_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_maps_of_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_maps_of_inputs

theorem rfs_child_comparison_length_of_inputs
    (f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier))
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hf : ∀ c, f c = (Kc c).rfs_whole_parent_map)
    (s₀ : ℝ) (hs₀ : s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) (ell : ℝ → ℝ)
    (hell : ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hlen : ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
      riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        ((Kc c).rfs_whole_parent_map x) ((Kc c).rfs_whole_parent_map y) ≤
      ENNReal.ofReal (ell s) * riemannianEDistOf
        ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y) :
    ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤
        ENNReal.ofReal (ell s) * riemannianEDistOf
          ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  ⟨s₀, hs₀, ell, hell, htend, fun c s hs x y => by
    rw [hf c]
    exact hlen c s hs x y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_length_of_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_length_of_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_length_of_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_length_of_inputs

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
