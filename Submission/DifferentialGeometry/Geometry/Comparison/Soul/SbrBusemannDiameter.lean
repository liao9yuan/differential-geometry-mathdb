import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannGlobal
import Mathlib.Topology.MetricSpace.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

theorem busemann_level_ediam_lt_top {X : Type*} [MetricSpace X]
    (c : ℝ≥0 → X) (hproper : IsProperMap (busemann c)) (a : ℝ) :
    Metric.ediam {x : X | busemann c x = a} < ⊤ :=
  lt_top_iff_ne_top.mpr (isCompact_busemann_level_of_proper c hproper a).isBounded.ediam_ne_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.busemann_level_ediam_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.busemann_level_ediam_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.busemann_level_ediam_lt_top ``Submission.DifferentialGeometry.Geometry.Topology.busemann_level_ediam_lt_top

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
    tensor04SectionalNonnegativeCone (I := I) (M := M))
  {c : ℝ≥0 → M} (hc : Isometry c)

include g hEnorm hsec hc

theorem busemann_level_diameter_le_of_compact_sublevel
    {a d : ℝ} (had : a < d) (hne : ({x : M | busemann c x = a}).Nonempty)
    (hC : IsCompact {x : M | busemann c x ≤ d}) :
    IsCompact {x : M | busemann c x = a} ∧
      IsCompact {x : M | busemann c x = d} ∧
      Metric.diam {x : M | busemann c x = a} ≤ Metric.diam {x : M | busemann c x = d} := by
  have hb : Continuous (busemann c) := (lipschitzWith_busemann hc).continuous
  have hCa : IsCompact {x : M | busemann c x = a} :=
    hC.of_isClosed_subset (isClosed_eq hb continuous_const) (fun _ hx => hx.le.trans had.le)
  have hCd : IsCompact {x : M | busemann c x = d} :=
    hC.of_isClosed_subset (isClosed_eq hb continuous_const) (fun _ hx => hx.le)
  refine ⟨hCa, hCd, ?_⟩
  obtain ⟨R, himage, hlip⟩ :=
    exists_surjective_nonexpanding_busemann_level_map g hEnorm hsec hc had hne hC
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  intro x hx y hy
  have hx' : x ∈ R '' {z : M | busemann c z = d} := by rw [himage]; exact hx
  have hy' : y ∈ R '' {z : M | busemann c z = d} := by rw [himage]; exact hy
  obtain ⟨p, hp, rfl⟩ := hx'
  obtain ⟨q, hq, rfl⟩ := hy'
  have hd : _root_.Dist.dist (R p) (R q) ≤ _root_.Dist.dist p q := by
    simpa only [NNReal.coe_one, one_mul] using hlip.dist_le_mul p hp q hq
  exact hd.trans (Metric.dist_le_diam_of_mem hCd.isBounded hp hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le_of_compact_sublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le_of_compact_sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le_of_compact_sublevel ``Submission.DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le_of_compact_sublevel

variable (hproper : IsProperMap (busemann c)) (hbelow : BddBelow (range (busemann c)))

include hproper hbelow

theorem busemann_level_diameter_le {a d : ℝ}
    (ha : (⨅ z : M, busemann c z) ≤ a) (had : a ≤ d) :
    Metric.diam {x : M | busemann c x = a} ≤ Metric.diam {x : M | busemann c x = d} := by
  have hπ := lipschitzWith_busemannLevelMap g hEnorm hsec hc hproper hbelow ha had
  have hsurj := surjective_busemannLevelMap g hEnorm hsec hc hproper hbelow ha had
  have hCd := isCompact_busemann_level_of_proper c hproper d
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  intro x hx y hy
  obtain ⟨p, hp⟩ := hsurj ⟨x, hx⟩
  obtain ⟨q, hq⟩ := hsurj ⟨y, hy⟩
  have hd : _root_.Dist.dist x y ≤ _root_.Dist.dist p.1 q.1 := by
    simpa only [hp, hq, NNReal.coe_one, one_mul, Subtype.dist_eq] using hπ.dist_le_mul p q
  exact hd.trans (Metric.dist_le_diam_of_mem hCd.isBounded p.2 q.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le ``Submission.DifferentialGeometry.Geometry.Topology.busemann_level_diameter_le

theorem monotoneOn_busemann_level_diameter :
    MonotoneOn (fun a : ℝ => Metric.diam {x : M | busemann c x = a})
      (_root_.Set.Ici (⨅ z : M, busemann c z)) := by
  intro a ha d _hd had
  exact busemann_level_diameter_le g hEnorm hsec hc hproper hbelow ha had

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.monotoneOn_busemann_level_diameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.monotoneOn_busemann_level_diameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.monotoneOn_busemann_level_diameter ``Submission.DifferentialGeometry.Geometry.Topology.monotoneOn_busemann_level_diameter

end DifferentialGeometry.Geometry.Topology

end
