import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrderedSides
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBandBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompleteMetricUnitArm
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonTriangleLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

private theorem marked_ne_outward (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    {x : N} (hx : x ∈ D.upper (5 * Real.pi)) : p ≠ x := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hp := D.marked_mem_lower (5 * Real.pi) hs (by positivity)
  have hdisjoint := (D.slice_spec (5 * Real.pi) hs).2.2.2.2.1
  intro hpx
  have hxlower : x ∈ D.lower (5 * Real.pi) :=
    (congrArg (fun z : N => z ∈ D.lower (5 * Real.pi)) hpx).mp hp
  exact Set.disjoint_left.mp hdisjoint hxlower hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_ne_outward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_ne_outward target :: scope.openDecls } }

section CompatibleMetric

variable [I.Boundaryless] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance outwardAngleC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outwardAngleC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outwardAngleC1 target :: scope.openDecls } }

theorem outward_comparisonAngle_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {x y : N} (hx : x ∈ D.upper (5 * Real.pi)) (hy : y ∈ D.upper (5 * Real.pi)) :
    comparisonAngle (_root_.Dist.dist p x) (_root_.Dist.dist p y) (_root_.Dist.dist x y) ≤ Real.pi / 6 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W.dimension_three]; norm_num⟩
  let _ : CompleteSpace N := completeMetric_compatible_completeSpace h hEnorm W.complete
  have hgap := spatialNeckControlEpsilon_inverse_gap W.epsilon_pos hsmall
  have hs : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hp := D.marked_mem_lower (5 * Real.pi) hs (by positivity)
  have hpavoid : p ∉ W.embedding '' {z : spatialNeckBuffer epsilon | z.val.2 = 5 * Real.pi} := by
    change p ∈ (W.embedding '' {z : spatialNeckBuffer epsilon | z.val.2 = 5 * Real.pi})ᶜ
    rw [← (D.slice_spec (5 * Real.pi) hs).2.2.2.2.2.1]
    exact Or.inl hp
  obtain ⟨u, hu, huend, hurad⟩ := completeMetric_exists_unit_arm h hEnorm p x
    (D.marked_ne_outward hsmall hx)
  obtain ⟨v, hv, hvend, hvrad⟩ := completeMetric_exists_unit_arm h hEnorm p y
    (D.marked_ne_outward hsmall hy)
  have hu0 : intrinsicGeodesic (I := I) h hEnorm p u 0 ∈ D.lower (5 * Real.pi) := by
    rw [intrinsicGeodesic_zero]
    exact hp
  have hv0 : intrinsicGeodesic (I := I) h hEnorm p v 0 ∈ D.lower (5 * Real.pi) := by
    rw [intrinsicGeodesic_zero]
    exact hp
  have huX : intrinsicGeodesic (I := I) h hEnorm p u (_root_.Dist.dist p x) ∈ D.upper (5 * Real.pi) := by
    rw [huend]
    exact hx
  have hvY : intrinsicGeodesic (I := I) h hEnorm p v (_root_.Dist.dist p y) ∈ D.upper (5 * Real.pi) := by
    rw [hvend]
    exact hy
  obtain ⟨a, ha, hsa⟩ := D.continuous_curve_crosses_slice (5 * Real.pi) hs dist_nonneg
    (intrinsicGeodesic_continuous (I := I) h hEnorm p u).continuousOn hu0 huX
  obtain ⟨b, hb, hsb⟩ := D.continuous_curve_crosses_slice (5 * Real.pi) hs dist_nonneg
    (intrinsicGeodesic_continuous (I := I) h hEnorm p v).continuousOn hv0 hvY
  have hapos : 0 < a := by
    by_contra! hn
    have ha0 : a = 0 := le_antisymm hn ha.1
    apply hpavoid
    simpa only [ha0, intrinsicGeodesic_zero] using hsa
  have hbpos : 0 < b := by
    by_contra! hn
    have hb0 : b = 0 := le_antisymm hn hb.1
    apply hpavoid
    simpa only [hb0, intrinsicGeodesic_zero] using hsb
  obtain ⟨za, hza, heqa⟩ := hsa
  obtain ⟨zb, hzb, heqb⟩ := hsb
  have hangle := W.outward_slice_comparisonAngle_lt hsmall za zb hza hzb
  simp only [riemannianEDistOf_eq_riemannianEDist h hEnorm, heqa, heqb,
    hurad a ha, hvrad b hb] at hangle
  have hshort := complete_comparisonAngle_shortening h hEnorm hsec p u v
    a (_root_.Dist.dist p x) b (_root_.Dist.dist p y) hapos ha.2 hbpos hb.2 hu hv
    (hurad (_root_.Dist.dist p x) ⟨dist_nonneg, le_rfl⟩)
    (hvrad (_root_.Dist.dist p y) ⟨dist_nonneg, le_rfl⟩)
  have hfull := hshort.trans hangle.le
  simpa only [huend, hvend, ← IsRiemannianManifold.out (I := I), ← dist_edist] using hfull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_comparisonAngle_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_comparisonAngle_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_comparisonAngle_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_comparisonAngle_le

theorem outward_distance_loss (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    {x y : N} (hx : x ∈ D.upper (5 * Real.pi)) (hy : y ∈ D.upper (5 * Real.pi))
    (hlarge : 2 * _root_.Dist.dist p y ≤ _root_.Dist.dist p x) : _root_.Dist.dist x y ≤ _root_.Dist.dist p x - _root_.Dist.dist p y / 4 := by
  have hangle := D.outward_comparisonAngle_le hEnorm hsmall hsec hx hy
  have hlower : |_root_.Dist.dist p x - _root_.Dist.dist p y| ≤ _root_.Dist.dist x y := by
    simpa only [dist_comm x p, dist_comm y p] using abs_dist_sub_le x y p
  have hupper : _root_.Dist.dist x y ≤ _root_.Dist.dist p x + _root_.Dist.dist p y := by
    simpa only [dist_comm x p] using dist_triangle x p y
  apply comparisonAngle_linear_side_loss
    (dist_pos.mpr (D.marked_ne_outward hsmall hx))
    (dist_pos.mpr (D.marked_ne_outward hsmall hy)) hlower hupper _ hlarge
  linarith [Real.pi_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_distance_loss then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_distance_loss"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_distance_loss ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.outward_distance_loss

end CompatibleMetric

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
