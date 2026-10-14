import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckAmbientDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedNeckNumerics
import Mathlib.Topology.EMetricSpace.Diam

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance bandBoundsSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bandBoundsSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bandBoundsSphereDimension target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance bandBoundsC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bandBoundsC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bandBoundsC1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

private theorem band_point_mem_core (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : |x.val.2| ≤ 5 * Real.pi) :
    x ∈ spatialNeckClosedCore epsilon := by
  have hgap := spatialNeckControlEpsilon_inverse_gap hepsilon hsmall
  have hbounds := abs_le.mp hx
  change -epsilon⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ epsilon⁻¹
  constructor <;> linarith [Real.pi_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_point_mem_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_point_mem_core target :: scope.openDecls } }

theorem marked_antipodal_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (z : spatialNeckBuffer epsilon) (hz : |z.val.2| ≤ 5 * Real.pi)
    (hanti : z.val.1 = -yStar) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
      riemannianEDistOf (I := I) h p (W.embedding z) := by
  let c := spatialNeckCentralPoint epsilon W.epsilon_pos yStar
  have hc : |c.val.2| ≤ 5 * Real.pi := by
    change |(0 : ℝ)| ≤ 5 * Real.pi
    rw [abs_zero]
    positivity
  have hlower := W.band_antipodal_edist_lower hsmall c z hc hz hanti
  change ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
    riemannianEDistOf (I := I) h
      (W.embedding (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)) (W.embedding z) at hlower
  rwa [W.marked] at hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_antipodal_edist_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_antipodal_edist_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_antipodal_edist_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_antipodal_edist_lower

theorem outward_slice_comparisonAngle_lt (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x.val.2 = 5 * Real.pi) (hy : y.val.2 = 5 * Real.pi) :
    comparisonAngle
      (riemannianEDistOf (I := I) h p (W.embedding x)).toReal
      (riemannianEDistOf (I := I) h p (W.embedding y)).toReal
      (riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y)).toReal < Real.pi / 6 := by
  let c := spatialNeckCentralPoint epsilon W.epsilon_pos yStar
  have hc : |c.val.2| ≤ 5 * Real.pi := by
    change |(0 : ℝ)| ≤ 5 * Real.pi
    rw [abs_zero]
    positivity
  have hxb : |x.val.2| ≤ 5 * Real.pi := by rw [hx, abs_of_pos (by positivity)]
  have hyb : |y.val.2| ≤ 5 * Real.pi := by rw [hy, abs_of_pos (by positivity)]
  have hcmark : W.embedding c = p := W.marked
  have hlower (z : spatialNeckBuffer epsilon) (hz : z.val.2 = 5 * Real.pi)
      (hzb : |z.val.2| ≤ 5 * Real.pi) :
      (11 / 12 : ℝ) * (5 * Real.pi) * spatialNeckScale h p ≤
        (riemannianEDistOf (I := I) h p (W.embedding z)).toReal := by
    have hedist := W.band_axial_edist_lower hsmall c z hc hzb
    have hfin : riemannianEDistOf (I := I) h (W.embedding c) (W.embedding z) ≠ ⊤ :=
      ne_of_lt ((W.band_edist_lt hsmall c z hc hzb).trans_le le_top)
    have hr := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hedist
    change 11 / 12 * spatialNeckScale h p * |z.val.2 - 0| ≤
      (riemannianEDistOf (I := I) h (W.embedding c) (W.embedding z)).toReal at hr
    rw [sub_zero, hz, abs_of_pos (by positivity), hcmark] at hr
    nlinarith
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hpair := W.slice_edist_upper hsmall x y (band_point_mem_core W.epsilon_pos hsmall x hxb)
    (band_point_mem_core W.epsilon_pos hsmall y hyb) (hy.trans hx.symm)
  have hpairReal := ENNReal.toReal_le_of_le_ofReal
    (by positivity : 0 ≤ 13 / 12 * spatialNeckScale h p * Real.pi) hpair
  apply bufferedNeck_comparisonAngle_lt_pi_div_six hscale
    (hlower x hx hxb) (hlower y hy hyb) ENNReal.toReal_nonneg
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.outward_slice_comparisonAngle_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.outward_slice_comparisonAngle_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.outward_slice_comparisonAngle_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.outward_slice_comparisonAngle_lt

section CompatibleMetric

variable [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [PseudoEMetricSpace N] [IsRiemannianManifold I N]

omit [I.Boundaryless] in
theorem band_ediam_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) :
    Metric.ediam (W.embedding '' {x : spatialNeckBuffer epsilon | |x.val.2| ≤ 5 * Real.pi}) ≤
      ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p) := by
  apply Metric.ediam_image_le_iff.mpr
  intro x hx y hy
  rw [IsRiemannianManifold.out (I := I),
    ← riemannianEDistOf_eq_riemannianEDist h hEnorm]
  exact (W.band_edist_lt hsmall x y hx hy).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_ediam_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_ediam_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_ediam_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.band_ediam_le

omit [I.Boundaryless] in
theorem slice_ediam_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) (s : ℝ) (hs : |s| ≤ 5 * Real.pi) :
    Metric.ediam (W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s}) ≤
      ENNReal.ofReal (13 / 12 * spatialNeckScale h p * Real.pi) := by
  apply Metric.ediam_image_le_iff.mpr
  intro x hx y hy
  have hxb : |x.val.2| ≤ 5 * Real.pi := by rw [hx]; exact hs
  have hyb : |y.val.2| ≤ 5 * Real.pi := by rw [hy]; exact hs
  rw [IsRiemannianManifold.out (I := I),
    ← riemannianEDistOf_eq_riemannianEDist h hEnorm]
  exact W.slice_edist_upper hsmall x y (band_point_mem_core W.epsilon_pos hsmall x hxb)
    (band_point_mem_core W.epsilon_pos hsmall y hyb) (hy.trans hx.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_ediam_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_ediam_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_ediam_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.slice_ediam_le

end CompatibleMetric

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
