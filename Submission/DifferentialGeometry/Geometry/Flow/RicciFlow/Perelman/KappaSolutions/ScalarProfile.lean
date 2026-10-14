import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.ScalarCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance scalarProfileTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileTopology
local instance scalarProfileCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileCharted
local instance scalarProfileSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSmooth
local instance scalarProfileC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileC1
local instance scalarProfileT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileT2
local instance scalarProfileSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarProfileSigma

theorem scalar_profile_eq_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : F.M,
      F.S.scalar t x = 3 / (2 * (T - t)) := by
  obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
  refine ⟨T, hT, ?_⟩
  intro t ht x
  have hscale : 0 < 4 * (T - t) := by nlinarith
  have hm : F.S.base.metric t = scaleMetric (4 * (T - t)) hscale
      (Diffeomorph.pullbackMetricCross Dq.gQuot e) := hmetric t ht
  change metricScalarAt (I := I) (F.S.base.metric t) x = _
  rw [hm, metricScalarAt_scaleMetric, metricScalar_cross, Dq.gQuot_scalar]
  norm_num
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_eq_of_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_eq_of_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_eq_of_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_eq_of_shrinking_spherical_space_form_flow

theorem scalar_eq_of_normalized_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    (hbase : PointedFlowScalarAtBase (I := I) F 1)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    F.S.scalar t x = 1 / (1 - (2 / 3 : ℝ) * t) := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  have hnorm := hscalar 0 le_rfl F.basepoint
  change F.S.scalar 0 F.basepoint = 1 at hbase
  rw [hbase, sub_zero] at hnorm
  have hmul : 1 * (2 * T) = (3 : ℝ) :=
    (eq_div_iff (by positivity : 2 * T ≠ 0)).mp hnorm
  have hTnorm : T = 3 / 2 := by linarith
  rw [hscalar t ht x, hTnorm]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_eq_of_normalized_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_eq_of_normalized_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_eq_of_normalized_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_eq_of_normalized_shrinking_spherical_space_form_flow

theorem scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    HasDerivWithinAt (fun s => F.S.scalar s x)
      ((2 / 3 : ℝ) * F.S.scalar t x ^ 2) (_root_.Set.Iic t) t := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  have hne : 2 * (T - t) ≠ 0 := by nlinarith
  have hden : HasDerivAt (fun s : ℝ => 2 * (T - s)) (-2) t := by
    convert! ((hasDerivAt_id t).const_sub T).const_mul 2 using 1
    norm_num
  have hd := (hasDerivAt_const t (3 : ℝ)).div hden hne
  have hd' : HasDerivAt (fun s : ℝ => 3 / (2 * (T - s)))
      ((2 / 3 : ℝ) * F.S.scalar t x ^ 2) t := by
    apply hd.congr_deriv
    rw [hscalar t ht x]
    field_simp
    ring
  exact hd'.hasDerivWithinAt.congr (fun s hs => hscalar s (hs.trans ht) x) (hscalar t ht x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow

theorem abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    |derivWithin (fun s => F.S.scalar s x) (_root_.Set.Iic t) t| =
      (2 / 3 : ℝ) * F.S.scalar t x ^ 2 := by
  rw [(scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow F hround ht x).derivWithin
    (uniqueDiffWithinAt_Iic t), abs_of_nonneg (by positivity)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.abs_scalar_derivWithin_of_shrinking_spherical_space_form_flow

theorem scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F)
    (hbase : PointedFlowScalarAtBase (I := I) F 1) (x : F.M) :
    derivWithin (fun s => F.S.scalar s x) (_root_.Set.Iic 0) 0 = 2 / 3 := by
  rw [(scalar_hasDerivWithinAt_of_shrinking_spherical_space_form_flow F hround le_rfl
    x).derivWithin (uniqueDiffWithinAt_Iic 0),
    scalar_eq_of_normalized_shrinking_spherical_space_form_flow F hround hbase le_rfl x]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow

theorem scalar_profile_of_shrinking_spherical_space_form_flow
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I) F) :
    ∀ t : ℝ, t ≤ 0 → ∃ R : ℝ, 0 < R ∧ ∀ x : F.M, F.S.scalar t x = R := by
  obtain ⟨T, hT, hscalar⟩ := scalar_profile_eq_of_shrinking_spherical_space_form_flow F hround
  intro t ht
  refine ⟨3 / (2 * (T - t)), ?_, hscalar t ht⟩
  have hpos : 0 < T - t := by linarith
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_of_shrinking_spherical_space_form_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_of_shrinking_spherical_space_form_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_of_shrinking_spherical_space_form_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_profile_of_shrinking_spherical_space_form_flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
