import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardHomotheticRicci
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

private instance normalizedRoundSphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSphere4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSphere4 target :: scope.openDecls } }

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance normalizedRoundTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundTopology
local instance normalizedRoundCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundCharted
local instance normalizedRoundSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSmooth
local instance normalizedRoundC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundC1
local instance normalizedRoundT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundT2
local instance normalizedRoundSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedRoundSigma


theorem round_of_curvatureNormalizedFlow_round
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ≤ 0) (p : F.M)
    (hround : IsShrinkingSphericalSpaceFormFlow
      (curvatureNormalizedFlow F rfl rfl t0 Q hQ ht0 p)) :
    IsShrinkingSphericalSpaceFormFlow F := by
  obtain ⟨T, hT, D, e, hmetric⟩ := hround
  have hsurj : Function.Surjective D.proj := by
    intro y
    exact ⟨_, (D.sectionAt y).proj_localSection
      ⟨y, (D.sectionAt y).mem_baseNeighborhood⟩⟩
  let _ : CompactSpace D.Q := hsurj.compactSpace D.proj_smooth.continuous
  have hcompact : CompactSpace F.M := e.symm.surjective.compactSpace e.symm.continuous
  let g : SmoothRiemannianMetric I F.M := Diffeomorph.pullbackMetricCross D.gQuot e
  let Tpast : ℝ := T / Q + t0
  have hTpast : t0 < Tpast := by
    have hpos := div_pos hT hQ
    dsimp only [Tpast]
    linarith
  have hpast (t : ℝ) (ht : t ≤ t0) : F.S.family.metric t =
      scaleMetric (4 * (Tpast - t))
        (mul_pos (by norm_num) (sub_pos.mpr (ht.trans_lt hTpast))) g := by
    have hs : Q * (t - t0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr ht)
    have htime : parabolicTime t0 Q (Q * (t - t0)) = t := by
      unfold parabolicTime
      field_simp [hQ.ne']
      ring
    have h := hmetric (Q * (t - t0)) hs
    change scaleMetric Q hQ (F.S.family.metric (parabolicTime t0 Q (Q * (t - t0)))) =
      scaleMetric (4 * (T - Q * (t - t0)))
        (mul_pos (by norm_num) (sub_pos.mpr (hs.trans_lt hT))) g at h
    rw [htime] at h
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hv := congrArg (fun gm : SmoothRiemannianMetric I F.M => gm.inner x v w) h
    simp only [scaleMetric_inner] at hv ⊢
    apply mul_left_cancel₀ hQ.ne'
    rw [hv]
    dsimp only [Tpast]
    field_simp [hQ.ne']
    ring
  exact ancient_sphericalSpaceFormFlow_of_backward_homothety F hdim hconn hcompact
    g ht0 hTpast hpast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.round_of_curvatureNormalizedFlow_round then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.round_of_curvatureNormalizedFlow_round"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.round_of_curvatureNormalizedFlow_round ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.round_of_curvatureNormalizedFlow_round

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
