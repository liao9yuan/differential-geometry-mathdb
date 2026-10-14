import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardFlow
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.RoundMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

private instance roundSpaceForm_sphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceForm_sphere4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceForm_sphere4 target :: scope.openDecls } }

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance roundSpaceFormTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormTopology
local instance roundSpaceFormCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormCharted
local instance roundSpaceFormSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSmooth
local instance roundSpaceFormC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormC1
local instance roundSpaceFormT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormT2
local instance roundSpaceFormSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormSigma


def IsShrinkingSphericalSpaceFormFlow : Prop :=
  ∃ (T : ℝ) (hT : 0 < T),
    ∃ D : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3,
      ∃ e : F.M ≃ₘ⟮I, 𝓡 3⟯ D.Q,
        ∀ (t : ℝ) (ht : t ≤ 0), F.S.family.metric t =
          scaleMetric (4 * (T - t)) (mul_pos (by norm_num) (by linarith))
            (Diffeomorph.pullbackMetricCross D.gQuot e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsShrinkingSphericalSpaceFormFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsShrinkingSphericalSpaceFormFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsShrinkingSphericalSpaceFormFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsShrinkingSphericalSpaceFormFlow

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance roundSpaceFormLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitTopology
local instance roundSpaceFormLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitCharted
local instance roundSpaceFormLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSmooth
local instance roundSpaceFormLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitC1
local instance roundSpaceFormLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitT2
local instance roundSpaceFormLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSpaceFormLimitSigma


theorem ancient_sphericalSpaceFormFlow_of_round_backward_convergence
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    let T := 3 / (2 * F.S.scalar 0 F.basepoint)
    ∃ hT : 0 < T, ∃ D : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3,
      ∃ e : F.M ≃ₘ⟮I, 𝓡 3⟯ D.Q,
        ∀ (t : ℝ) (ht : t ≤ 0), F.S.family.metric t =
          scaleMetric (4 * (T - t)) (mul_pos (by norm_num) (by linarith))
            (Diffeomorph.pullbackMetricCross D.gQuot e) := by
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology := fun _ => hconn
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompact hconnected
  obtain ⟨_hsource, _htarget, _e, _hmap, _hinv, _hpoint, hcompactF⟩ := hk0 k0 le_rfl
  obtain ⟨hT, _hprofile, hmetric, hsection⟩ :=
    ancient_roundScaling_of_round_backward_convergence F hdim hconn hcompactF
      tau htau hescape q hphi Phi C hcanonical hcompact hR hscalar hEin
  let T := 3 / (2 * F.S.scalar 0 F.basepoint)
  let c := 1 / (4 * T)
  have hc : 0 < c := one_div_pos.mpr (mul_pos (by norm_num) hT)
  have hsec : ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric 0) x X Y Y X = c *
        ((F.S.family.metric 0).inner x X X * (F.S.family.metric 0).inner x Y Y -
          (F.S.family.metric 0).inner x X Y * (F.S.family.metric 0).inner x X Y) := by
    simpa only [sub_zero] using hsection 0 le_rfl
  obtain ⟨D, e, hQ⟩ := exists_roundSphereQuotient_metric hcompactF hconn
    (inferInstance : I.Boundaryless) hdim (F.S.family.metric 0) c hc hsec
  refine ⟨hT, D, e, fun t ht => ?_⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [hmetric t ht, scaleMetric_inner, scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner]
  rw [hQ x v w]
  change ((T - t) / T) * (F.S.family.metric 0).inner x v w =
    (4 * (T - t)) * (c * (F.S.family.metric 0).inner x v w)
  dsimp only [c]
  simp only [div_mul_eq_div_div]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_round_backward_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_round_backward_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_round_backward_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_sphericalSpaceFormFlow_of_round_backward_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
