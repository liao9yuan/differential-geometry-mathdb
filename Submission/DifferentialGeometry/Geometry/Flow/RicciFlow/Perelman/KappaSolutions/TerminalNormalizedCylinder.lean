import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderSmoothModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedLine
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.CylinderExclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance terminalCylinderSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSphereDimension target :: scope.openDecls } }

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalCylinderSourceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceTopology
local instance terminalCylinderSourceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceCharted
local instance terminalCylinderSourceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderSourceSmooth
local instance terminalCylinderLimitTopology : TopologicalSpace G.M := G.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitTopology
local instance terminalCylinderLimitCharted : ChartedSpace H G.M := G.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitCharted
local instance terminalCylinderLimitSmooth : IsManifold I ∞ G.M := G.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitSmooth
local instance terminalCylinderLimitT2 : T2Space G.M := G.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCylinderLimitT2

theorem exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit
    {kappa : ℝ} (hK : KLim kappa F) (hG : IsAncientKappaSolution (I := I) kappa G)
    (hdim : Module.finrank ℝ E = 3)
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : _root_.Filter.Tendsto
      (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
      _root_.Filter.atTop _root_.Filter.atTop)
    (hscaled : _root_.Filter.Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) _root_.Filter.atTop _root_.Filter.atTop)
    {psi : ℕ → ℕ} (hpsi : StrictMono psi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) (G.atTime 0) psi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k =
      CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k)
    (hEuclidean : Nonempty (F.M ≃ₘ⟮I, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3))) :
    ∃ T : ℝ, 0 < T ∧ ∃ d : Cylinder ≃ₘ⟮CylinderI, I⟯ G.M,
      ∀ t : ℝ, t ≤ 0 → ∀ (y : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
        (G.S.family.metric t).inner (d (y, s))
            (mfderiv CylinderI I d (y, s) (v, a))
            (mfderiv CylinderI I d (y, s) (w, b)) =
          (2 * (T - t)) * (sphereMetric).inner y v w + a * b := by
  have hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    rfl
  obtain ⟨v, w, hplane, hnull⟩ :=
    exists_null_plane_of_terminalCurvatureNormalizedFlowSeq_limit
      F hK (by omega : 2 ≤ Module.finrank ℝ E) p x hQ hescape hscaled hpsi Phi C
      hcanonical hreference (hG.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
      hG.connected G.basepoint
  have hnull' : G.S.base.rm04 0 G.basepoint (vec4 (I := I) v w w v) = 0 := by
    change metricRm04StandardAt (I := I) (G.S.base.metric 0) G.basepoint v w w v = 0 at hnull
    exact hnull
  obtain ⟨T, hT, pi, _, _, hmetric, hcases⟩ :=
    ancientKappa_null_plane_cylinder_smooth_models G hG hdim 0 le_rfl G.basepoint v w
      hplane hnull'
  obtain ⟨eSource⟩ := hEuclidean
  have hexclude := pointedLimit_not_nontrivialCylinderQuotient_diffeomorph
    Phi (fun _ => eSource)
  rcases hcases with ⟨d, hd⟩ | ⟨d, _⟩ | ⟨d, _⟩
  · refine ⟨T, hT, d, ?_⟩
    have hfun : (d : Cylinder → G.M) = pi := funext hd
    rw [hfun]
    exact hmetric
  · exact False.elim (hexclude.1 ⟨d⟩)
  · exact False.elim (hexclude.2 ⟨d⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
