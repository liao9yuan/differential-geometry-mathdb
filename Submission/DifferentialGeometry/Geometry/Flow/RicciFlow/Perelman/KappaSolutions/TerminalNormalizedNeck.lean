import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckDetection
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckScaling

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

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (G : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalNeckSourceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceTopology target :: scope.openDecls } }
private local instance terminalNeckSourceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceCharted target :: scope.openDecls } }
private local instance terminalNeckSourceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceSmooth target :: scope.openDecls } }
private local instance terminalNeckSourceT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceT2 target :: scope.openDecls } }
private local instance terminalNeckSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckSourceSigma target :: scope.openDecls } }
private local instance terminalNeckLimitTopology : TopologicalSpace G.M := G.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitTopology target :: scope.openDecls } }
private local instance terminalNeckLimitCharted : ChartedSpace H G.M := G.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitCharted target :: scope.openDecls } }
private local instance terminalNeckLimitSmooth : IsManifold I ∞ G.M := G.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitSmooth target :: scope.openDecls } }
private local instance terminalNeckLimitT2 : T2Space G.M := G.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitT2 target :: scope.openDecls } }
private local instance terminalNeckLimitSigma : SigmaCompactSpace G.M := G.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalNeckLimitSigma target :: scope.openDecls } }

theorem terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness
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
    ∃ (yStar : SpatialNeckSphere)
      (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ G.M),
      e (yStar, 0) = G.basepoint ∧
      Diffeomorph.pullbackMetricCross (G.S.family.metric 0) e = doubleSphereCylinderMetric ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ W : SpatialNeckWitness (F.S.base.metric 0) yStar (x (psi k)) epsilon,
          ∀ z : spatialNeckBuffer epsilon,
            W.embedding z = Phi.map k
              (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
                (z : SpatialNeckCylinder))) := by
  obtain ⟨T, hT, d, hproduct⟩ :=
    exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit
      F G hK hG hdim p x hQ hescape hscaled hpsi Phi C hcanonical hEuclidean
  have hscalar :=
    terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one F hK x hQ Phi C hcanonical
  change metricScalarAt (I := I) (G.S.family.metric 0) G.basepoint = 1 at hscalar
  obtain ⟨yStar, e, hmarked, hmetric, _⟩ := exists_marked_normalized_cylinder
    G.S.family.metric T hT d hproduct G.basepoint hscalar
  refine ⟨yStar, e, hmarked, hmetric, ?_⟩
  intro epsilon hepsilon
  obtain ⟨k0, hk0⟩ := pointedCylinderLimit_eventually_spatialNeckWitness
    Phi C hcanonical hdim
    (fun k => (terminalCurvatureNormalizedFlowSeq_complete F hK x hQ).complete_on
      k 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)
    yStar e hmarked hmetric epsilon hepsilon
  refine ⟨k0, fun k hk => ?_⟩
  have hscaledWitness :
      ∃ W : SpatialNeckWitness
          (scaleMetric (F.S.scalar 0 (x (psi k))) (hQ (psi k)) (F.S.base.metric 0))
          yStar (x (psi k)) epsilon,
        ∀ z : spatialNeckBuffer epsilon,
          W.embedding z = Phi.map k
            (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
              (z : SpatialNeckCylinder))) := by
    rw [← terminalCurvatureNormalizedFlowSeq_metric F hK x hQ (psi k)]
    exact hk0 k hk
  obtain ⟨W, hW⟩ := hscaledWitness
  exact ⟨W.ofScaleMetric (F.S.scalar 0 (x (psi k))) (hQ (psi k)), hW⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
