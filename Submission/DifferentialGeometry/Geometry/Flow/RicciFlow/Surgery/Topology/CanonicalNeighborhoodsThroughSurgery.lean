import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SingularEventExtinction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

def CanonicalNeighborhoodsThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε < 1 / 11 →
  ∃ (C1 C2 qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime : ℝ≥0),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) ∧
        ∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgery ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgery

def UniformDebitSurgeryStep (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B : ℝ), 0 < B →
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 11 ∧
  ∀ (C1 C2 qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime : ℝ≥0),
    1 ≤ C1 → 1 ≤ C2 → 0 < qcan → 0 < τmin → 0 < δmax → 0 < ρmax → 0 < εcap → 0 < Dcap →
  ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
    p₀.modelAccuracy ≤ εcap ∧ Dcap ≤ p₀.modelRadius ∧ mcap ≤ p₀.modelOrder ∧
    0 < δbound ∧ δbound ≤ δmax ∧ 0 < ρbound ∧ ρbound ≤ ρmax ∧ 0 < v ∧
    ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
      H.hasCanonicalCutoffRecords p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) (t : ℝ),
        t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ) →
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        G.SingularEndpoint →
        (∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t y →
          |derivWithin (fun v => G.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            Ctime * G.flow.scalar t y ^ 2) →
        (∀ (x : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
          t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) s → qcan < G.flow.scalar t x →
          τmin ≤ G.flow.scalar t x * (t - H.time (Fin.last H.eventCount)) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
          (q : CutoffParameters),
          E.incoming = G ∧
          (H.appendEvent E.incoming.lt E hinit).hasCanonicalCutoffRecords p₀ δbound ρbound ∧
          q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
          q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
          q.recenterConstant = p₀.recenterConstant ∧
          Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
            (Fin.last H.eventCount) q) ∧
          E.transition.boundaryFrameReversing ∧
          E.toMetricCutCapEvent.poincareStandardDiscarded ∧
          ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric _root_.Set.univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.UniformDebitSurgeryStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.UniformDebitSurgeryStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.UniformDebitSurgeryStep ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.UniformDebitSurgeryStep

theorem exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric)
    (hstep : UniformDebitSurgeryStep P₀ g₀) (hcn : CanonicalNeighborhoodsThroughSurgery P₀ g₀) :
    Nonempty (PoincareControlledExtinction P₀.toClosedOrientedManifold g₀) := by
  apply exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants P₀ g₀
  intro B hB
  obtain ⟨ε, hε, hε', hstepB⟩ := hstep B hB
  obtain ⟨C1, C2, qcan, τmin, δmax, ρmax, εcap, Dcap, mcap, Ctime, hC1, hC2, hqcan, hτ, hδmax,
    hρmax, hεcap, hDcap, hclass⟩ := hcn B ε hB hε hε'
  obtain ⟨p₀, δbound, ρbound, v, hacc, hD, hm, -, hδle, -, hρle, hv, hnext⟩ :=
    hstepB C1 C2 qcan τmin δmax ρmax εcap Dcap mcap Ctime hC1 hC2 hqcan hτ hδmax hρmax hεcap hDcap
  refine ⟨p₀, v, fun H => H.hasCanonicalCutoffRecords p₀ δbound ρbound, hv,
    RetainedCoreHistory.hasCanonicalCutoffRecords_atZero P₀ g₀ p₀ δbound ρbound, ?_⟩
  intro H initial hInv p htime hhor hpf hpD hpm hpε hpc _ _ _ _ s G hs hinit hsing
  obtain ⟨hderiv, hslab⟩ :=
    hclass p₀ δbound ρbound hacc hD hm hδle hρle H initial htime hhor hInv
  obtain ⟨hderivG, hcnG⟩ := hslab s G hs hinit hsing
  obtain ⟨Q, E, hinitE, q, hEG, hInvK, hqf, hqD, hqm, hqε, hqc, hrec, hbfr, hctrl, hdebit⟩ :=
    hnext H initial htime hhor hInv hderiv s G hs hinit hsing hderivG hcnG
  exact ⟨Q, E, hinitE, q, hEG, hInvK, hqf.trans hpf.symm, hqD.trans hpD.symm,
    hqm.trans hpm.symm, hqε.trans hpε.symm, hqc.trans hpc.symm, hrec, hbfr, hctrl, hdebit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods

theorem hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    (hstep : ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric), UniformDebitSurgeryStep P₀ g₀)
    (hcn : ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
      CanonicalNeighborhoodsThroughSurgery P₀ g₀) :
    ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier] (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) := by
  intro M hsc g
  have : SimplyConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := inferInstanceAs (SimplyConnectedSpace M.Carrier)
  exact exists_poincare_controlled_extinction_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g
    (hstep (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hcn (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods

theorem smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods
    (hstep : ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric), UniformDebitSurgeryStep P₀ g₀)
    (hcn : ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
      CanonicalNeighborhoodsThroughSurgery P₀ g₀) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_controlledExtinction
    (hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods hstep hcn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
