import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_backwardSurvivorFootprint_curvature_bound
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (K : Set (H.toHistory.event i).incoming.terminalRegularOpen)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.toHistory.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v x) (_root_.Set.Iic t) t| ≤
        C * (H.toHistory.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (_root_.Set.Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hscalar : ∀ x ∈ K, metricScalarAt (H.toHistory.event i).terminal.metric x ≤ 2 * Q)
    {c : ℝ} (hc : c ∈ _root_.Set.Ico (H.time first.castSucc) (H.time first.succ))
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c (H.time i.castSucc) →
      ∀ y ∈ (H.toHistory.event j).capRegion,
        4 * Q ≤ metricScalarAt (H.toHistory.event j).outputMetric y)
    (htime : 6 * C * (H.time i.succ - c) * Q ≤ 1) :
    _root_.Set.range (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K) = interior K ∧
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K),
      (∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.toHistory.backwardSurvivorSlabMetric first.castSucc i.castSucc hle j hf hl t).restrictOpen
            (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle)).restrictOpen
              (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      (∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.toHistory.backwardSurvivorTerminalFaceMetric first.castSucc i hle t).restrictOpen
          (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.toHistory.event i).terminal.metric
        (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K)
        (H.toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc i hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
          (RealTimeInterval.closed c (H.time i.succ)
            (hc.2.le.trans (H.time_strictMono.monotone (by
              change first.val+1 ≤ i.val+1
              exact Nat.succ_le_succ hle))))) ∧
      ∀ t ∈ _root_.Set.Icc c (H.time i.succ), ∀ x : H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)) ^ 2 := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hbudget : C * (H.time i.succ-c) ≤ (2*Q)⁻¹-(4*Q)⁻¹ := by
    have heq : (2*Q)⁻¹-(4*Q)⁻¹ = (4*Q)⁻¹ := by field_simp; ring
    rw [heq,inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 4*Q)).mpr
    nlinarith [C.coe_nonneg]
  have htrace : ∀ x ∈ K,
      Nonempty (BackwardPointTrace H.toHistory first.castSucc i.castSucc hle x.val) := by
    intro x hx
    obtain ⟨A,_⟩ := H.exists_backwardPointTrace_on_time_window i first hle x hq
      (by linarith : q ≤ 2*Q) (by linarith : 2*Q < 4*Q) (hscalar x hx)
      hc hbudget le_rfl hbound hcap
    exact ⟨A⟩
  exact H.toHistory.exists_backwardSurvivorFootprint_curvature_bound first.castSucc i hle K
    hq hqQ hPhi hbound hpinch hscalar htrace hc.1
    (hc.2.le.trans (H.time_strictMono.monotone (by
      change first.val+1 ≤ i.val+1
      exact Nat.succ_le_succ hle))) htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardSurvivorFootprint_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardSurvivorFootprint_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardSurvivorFootprint_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardSurvivorFootprint_curvature_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
