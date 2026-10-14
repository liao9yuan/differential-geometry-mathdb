import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomain : IsManifold ThreeModel 1 (H.backwardSurvivorDomain first i.castSucc hle) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFace : IsManifold ThreeModel 1 (H.backwardSurvivorTerminalFace first i hle) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior (K : Set (H.event i).incoming.terminalRegularOpen) :
    IsManifold ThreeModel 1 (H.backwardSurvivorFootprintInterior first i hle K) :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior target :: scope.openDecls } }

include hle in
private theorem exists_closed_stage_of_mem_Icc
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (H.time first) (H.time i.succ)) :
    ∃ j : Fin H.eventCount, first ≤ j.castSucc ∧ j.castSucc ≤ i.castSucc ∧
      t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ) := by
  by_cases hlast : H.time i.castSucc ≤ t
  · exact ⟨i, hle, le_rfl, hlast, ht.2⟩
  have hti : t < H.time i.castSucc := lt_of_not_ge hlast
  let tH : _root_.Set.Icc (0 : ℝ) H.horizon :=
    ⟨t, (H.time_nonneg first).trans ht.1, ht.2.trans (H.time_le_horizon_at i.succ)⟩
  let k := H.activeStage tH
  have hk : k < i.castSucc := by
    apply H.time_strictMono.lt_iff_lt.mp
    exact (H.activeStage_time_le tH).trans_lt hti
  have hkfirst : first ≤ k := H.le_activeStage tH first ht.1
  let j : Fin H.eventCount := ⟨k.val, by have := i.isLt; change k.val < H.eventCount; omega⟩
  have hj : j.castSucc = k := rfl
  have hn := H.activeStage_before_next tH (show k.val < H.eventCount from j.isLt)
  refine ⟨j, hkfirst, hk.le, H.activeStage_time_le tH, ?_⟩
  exact hn.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_closed_stage_of_mem_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_closed_stage_of_mem_Icc target :: scope.openDecls } }

private theorem rmNorm_footprint_slab
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc)
    (t : ℝ) (x : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S
      (((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) x 4
      (metricRm04At (((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) x)) =
      Real.sqrt (normSq0S ((H.event j).terminal.extendedMetric t)
        (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hl x.val.val) 4
        (metricRm04At ((H.event j).terminal.extendedMetric t)
          (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hl x.val.val))) := by
  rw [rmNormSq_restrictOpen, rmNormSq_restrictOpen]
  change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4 (metricRm04At (localPullMetric _ _ _) _)) = _
  rw [normSq0S_metricRm04At_localPullMetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_slab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_slab target :: scope.openDecls } }

private theorem rmNorm_footprint_last
    (K : Set (H.event i).incoming.terminalRegularOpen) (t : ℝ)
    (x : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S
      ((H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K)) x 4
      (metricRm04At ((H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K)) x)) =
      Real.sqrt (normSq0S ((H.event i).terminal.extendedMetric t)
        (H.backwardSurvivorFootprintMap first i hle K x) 4
        (metricRm04At ((H.event i).terminal.extendedMetric t)
          (H.backwardSurvivorFootprintMap first i hle K x))) := by
  rw [rmNormSq_restrictOpen]
  change Real.sqrt (normSq0S (localPullMetric _ _ _) _ 4 (metricRm04At (localPullMetric _ _ _) _)) = _
  rw [normSq0S_metricRm04At_localPullMetric]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_last
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_last target :: scope.openDecls } }

private theorem rmNorm_footprint_of_closed_stage_bounds
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
        G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
            (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (B c : ℝ)
    (hB : ∀ x ∈ K, ∀ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ y : (H.event j).incoming.terminalRegularOpen, y.val = A.point j.castSucc hf hl →
      ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ), c ≤ t →
        Real.sqrt (normSq0S ((H.event j).terminal.extendedMetric t) y 4
          (metricRm04At ((H.event j).terminal.extendedMetric t) y)) ≤ B)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (H.time first) (H.time i.succ)) (hct : c ≤ t)
    (z : H.backwardSurvivorFootprintInterior first i hle K) :
    Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤ B := by
  let x := H.backwardSurvivorFootprintMap first i hle K z
  have hx : x ∈ K := interior_subset z.property
  let A : BackwardPointTrace H first i.castSucc hle x.val := Classical.choice z.val.val.property
  obtain ⟨j,hf,hl,htj⟩ := exists_closed_stage_of_mem_Icc (hle := hle) ht
  by_cases he : j = i
  · subst j
    rw [hlast t htj, rmNorm_footprint_last]
    exact hB x hx A i hle le_rfl x A.endpoint_eq.symm t htj hct
  · have hjnext : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val ≤ i.val := hl
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    rw [hslabs j hf hjnext t htj, rmNorm_footprint_slab]
    apply hB x hx A j hf hl
      (H.backwardSurvivorTerminalMap first i.castSucc hle j hf hjnext z.val.val)
    · exact H.backwardSurvivorMap_eq_point first i.castSucc hle j.castSucc hf hl z.val.val A
    · exact htj
    · exact hct

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_of_closed_stage_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rmNorm_footprint_of_closed_stage_bounds target :: scope.openDecls } }


private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensBackwardSurvivorDomainBackwardSurvivorTerminalFaceBackwardSurvivorFootprintInterior target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensTerminalRegularOpenIncomingEvent : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensTerminalRegularOpenIncomingEvent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageCastSuccMemOpensTerminalRegularOpenIncomingEvent target :: scope.openDecls } }

theorem ObservedHistory.exists_backwardSurvivorFootprint_curvature_bound
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (_root_.Set.Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (_root_.Set.Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hscalar : ∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ 2 * Q)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ H.time i.succ)
    (htime : 6 * C * (H.time i.succ - c) * Q ≤ 1) :
    _root_.Set.range (H.backwardSurvivorFootprintMap first i hle K) = interior K ∧
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K)
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
          (RealTimeInterval.closed c (H.time i.succ) hcs)) ∧
      ∀ t ∈ _root_.Set.Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)) ^ 2 := by
  have hQ : 0 < Q := hq.trans_le hqQ
  obtain ⟨G,hslabs,hlast,hterminal,_,hsol⟩ := H.exists_backwardSurvivorFootprint_isSolutionOn first i hle K
  refine ⟨H.range_backwardSurvivorFootprintMap first i hle K htrace,G,hslabs,hlast,hterminal,?_,?_⟩
  · exact isSolutionOn_timeRestrict hsol
      (fun t ht => ⟨hc.trans ht.1,ht.2⟩) (fun t ht => ⟨hc.trans_lt ht.1,ht.2⟩)
  · intro t ht z
    have hb : Real.sqrt (normSq0S (G t) z 4 (metricRm04At (G t) z)) ≤
        4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) := by
      apply rmNorm_footprint_of_closed_stage_bounds K G hslabs hlast
        (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)) c ?_
        ⟨hc.trans ht.1,ht.2⟩ ht.1 z
      intro x hx A j hf hl y hy u hu hcu
      have htime' : 6 * C * (H.time i.succ - u) * Q ≤ 1 := by
        apply le_trans _ htime
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_sub_left hcu _) (by positivity)) hQ.le
      have hA := fun j hf hl t ht => hbound j hf hl (A.point j.castSucc hf hl) t ht
      rcases lt_or_eq_of_le hu.2 with hus | rfl
      · have hh := A.riemannNorm_le_of_terminal_scalar_le x hq hqQ hA (hscalar x hx)
          hPhi hpinch j hf hl ⟨hu.1,hus⟩ (by nlinarith [C.coe_nonneg,hQ])
        rw [(H.event j).terminal.extendedMetric_before hus,rmNormSq_restrictOpen,hy]
        exact hh
      · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
        exact A.riemannNorm_terminal_le_of_terminal_scalar_le x hq hqQ hA (hscalar x hx)
          hPhi hpinch j hf hl y hy htime'
    exact (Real.sqrt_le_iff.mp hb).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivorFootprint_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivorFootprint_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivorFootprint_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivorFootprint_curvature_bound

theorem ObservedHistory.metricScalarAt_backwardSurvivorFootprint
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (G : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ i.castSucc), ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
      G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (hlast : ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
      G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
        (H.backwardSurvivorFootprintInterior first i hle K))
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (H.time j.castSucc) (H.time j.succ))
    (x : H.backwardSurvivorFootprintInterior first i hle K) :
    metricScalarAt (G t) x = (H.event j).incoming.flow.scalar t
      (H.backwardSurvivorMap first i.castSucc hle j.castSucc hf hl x.val.val) := by
  by_cases he : j = i
  · subst j
    rw [hlast t ⟨ht.1, ht.2.le⟩, CheegerGromovCompactness.metricScalarAt_restrictOpen,
      ObservedHistory.backwardSurvivorTerminalFaceMetric, metricScalarAt_localPull,
      (H.event i).terminal.extendedMetric_before ht.2, CheegerGromovCompactness.metricScalarAt_restrictOpen,
      H.backwardSurvivorMap_last]
    rfl
  · have hjnext : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hji : j.val ≤ i.val := hl
      have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    rw [hslabs j hf hjnext t ⟨ht.1, ht.2.le⟩,
      CheegerGromovCompactness.metricScalarAt_restrictOpen, CheegerGromovCompactness.metricScalarAt_restrictOpen,
      ObservedHistory.backwardSurvivorSlabMetric, metricScalarAt_localPull,
      (H.event j).terminal.extendedMetric_before ht.2, CheegerGromovCompactness.metricScalarAt_restrictOpen]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.metricScalarAt_backwardSurvivorFootprint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.metricScalarAt_backwardSurvivorFootprint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.metricScalarAt_backwardSurvivorFootprint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.metricScalarAt_backwardSurvivorFootprint


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
