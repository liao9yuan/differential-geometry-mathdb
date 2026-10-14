import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceConstruction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem backward_traces_on_set_or_recent_presented_cap
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ ≤ 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hcrossTime : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ)
    (hscalar : ∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, first < j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hf hl b).neck.scale / 2 ≤
          metricScalarAt (S j hf hl b).witness.metric ((S j hf hl b).witness.cap z)) :
    (∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) ∨
      ∃ (x : G.terminalRegularOpen), x ∈ K ∧
        ∃ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
          (A : BackwardPointTrace H j.succ last hl x.val)
          (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ¬ Nonempty (BackwardPointTrace H first last hle x.val) ∧
          (H.event j).transition.trace.presentation ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
          A.point j.succ le_rfl hl = (S j hf hl b).inclusion ((S j hf hl b).witness.cap z) ∧
          metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
          (S j hf hl b).neck.scale < 4 * Q ∧
          0 < (S j hf hl b).neck.scale * (s - H.time j.succ) ∧
          (S j hf hl b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
          (S j hf hl b).neck.scale * (s - H.time j.succ) < 1 := by
  classical
  by_cases hall : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x, hx, hnot⟩ := hall
    have hn : ¬ Nonempty (BackwardPointTrace H first last hle x.val) :=
      not_nonempty_iff.mpr hnot
    rcases H.exists_backwardPointTrace_or_recent_presented_cap_of_incoming_slab first last hle G L hinit
      x hq hqQ hθsmall hbudget hcrossTime (hscalar x hx) hderiv (hfinal x hx) hOld S hcap with
      htrace | ⟨j, hf, hl, A, b, z, hpres, hbirth, hsc, hqcap, hage, hagesmall, hageone⟩
    · exact False.elim (hn htrace)
    · exact Or.inr ⟨x, hx, j, hf, hl, A, b, z, hn, hpres, hbirth, hsc, hqcap,
        hage, hagesmall, hageone⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_traces_on_set_or_recent_presented_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_traces_on_set_or_recent_presented_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_traces_on_set_or_recent_presented_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_traces_on_set_or_recent_presented_cap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_backward_traces_of_terminal_scalar_upper_bound
    (c ρ Qbar : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (K : Set G.terminalRegularOpen) (q Q θ : ℝ) (C : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / Q < H.time j.succ) →
      (∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q) →
      (∀ j : Fin H.eventCount, first < j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
          q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (H.time last) s, q < G.flow.scalar t x.val →
        |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2) →
      ∀ (p : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j p),
      p.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
      ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val) := by
  obtain ⟨δ₀, hδ₀, hscale⟩ := exists_uniform_static_cap_scale_lower_bound c ρ (4 * Qbar)
    hc hρ (by positivity)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar hderiv hfinal p records hpc hδ hrad hcap x hx
  rcases H.exists_backwardPointTrace_or_recent_presented_cap_of_incoming_slab first last hle G L hinit
    x hq hqQ hθ hbudget hcrossTime (hscalar x hx) hderiv (hfinal x hx)
    (fun j _ _ => (records j).old_eq_retained) (fun j _ _ => (records j).static) hcap with
    htrace | ⟨j, hf, hl, A, b, z, _, _, _, hscaleUpper, _⟩
  · exact htrace
  · have hscaleLower := hscale H j p hpc (hδ j hf hl) (hrad j hf hl) (records j) b
    exfalso
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_backward_flow_of_terminal_scalar_upper_bound
    (c ρ Qbar : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (K : Set G.terminalRegularOpen) (q Q θ : ℝ) (C : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / Q < H.time j.succ) →
      (∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
          q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (H.time last) s, q < G.flow.scalar t x.val →
        |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2) →
      ∀ (p : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j p),
      p.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
      H.time first ≤ s - θ / Q → 0 < θ →
      ∀ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
          (_root_.Set.Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
      Perelman.PhiAlmostNonnegative G.flow (_root_.Set.Ico (H.time last) s) Phi →
      _root_.Set.range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first last hle G K))
        (hcs : s - θ / Q ≤ s),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        (∀ t ∈ _root_.Set.Icc (H.time last) s,
          gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        gflow s = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first last hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
            (RealTimeInterval.closed (s - θ / Q) s hcs)) ∧
        ∀ t ∈ _root_.Set.Icc (s - θ / Q) s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
          normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
            (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 := by
  obtain ⟨δ₀, hδ₀, htraces⟩ := exists_uniform_backward_traces_of_terminal_scalar_upper_bound
    c ρ Qbar hc hρ hQbar
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar hderiv hfinal p records hpc hδ hrad hcap hroom hθpos Phi hPhi
    hpinch hpinchFinal
  have hQ : 0 < Q := hq.trans_le hqQ
  have hall := htraces H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar (fun j hf hl => hderiv j hf.le hl) hfinal p records hpc hδ hrad hcap
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθpos.le hQ.le)
  have hbudget' : 6 * (C : ℝ) * (s - (s - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * (C : ℝ) * (s - (s - θ / Q)) * Q = 6 * C * θ := by
      field_simp
      ring
    rw [heq]
    exact hbudget
  obtain ⟨hrange, gflow, hslabs, hlast, hterminal, hsol, hbound⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound first last hle G L hinit K
      hq hqQ hPhi hderiv hfinal hpinch hpinchFinal
      (fun x hx => (hscalar x hx).trans (by linarith)) hall hroom hcs hbudget'
  exact ⟨hrange, gflow, hcs, hslabs, hlast, hterminal, hsol, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window
    (c ρ Qbar : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (K : Set G.terminalRegularOpen) (q Q θ : ℝ) (C : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / Q < H.time j.succ) →
      (∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q) →
      (∀ j : Fin H.eventCount, first < j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
          s - θ / Q ≤ t → q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t x.val →
        |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2) →
      ∀ (p : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j p),
      p.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
      ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val) := by
  obtain ⟨δ₀, hδ₀, hscale⟩ := exists_uniform_static_cap_scale_lower_bound c ρ (4 * Qbar)
    hc hρ (by positivity)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar hderiv hfinal p records hpc hδ hrad hcap x hx
  rcases H.exists_backwardPointTrace_or_recent_presented_cap_on_time_window first last hle G L hinit
    x hq hqQ hθ hbudget hcrossTime (hscalar x hx) hderiv (hfinal x hx)
    (fun j _ _ => (records j).old_eq_retained) (fun j _ _ => (records j).static) hcap with
    htrace | ⟨j, hf, hl, A, b, z, _, _, _, hscaleUpper, _⟩
  · exact htrace
  · have hscaleLower := hscale H j p hpc (hδ j hf hl) (hrad j hf hl) (records j) b
    exfalso
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_backward_flow_of_terminal_scalar_upper_bound_on_time_window
    (c ρ Qbar : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hQbar : 0 < Qbar) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (K : Set G.terminalRegularOpen) (q Q θ : ℝ) (C : ℝ≥0),
      0 < q → q ≤ Q → Q ≤ Qbar → θ ≤ 1 / 4 → 6 * C * θ ≤ 1 →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        s - θ / Q < H.time j.succ) →
      (∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
          s - θ / Q ≤ t → q < (H.event j).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t y ^ 2) →
      (∀ x ∈ K, ∀ t ∈ _root_.Set.Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t x.val →
        |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x.val ^ 2) →
      ∀ (p : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j p),
      p.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → p.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
      H.time first ≤ s - θ / Q → 0 < θ →
      ∀ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
          (_root_.Set.Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
      Perelman.PhiAlmostNonnegative G.flow (_root_.Set.Ico (H.time last) s) Phi →
      _root_.Set.range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      ∃ (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.backwardSurvivorIncomingFootprint first last hle G K))
        (hcs : s - θ / Q ≤ s),
        (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
          ∀ t ∈ _root_.Set.Icc (H.time j.castSucc) (H.time j.succ),
            gflow t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
              (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
                (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        (∀ t ∈ _root_.Set.Icc (H.time last) s,
          gflow t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
            (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
        gflow s = localPullMetric L.metric
          (H.backwardSurvivorIncomingFootprintMap first last hle G K)
          (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
        IsSolutionOn ({ base := { metric := gflow } } :
          SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingFootprint first last hle G K)
            (RealTimeInterval.closed (s - θ / Q) s hcs)) ∧
        ∀ t ∈ _root_.Set.Icc (s - θ / Q) s, ∀ z : H.backwardSurvivorIncomingFootprint first last hle G K,
          normSq0S (gflow t) z 4 (metricRm04At (gflow t) z) ≤
            (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 := by
  obtain ⟨δ₀, hδ₀, htraces⟩ := exists_uniform_backward_traces_of_terminal_scalar_upper_bound_on_time_window
    c ρ Qbar hc hρ hQbar
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar hderiv hfinal p records hpc hδ hrad hcap hroom hθpos Phi hPhi
    hpinch hpinchFinal
  have hQ : 0 < Q := hq.trans_le hqQ
  have hall := htraces H first last hle s G L hinit K q Q θ C hq hqQ hQQbar hθ hbudget
    hcrossTime hscalar (fun j hf hl => hderiv j hf.le hl) hfinal p records hpc hδ hrad hcap
  have hcs : s - θ / Q ≤ s := sub_le_self _ (div_nonneg hθpos.le hQ.le)
  have hbudget' : 6 * (C : ℝ) * (s - (s - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * (C : ℝ) * (s - (s - θ / Q)) * Q = 6 * C * θ := by
      field_simp
      ring
    rw [heq]
    exact hbudget
  obtain ⟨hrange, gflow, hslabs, hlast, hterminal, hsol, hbound⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound_on_time_window first last hle G L hinit K
      (by linarith [div_pos hθpos hQ] : s - θ / Q < s) hcrossTime hq hqQ hPhi hderiv hfinal hpinch hpinchFinal
      (fun x hx => (hscalar x hx).trans (by linarith)) hall hroom hbudget'
  exact ⟨hrange, gflow, hcs, hslabs, hlast, hterminal, hsol, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound_on_time_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound_on_time_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound_on_time_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_uniform_backward_flow_of_terminal_scalar_upper_bound_on_time_window

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
