import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalReciprocalBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem inv_max_scalar_sub_endpoint_le
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ _root_.Set.Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (_root_.Set.Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2) :
    |(_root_.Max.max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ -
      (_root_.Max.max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹| ≤
        C * (H.time last - H.time first) := by
  induction first using Fin.reverseInduction with
  | last =>
    have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
    subst last
    simp only [A.endpoint_eq, sub_self, abs_zero, _root_.MulZeroClass.mul_zero, le_refl]
  | cast i ih =>
    by_cases he : i.castSucc = last
    · subst last
      simp only [A.endpoint_eq, sub_self, abs_zero, _root_.MulZeroClass.mul_zero, le_refl]
    · have hl : i.succ ≤ last := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : i.castSucc < last := lt_of_le_of_ne hle he
        exact Nat.succ_le_iff.mpr hlt
      let B := A.restrictFirst i.castSucc_lt_succ.le hl
      have htail := ih hl B (fun j hj hlast =>
        hbound j (i.castSucc_lt_succ.le.trans hj) hlast)
      have hcross := A.crossing i le_rfl hl
      let p : (H.event i).incoming.terminalRegularOpen :=
        ⟨A.point i.castSucc le_rfl hle, hcross.mem_terminalRegularRegion (H.event i)⟩
      have hstep := (H.event i).terminal.inv_max_scalar_initial_sub_terminal_le
        (H.event i).incoming hq p (hbound i le_rfl hl)
      have hscalar := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i)
        (p := p) hcross
      change |(_root_.Max.max q (metricScalarAt ((H.event i).incoming.flow.base.metric
        (H.time i.castSucc)) p.val))⁻¹ -
        (_root_.Max.max q (metricScalarAt (H.event i).terminal.metric p))⁻¹| ≤ _ at hstep
      rw [H.event_initial i] at hstep
      change metricScalarAt (H.event i).terminal.metric p =
        metricScalarAt (H.event i).outputMetric (A.point i.succ i.castSucc_lt_succ.le hl) at hscalar
      rw [H.event_output i] at hscalar
      rw [hscalar] at hstep
      have htri := abs_sub_le
        ((_root_.Max.max q (metricScalarAt (H.initialMetric i.castSucc) (A.point i.castSucc le_rfl hle)))⁻¹)
        ((_root_.Max.max q (metricScalarAt (H.initialMetric i.succ)
          (A.point i.succ i.castSucc_lt_succ.le hl)))⁻¹)
        ((_root_.Max.max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹)
      dsimp only [B, restrictFirst] at htail
      nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_endpoint_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_endpoint_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_endpoint_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_endpoint_le

theorem scalar_le_two_mul_of_time_sub_le
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ _root_.Set.Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (_root_.Set.Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric last) endpoint ≤ Q)
    (htime : 2 * C * (H.time last - H.time first) * Q ≤ 1) :
    metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := inv_max_scalar_sub_endpoint_le last first hle endpoint A hq hbound
  have hinv : Q⁻¹ ≤ (_root_.Max.max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * (H.time last - H.time first) ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlower : (2 * Q)⁻¹ ≤
      (_root_.Max.max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ := by
    rw [htwo] at hinv
    linarith [(abs_le.mp hrec).1]
  have hup := (inv_le_inv₀ (by positivity : 0 < 2 * Q)
    (hq.trans_le (le_max_left q
      (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle))))).mp hlower
  exact (le_max_right _ _).trans hup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.scalar_le_two_mul_of_time_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.scalar_le_two_mul_of_time_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.scalar_le_two_mul_of_time_sub_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.scalar_le_two_mul_of_time_sub_le

section

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem inv_max_scalar_initial_sub_incoming_terminal_le
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (_root_.Set.Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ _root_.Set.Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) :
    |(_root_.Max.max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ -
      (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤ C * (s - H.time first) := by
  have hpast := A.inv_max_scalar_sub_endpoint_le last first hle x.val hq hderiv
  have htail := L.inv_max_scalar_initial_sub_terminal_le G hq x hfinal
  change |(_root_.Max.max q (metricScalarAt (G.flow.base.metric (H.time last)) x.val))⁻¹ - _| ≤ _ at htail
  rw [hinit] at htail
  have htri := abs_sub_le
    ((_root_.Max.max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹)
    ((_root_.Max.max q (metricScalarAt (H.initialMetric last) x.val))⁻¹)
    ((_root_.Max.max q (metricScalarAt L.metric x))⁻¹)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_initial_sub_incoming_terminal_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_initial_sub_incoming_terminal_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_initial_sub_incoming_terminal_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_initial_sub_incoming_terminal_le


end

theorem inv_max_scalar_sub_incoming_terminal_le_on_time_window
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (H.time j.castSucc) (H.time j.succ))
    (hderiv : ∀ k : Fin H.eventCount, ∀ hfk : j.castSucc ≤ k.castSucc, ∀ hlk : k.succ ≤ last,
      ∀ v ∈ _root_.Set.Ioo (H.time k.castSucc) (H.time k.succ), t ≤ v →
        q < (H.event k).incoming.flow.scalar v
          (A.point k.castSucc (hf.trans hfk) (k.castSucc_lt_succ.le.trans hlk)) →
        |derivWithin (fun w => (H.event k).incoming.flow.scalar w
          (A.point k.castSucc (hf.trans hfk) (k.castSucc_lt_succ.le.trans hlk))) (_root_.Set.Iic v) v| ≤
          C * (H.event k).incoming.flow.scalar v
            (A.point k.castSucc (hf.trans hfk) (k.castSucc_lt_succ.le.trans hlk)) ^ 2)
    (hfinal : ∀ v ∈ _root_.Set.Ioo (H.time last) s, t ≤ v → q < G.flow.scalar v x.val →
      |derivWithin (fun w => G.flow.scalar w x.val) (_root_.Set.Iic v) v| ≤ C * G.flow.scalar v x.val ^ 2) :
    |(_root_.Max.max q ((H.event j).incoming.flow.scalar t
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))))⁻¹ -
      (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤ C * (s - t) := by
  let B := A.restrictFirst (hf.trans j.castSucc_lt_succ.le) hl
  have htail := B.inv_max_scalar_initial_sub_incoming_terminal_le G L hinit x hq
    (fun k hk hkl v hv => hderiv k (j.castSucc_lt_succ.le.trans hk) hkl v hv
      ((ht.2.le.trans (H.time_strictMono.monotone hk)).trans hv.1.le))
    (fun v hv => hfinal v hv ((ht.2.le.trans (H.time_strictMono.monotone hl)).trans hv.1.le))
  have hcross := A.crossing j hf hl
  let p : (H.event j).incoming.terminalRegularOpen :=
    ⟨A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl),
      hcross.mem_terminalRegularRegion (H.event j)⟩
  have hstep := (H.event j).terminal.inv_max_scalar_sub_terminal_le_on_time_window
    (H.event j).incoming hq p ht.1 ht.2
    (fun v hv => hderiv j le_rfl hl v ⟨ht.1.trans_lt hv.1,hv.2⟩ hv.1.le)
    (show t ∈ _root_.Set.Ico t (H.time j.succ) from ⟨le_rfl,ht.2⟩)
  have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event j) (p := p) hcross
  rw [H.event_output j] at heq
  rw [heq] at hstep
  have htri := abs_sub_le
    ((_root_.Max.max q ((H.event j).incoming.flow.scalar t p.val))⁻¹)
    ((_root_.Max.max q (metricScalarAt (H.initialMetric j.succ)
      (A.point j.succ (hf.trans j.castSucc_lt_succ.le) hl)))⁻¹)
    ((_root_.Max.max q (metricScalarAt L.metric x))⁻¹)
  dsimp only [B, restrictFirst] at htail
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_incoming_terminal_le_on_time_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_incoming_terminal_le_on_time_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_incoming_terminal_le_on_time_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.inv_max_scalar_sub_incoming_terminal_le_on_time_window

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
