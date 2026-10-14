import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import Submission.DifferentialGeometry.Geometry.Neck.Recentering
import Submission.DifferentialGeometry.Geometry.Neck.Orientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereAttachment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D accuracy : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

theorem recenter_fields_of_neck_heq
    (S : E.PresentedStaticCap fixed D m accuracy b)
    {x : E.incoming.terminalRegularOpen} {δ c : ℝ} {k l j : ℕ}
    (d : normalizedDatum E.terminal.metric x δ k)
    (dHigh : normalizedDatum E.terminal.metric x δ l) (hHigh : dHigh.map = d.map)
    (side : Bool)
    (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹)
    (dCap : normalizedDatum E.terminal.metric
      (d.offsetPoint (cuttingSign_sq side)) (c * δ) j)
    (hmap : dCap.map = d.recenteringMap (cuttingSign_sq side) hfit)
    (hside : dCap.retainedSide = _root_.Bool.true)
    (hdelta : S.delta = c * δ) (horder : S.order = j)
    (hneck : HEq S.neck dCap.oriented.toNormalizedNeck)
    (hratio : |metricScalarAt E.terminal.metric (d.offsetPoint (cuttingSign_sq side)) /
      metricScalarAt E.terminal.metric x - 1| ≤ c * δ) :
    S.delta = c * δ ∧ S.order = j ∧
      S.neck.sphereMark = dHigh.toNormalizedNeck.sphereMark ∧
      |S.neck.scale / dHigh.toNormalizedNeck.scale - 1| ≤ c * δ ∧
      (∀ q : neckBuffer S.delta,
        (q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)) ∈ neckBuffer δ) ∧
      (∀ q : neckBuffer S.delta,
        ∀ hq : (q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)) ∈ neckBuffer δ,
        S.neck.chart q = dHigh.toNormalizedNeck.chart
          ⟨(q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)), hq⟩) := by
  rcases S with ⟨δS, kS, N, rest⟩
  dsimp only at hdelta horder hneck ⊢
  subst δS
  subst kS
  have hN := eq_of_heq hneck
  cases hN
  refine ⟨rfl, rfl, rfl, hratio, ?_, ?_⟩
  · intro q
    have h := (recenteringCylinderMap (cuttingSign_sq side) hfit q).property
    have hv := recenteringCylinderMap_val (cuttingSign_sq side) hfit q
    exact hv ▸ h
  · intro q hq
    change dCap.oriented.map q = dHigh.map _
    rw [normalizedDatum.oriented_map_of_retainedSide_true dCap hside, hmap, hHigh]
    apply congrArg d.map
    apply Subtype.ext
    exact recenteringCylinderMap_val (cuttingSign_sq side) hfit q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq

theorem recenter_fields_of_neck_heq_terminal
    (S : E.PresentedStaticCap fixed D m accuracy b)
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric)
    (hG : E.incoming = G) (hL : HEq E.terminal L)
    {x : G.terminalRegularOpen} {δ c : ℝ} {k l j : ℕ}
    (d : normalizedDatum L.metric x δ k)
    (dHigh : normalizedDatum L.metric x δ l) (hHigh : dHigh.map = d.map)
    (side : Bool)
    (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹)
    (dCap : normalizedDatum L.metric
      (d.offsetPoint (cuttingSign_sq side)) (c * δ) j)
    (hmap : dCap.map = d.recenteringMap (cuttingSign_sq side) hfit)
    (hside : dCap.retainedSide = _root_.Bool.true)
    (hdelta : S.delta = c * δ) (horder : S.order = j)
    (hneck : HEq S.neck dCap.oriented.toNormalizedNeck)
    (hratio : |metricScalarAt L.metric (d.offsetPoint (cuttingSign_sq side)) /
      metricScalarAt L.metric x - 1| ≤ c * δ) :
    S.delta = c * δ ∧ S.order = j ∧
      S.neck.sphereMark = dHigh.toNormalizedNeck.sphereMark ∧
      |S.neck.scale / dHigh.toNormalizedNeck.scale - 1| ≤ c * δ ∧
      (∀ q : neckBuffer S.delta,
        (q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)) ∈ neckBuffer δ) ∧
      (∀ q : neckBuffer S.delta,
        ∀ hq : (q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)) ∈ neckBuffer δ,
        HEq (S.neck.chart q) (dHigh.toNormalizedNeck.chart
          ⟨(q.1.1, (if side then (1 : ℝ) else -1) * (1 + q.1.2)), hq⟩)) := by
  subst G
  cases eq_of_heq hL
  obtain ⟨hd, ho, hm, hr, hb, hc⟩ := S.recenter_fields_of_neck_heq
    d dHigh hHigh side hfit dCap hmap hside hdelta horder hneck hratio
  exact ⟨hd, ho, hm, hr, hb, fun q hq => heq_of_eq (hc q hq)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.recenter_fields_of_neck_heq_terminal

end MetricCutCapEvent.PresentedStaticCap
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
