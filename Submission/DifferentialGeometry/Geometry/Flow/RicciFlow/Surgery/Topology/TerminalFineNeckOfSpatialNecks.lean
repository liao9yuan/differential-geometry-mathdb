import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSpatialCanonicalAlternatives
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecks

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hx : 0 < metricScalarAt L.metric x) {εc eps : ℝ} (hεc : 0 < εc) (hεc1 : εc < 1)
    (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∃ᶠ t in 𝓝[<] s, Nonempty (SpatialNeck (G.flow.base.metric t) eps x.val)) :
    ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x := by
  obtain ⟨τ, hτ, hfreq⟩ := Filter.frequently_iff_seq_frequently.mp h
  obtain ⟨φ, hφ, hφP⟩ := _root_.Filter.extraction_of_frequently_atTop hfreq
  let neck : ∀ n, SpatialNeck (G.flow.base.metric (τ (φ n))) eps x.val := fun n => (hφP n).some
  have heps : 0 < eps := (neck 0).eps_pos
  have hinv : εc⁻¹ < eps⁻¹ := by linarith
  have hepsδ : eps < εc := (inv_lt_inv₀ hεc heps).mp hinv
  have hk : ⌊εc⁻¹⌋₊ + 1 ≤ ⌈eps⁻¹⌉₊ := by
    have h1 : ((⌊εc⁻¹⌋₊ : ℕ) : ℝ) + 1 ≤ ((⌈eps⁻¹⌉₊ : ℕ) : ℝ) := by
      have hf := Nat.floor_le (inv_nonneg.mpr hεc.le)
      have hc := Nat.le_ceil eps⁻¹
      linarith
    exact_mod_cast h1
  obtain ⟨n, N, hN, -, -⟩ := (L.eventually_normalizedNeck_of_incoming_spatialNecks
    (hτ.comp hφ.tendsto_atTop) x hx hεc hεc1 hepsδ hfit _ hk neck).exists
  exact ⟨N, hN⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_normalizedNeck_of_frequently_spatialNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem fineCutNecks_of_frequently_spatialNeck {εc eps Qc : ℝ} (hεc : 0 < εc) (hεc1 : εc < 1)
    (hfit : εc⁻¹ + 1 ≤ eps⁻¹)
    (h : ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
      (x : D.slab.terminalRegularOpen),
      x ∈ interior (_root_.Set.range fun p : HalfNeckCylinder => P.horn c e p.1) →
      Qc ≤ metricScalarAt D.terminal.metric x →
      ∃ᶠ t in 𝓝[<] D.endTime,
        Nonempty (SpatialNeck (D.slab.flow.base.metric t) eps x.val)) :
    P.FineCutNecks εc Qc := by
  intro c e x hx hQ
  obtain ⟨⟨⟨y, u⟩, hu⟩, hpx⟩ := interior_subset hx
  change P.horn c e (y, u) = x at hpx
  have hRx : 0 < metricScalarAt D.terminal.metric x := by
    have hl := P.horn_scalar_large c e y u hu
    rw [hpx] at hl
    exact lt_trans (by have := P.coreRadius_pos; positivity) hl
  obtain ⟨N, hN⟩ := D.terminal.exists_normalizedNeck_of_frequently_spatialNeck x hRx hεc hεc1
    hfit (h c e x hx hQ)
  exact ⟨εc, ⌊εc⁻¹⌋₊ + 1, N, hN, le_rfl, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.fineCutNecks_of_frequently_spatialNeck

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
