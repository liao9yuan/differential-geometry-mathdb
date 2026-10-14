import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_identified_initial_pinching_and_static_cap_scale
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    {c ρ q₀ C₀ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hC₀ : 0 < C₀) :
    ∃ a₀ δ₀ : ℝ, 0 < a₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      ∀ p : CutoffParameters, p.recenterConstant ≤ c →
      ∀ records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p,
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) ∧
        (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) ∧
        ∀ i : Fin H.eventCount, p.delta (H.time i.succ) ≤ δ₀ →
          p.neckRadius (H.time i.succ) ≤ ρ →
          ∀ b : (H.event i).RetainedBoundaryIndex,
            q₀ ≤ C₀ * ((records i).static b).neck.scale ∧
              1 ≤ a₀ * ((records i).static b).neck.scale := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  let K := _root_.Max.max (q₀ / C₀) a₀⁻¹
  have hK : 0 < K := (inv_pos.mpr ha₀).trans_le (le_max_right _ _)
  obtain ⟨δ₀, hδ₀, hscale⟩ := exists_uniform_static_cap_scale_lower_bound c ρ K hc hρ hK
  refine ⟨a₀, δ₀, ha₀, hδ₀, ?_⟩
  intro H hH p hpc records
  obtain ⟨hfixed, hscalar⟩ := hinitial H hH
  refine ⟨hfixed, hscalar, ?_⟩
  intro i hδ hρp b
  have hcap := hscale H i p hpc hδ hρp (records i) b
  have hq : q₀ / C₀ ≤ ((records i).static b).neck.scale :=
    (le_max_left _ _).trans hcap.le
  have ha : a₀⁻¹ ≤ ((records i).static b).neck.scale :=
    (le_max_right _ _).trans hcap.le
  constructor
  · have hh := (div_le_iff₀ hC₀).mp hq
    simpa only [mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left ha ha₀.le
    simpa only [mul_inv_cancel₀ ha₀.ne'] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_identified_initial_pinching_and_static_cap_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_identified_initial_pinching_and_static_cap_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_identified_initial_pinching_and_static_cap_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_uniform_identified_initial_pinching_and_static_cap_scale

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
