import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.CapWindowPoint.of_le_time {P₀ : OrientedThreeStage.{u}}
    {H : RetainedCoreHistory P₀} {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    {k : Fin (H.eventCount + 1)} {y : (H.stage k).Carrier} {σ t D θ θ' S : ℝ}
    (h : H.CapWindowPoint records k y σ D θ) (hσt : σ ≤ t)
    (hS : ∀ i b, ((records i).static b).neck.scale ≤ S)
    (hslack : S * (t - σ) ≤ θ' - θ) :
    H.CapWindowPoint records k y t D θ' := by
  obtain ⟨j, hl, A, b, x, hx, hxn, hage⟩ := h
  refine ⟨j, hl, A, b, x, hx, hxn, ?_⟩
  have hsc := ((records j).static b).neck.scale_pos
  have hle : ((records j).static b).neck.scale * (t - σ) ≤ θ' - θ :=
    (mul_le_mul_of_nonneg_right (hS j b) (sub_nonneg.mpr hσt)).trans hslack
  have hdiv : t - σ ≤ (θ' - θ) * (((records j).static b).neck.scale)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hsc]
    linarith
  calc t - H.time j.succ = (σ - H.time j.succ) + (t - σ) := by ring
    _ ≤ θ * (((records j).static b).neck.scale)⁻¹ +
        (θ' - θ) * (((records j).static b).neck.scale)⁻¹ := add_le_add hage hdiv
    _ = θ' * (((records j).static b).neck.scale)⁻¹ := by ring

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.CapWindowPoint
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.CapWindowPoint.of_le_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.CapWindowPoint.of_le_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.CapWindowPoint.of_le_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.CapWindowPoint.of_le_time

theorem RetainedCoreHistory.exists_forall_neck_scale_le {P₀ : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory P₀) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) :
    ∃ S : ℝ, 0 < S ∧ ∀ i b, ((records i).static b).neck.scale ≤ S := by
  obtain ⟨S₀, hS₀⟩ := (Set.finite_range fun ib :
    (Σ i : Fin H.eventCount, (H.toHistory.event i).RetainedBoundaryIndex) =>
      ((records ib.1).static ib.2).neck.scale).bddAbove
  exact ⟨max S₀ 1, lt_max_of_lt_right one_pos,
    fun i b => (hS₀ ⟨⟨i, b⟩, rfl⟩).trans (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_forall_neck_scale_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_forall_neck_scale_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_forall_neck_scale_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_forall_neck_scale_le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
