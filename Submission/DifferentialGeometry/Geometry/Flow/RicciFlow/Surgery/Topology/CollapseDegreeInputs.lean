import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegree
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
universe u

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ 0 < k ∧ x ≠ 0 ∧
      ¬ ∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1 := by
  refine ⟨2, 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨φ, hφ⟩
  have h : φ 2 = 2 * φ 1 := by simpa using φ.map_smul (2 : ℤ) (1 : ℤ)
  rw [h] at hφ
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one ``Submission.DifferentialGeometry.Topology.exists_eq_zsmul_pos_ne_zero_not_exists_linearMap_eq_one

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord.ComparisonSupport

theorem localTerminalDistanceControl_const (K : G.ComparisonSupport c)
    (q : (G.Child c).Carrier) :
    K.LocalTerminalDistanceControl (ContinuousMap.const (G.Parent c).Carrier q) := by
  intro x hx
  refine ⟨{y : (G.Parent c).Carrier | y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage continuous_subtype_val).mem_nhds
      (K.support_terminal x hx), fun _ hy => hy, ?_⟩
  intro y _ z _ hy hz
  simp [ContinuousMap.const_apply, riemannianEDistOf_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_const

theorem localTerminalDistanceControl_of_localTerminalEDistComparison
    (Kc : (c' : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c')
    (h : G.LocalTerminalEDistComparison Kc) :
    (Kc c).LocalTerminalDistanceControl (Kc c).rfs_whole_parent_map := by
  intro x hx
  obtain ⟨U, hU, hterm, hmain⟩ := h c x hx
  refine ⟨U, hU, hterm, fun y hy z hz hy' hz' => ?_⟩
  exact (riemannianEDistOf_le_restrictOpen (H.event i).outputMetric
      ((H.stage i.succ).componentOpen c) _ _).trans (hmain y hy z hz hy' hz')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison

end GeometricCutoffRecord.ComparisonSupport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
