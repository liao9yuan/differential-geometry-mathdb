import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_pos_generator_eq :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ 0 < k ∧
      (∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1) ∧ x = y :=
  ⟨1, 1, 1, by norm_num, by norm_num, ⟨LinearMap.id, rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_eq_zsmul_pos_generator_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_eq_zsmul_pos_generator_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_eq_zsmul_pos_generator_eq ``Submission.DifferentialGeometry.Topology.exists_eq_zsmul_pos_generator_eq

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

structure ChildComparisonInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3) where
  Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c
  collapse : G.LocalTerminalEDistComparison Kc
  convergenceTime : ℝ
  convergenceTime_mem : convergenceTime ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)
  scale : ℝ → ℝ
  scale_one : ∀ s ∈ _root_.Set.Ioo convergenceTime (H.time i.succ), 1 ≤ scale s
  scale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1)
  convergence : G.LocalTerminalParentEDistComparison Kc convergenceTime scale
  multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ
  map_eq : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c
  generator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1
  positive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs

variable {G}

theorem ChildComparisonInputs.localLengthComparison
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b) :
    G.LocalLengthComparison h.Kc :=
  G.localLengthComparison_of_terminal_comparisons h.Kc h.convergenceTime_mem
    h.collapse h.convergence h.scale_one h.scale_tendsto

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.localLengthComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.localLengthComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.localLengthComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.localLengthComparison

theorem ChildComparisonInputs.integralHomologyMap_eq
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    integralHomologyMap 3 (h.Kc c).rfs_whole_parent_map (a c) = b c :=
  (ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (K := h.Kc c) (a c) (b c)
    (ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
      (c := c) h.Kc h.collapse)
    (h.map_eq c) (h.generator c) (h.positive c)).2.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.integralHomologyMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.integralHomologyMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.integralHomologyMap_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ChildComparisonInputs.integralHomologyMap_eq

theorem rfs_child_comparison_of_data
    (h : G.ChildComparisonInputs
      (fun c => fundamentalClass (G.Parent c).orientation)
      (fun c => fundamentalClass (G.Child c).orientation)) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  rfs_child_comparison_of_local_length_comparison G h.Kc
    (fun c => h.integralHomologyMap_eq c) h.localLengthComparison

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_data ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_data

theorem rfs_child_comparison_of_nonempty_data
    (h : Nonempty (G.ChildComparisonInputs
      (fun c => fundamentalClass (G.Parent c).orientation)
      (fun c => fundamentalClass (G.Child c).orientation))) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ _root_.Set.Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  rfs_child_comparison_of_data h.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_nonempty_data then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_nonempty_data"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_nonempty_data ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.rfs_child_comparison_of_nonempty_data

theorem nonempty_comparisonSupport_of_simplyConnected
    [∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier] :
    Nonempty ((c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :=
  ⟨fun c => Classical.choice (G.rfs_comparison_support c)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_comparisonSupport_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_comparisonSupport_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_comparisonSupport_of_simplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.nonempty_comparisonSupport_of_simplyConnected

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
