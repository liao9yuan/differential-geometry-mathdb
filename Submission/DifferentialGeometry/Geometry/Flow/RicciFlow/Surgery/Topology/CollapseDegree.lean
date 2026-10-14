import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import Submission.DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion
import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u

namespace DifferentialGeometry.Topology

theorem eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos
    {M : Type u} [AddCommGroup M] [Module ℤ M] {x y : M} {k : ℤ}
    (h : ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) (hxy : x = k • y) (hk : 0 < k) : k = 1 := by
  rcases Int.isUnit_iff.mp (isUnit_of_exists_linearMap_eq_one x h hxy) with h1 | h1
  · exact h1
  · omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos ``Submission.DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos

theorem not_exists_linearMap_eq_one_zero {M : Type u} [AddCommGroup M] [Module ℤ M] :
    ¬ ∃ φ : M →ₗ[ℤ] ℤ, φ (0 : M) = 1 := by
  rintro ⟨φ, hφ⟩
  rw [map_zero] at hφ
  exact zero_ne_one hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_exists_linearMap_eq_one_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_exists_linearMap_eq_one_zero ``Submission.DifferentialGeometry.Topology.not_exists_linearMap_eq_one_zero

theorem exists_eq_zsmul_not_isUnit :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ ¬ IsUnit k :=
  ⟨0, 0, 0, by simp, by rw [Int.isUnit_iff]; norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_eq_zsmul_not_isUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_eq_zsmul_not_isUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_eq_zsmul_not_isUnit ``Submission.DifferentialGeometry.Topology.exists_eq_zsmul_not_isUnit

theorem exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ (∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1) ∧ k ≠ 1 :=
  ⟨-1, 1, -1, by norm_num, ⟨LinearMap.id, rfl⟩, by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one ``Submission.DifferentialGeometry.Topology.exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one

theorem exists_linearMap_eq_one_integralLiftedSphereGenerator :
    ∃ φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ,
      φ (integralLiftedSphereGenerator.{u} 2) = 1 :=
  (isSphereHomologyGenerator_iff_exists_functional 2
    (integralLiftedSphereGenerator.{u} 2)).mp (integralLiftedSphereGenerator_isGenerator 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_linearMap_eq_one_integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_linearMap_eq_one_integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_linearMap_eq_one_integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.exists_linearMap_eq_one_integralLiftedSphereGenerator

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord

namespace ComparisonSupport

variable (K : G.ComparisonSupport c)

def LocalTerminalDistanceControl
    (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  ∀ x ∈ K.support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    (∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf (H.event i).outputMetric (f y).1 (f z).1 ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalDistanceControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalDistanceControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalDistanceControl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.LocalTerminalDistanceControl

theorem rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl
    (hlip : K.LocalTerminalDistanceControl K.rfs_whole_parent_map) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map := by
  intro x hx
  obtain ⟨U, hU, hterm, hdist⟩ := hlip x hx
  refine ⟨U, hU, hterm, hdist, ?_⟩
  intro γ hparent a b hab hγ hγU hlen
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_iSup (fun q : ℕ ×
    {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ _root_.Set.Icc a b} =>
      ∑ j ∈ Finset.range q.1, riemannianEDistOf (H.event i).terminal.metric
        (γ (q.2.1 (j + 1))) (γ (q.2.1 j))) p)
  exact hdist _ (hγU _ (p.2.2.2 (k + 1))) _ (hγU _ (p.2.2.2 k))
    (γ (p.2.1 (k + 1))).2 (γ (p.2.1 k)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl

theorem rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hlip : K.LocalTerminalDistanceControl K.rfs_whole_parent_map)
    (hmap : integralHomologyMap 3 K.rfs_whole_parent_map a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 K.rfs_whole_parent_map a) = 1)
    (hk : 0 < k) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map a = b ∧
    Function.Surjective K.rfs_whole_parent_map := by
  have hclass : integralHomologyMap 3 K.rfs_whole_parent_map a = b := by
    have hone : k = 1 :=
      DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos
        hgen hmap hk
    rw [hmap, hone, one_smul]
  exact ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl hlip,
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    fun x => K.rfs_whole_parent_map_childCore x, hclass,
    K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
