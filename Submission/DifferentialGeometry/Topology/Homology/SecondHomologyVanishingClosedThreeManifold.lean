import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalVanishing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Submission.DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNormalization
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleHomology
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

theorem subsingleton_integralRelativeHomology_two_compl_singleton
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M) :
    Subsingleton (integralRelativeHomology 2 ({x}ᶜ : Set M)) := by
  have : T1Space M := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin 3)) M
  let uliftChart :=
    (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin 3))).symm.toOpenPartialHomeomorph
  let : InnerProductSpace ℝ (ULift.{u} (EuclideanSpace ℝ (Fin 3))) :=
    { inner := fun x y => _root_.Inner.inner ℝ x.down y.down
      norm_sq_eq_re_inner := fun x => _root_.InnerProductSpace.norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y r => inner_smul_left x.down y.down r }
  let : ChartedSpace (ULift.{u} (EuclideanSpace ℝ (Fin 3))) M :=
    { atlas := (fun e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) =>
        e.trans uliftChart) '' atlas (EuclideanSpace ℝ (Fin 3)) M
      chartAt := fun x => (chartAt (EuclideanSpace ℝ (Fin 3)) x).trans uliftChart
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin 3)) x, trivial⟩
      chart_mem_atlas := fun x =>
        ⟨chartAt (EuclideanSpace ℝ (Fin 3)) x,
          chart_mem_atlas (EuclideanSpace ℝ (Fin 3)) x, rfl⟩ }
  have hfin : Module.finrank ℝ (ULift.{u} (EuclideanSpace ℝ (Fin 3))) = 1 + 2 :=
    (ULift.moduleEquiv (R := ℝ) (M := EuclideanSpace ℝ (Fin 3))).finrank_eq.trans (by simp)
  exact integralManifoldLocal_subsingleton (ULift.{u} (EuclideanSpace ℝ (Fin 3))) 1 2 hfin
    (by norm_num) M x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_compl_singleton ``Submission.DifferentialGeometry.Topology.subsingleton_integralRelativeHomology_two_compl_singleton

theorem subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M)
    (h : Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M))) :
    Subsingleton (integralSingularHomology 2 M) :=
  subsingleton_integralSingularHomology_two_of_subsingleton_compl_and_relative x h
    (subsingleton_integralRelativeHomology_two_compl_singleton x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton

theorem subsingleton_integralSingularHomology_of_homotopyEquiv {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (e : X ≃ₕ Y)
    [Subsingleton (integralSingularHomology n X)] :
    Subsingleton (integralSingularHomology n Y) :=
  (integralSingularHomologyHomotopyEquiv n e).surjective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_homotopyEquiv

theorem subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (integralSingularHomology 2 M) :=
  haveI : Subsingleton (integralSingularCohomology 1 M) :=
    integralSingularCohomology_one_subsingleton (X := M)
  subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton x
    (subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality x h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured

theorem
    noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton
    {M : Type u} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set M) ↔
      Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M)) := by
  have : Subsingleton (integralSingularCohomology 1 M) :=
    integralSingularCohomology_one_subsingleton (X := M)
  have : Subsingleton (integralCompactSupportCohomologyOne ({x}ᶜ : Set M)) :=
    subsingleton_integralCompactSupportCohomologyOne_compl_singleton x
  exact ⟨fun h =>
      subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
        x h,
    fun h => noncompactPoincareDualityTwoOne_of_subsingleton⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton ``Submission.DifferentialGeometry.Topology.noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton

theorem subsingleton_integralSingularHomology_two_sphereThree_of_noncompactPoincareDuality :
    Subsingleton (integralSingularHomology 2 SphereThree) :=
  subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured
    (Classical.choice (inferInstance : Nonempty SphereThree))
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_of_noncompactPoincareDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_of_noncompactPoincareDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_of_noncompactPoincareDuality ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_sphereThree_of_noncompactPoincareDuality

theorem not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy :
    ¬ Subsingleton (integralSingularHomology 2 sphereTwoTimesCircleModelCopy.Q) := by
  intro h
  exact not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircle
    (@subsingleton_integralSingularHomology_of_homotopyEquiv
      sphereTwoTimesCircleModelCopy.Q SphereTwoTimesCircle _ _ 2
      sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.symm.toHomotopyEquiv h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy ``Submission.DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy

theorem not_subsingleton_integralSingularHomology_two_compl_singleton_sphereTwoTimesCircleModelCopy
    (x : sphereTwoTimesCircleModelCopy.Q) :
    ¬ Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set sphereTwoTimesCircleModelCopy.Q)) :=
  fun h => not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy
    (subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton x h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_compl_singleton_sphereTwoTimesCircleModelCopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_compl_singleton_sphereTwoTimesCircleModelCopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_compl_singleton_sphereTwoTimesCircleModelCopy ``Submission.DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_compl_singleton_sphereTwoTimesCircleModelCopy

theorem not_forall_subsingleton_integralSingularHomology_two_of_closedThreeManifold :
    ¬ (∀ (X : Type) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
        [IsManifold (𝓡 3) ∞ X] [T2Space X] [CompactSpace X] [ConnectedSpace X],
        Subsingleton (integralSingularHomology 2 X)) := by
  intro h
  exact not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy
    (h sphereTwoTimesCircleLift.Carrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedThreeManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedThreeManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedThreeManifold ``Submission.DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedThreeManifold

theorem not_forall_subsingleton_integralSingularHomology_two_of_closedOrientedThreeManifold :
    ¬ (∀ (M : ConnectedClosedOrientedManifold.{0} 3),
        Subsingleton (integralSingularHomology 2 M.Carrier)) := by
  intro h
  exact not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircleModelCopy
    (h sphereTwoTimesCircleLift)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedOrientedThreeManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedOrientedThreeManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedOrientedThreeManifold ``Submission.DifferentialGeometry.Topology.not_forall_subsingleton_integralSingularHomology_two_of_closedOrientedThreeManifold

end DifferentialGeometry.Topology
