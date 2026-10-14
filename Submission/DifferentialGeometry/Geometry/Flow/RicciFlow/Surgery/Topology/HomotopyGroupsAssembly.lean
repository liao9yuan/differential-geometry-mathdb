import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import Submission.DifferentialGeometry.Topology.Homology.HurewiczLowDegreeTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology

variable {M : Type u} [TopologicalSpace M]

def CubeSphereHurewiczThreeGeneration : Prop :=
  ∀ y : integralSingularHomology 3 M,
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, M),
      freeSphereHomologyImage (X := M) 2 cubeSphereFundamentalClass (ZerothHomotopy.mk f) = y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeGeneration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeGeneration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeGeneration ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeGeneration

def CubeSphereHurewiczThreeNullhomotopic : Prop :=
  ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, M),
    freeSphereHomologyImage (X := M) 2 cubeSphereFundamentalClass (ZerothHomotopy.mk f) = 0 →
      f.Nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeNullhomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeNullhomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeNullhomotopic ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CubeSphereHurewiczThreeNullhomotopic

theorem cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree
    [SimplyConnectedSpace M] (q : M) :
    CubeSphereHurewiczThreeGeneration (M := M) ↔ Function.Surjective (hurewiczThree q) := by
  change (∀ y : integralSingularHomology 3 M,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, M),
        freeSphereHomologyImage (X := M) 2 cubeSphereFundamentalClass
          (ZerothHomotopy.mk f) = y) ↔
    Function.Surjective (hurewiczThree q)
  rw [← sphereHurewicz_cubeSphereFundamentalClass q]
  exact (surjective_sphereHurewicz_iff_forall_exists_map_eq 2 q
    cubeSphereFundamentalClass).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree

theorem cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree
    [SimplyConnectedSpace M] (q : M) :
    CubeSphereHurewiczThreeNullhomotopic (M := M) ↔ Function.Injective (hurewiczThree q) := by
  constructor
  · intro h
    exact injective_hurewiczThree_of_freeSphereNullhomotopic q
      (show ∀ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, M),
        freeSphereHomologyImage 2 cubeSphereFundamentalClass (ZerothHomotopy.mk f) = 0 →
          f.Nullhomotopic from h)
  · intro h f hf
    rw [← sphereHurewicz_cubeSphereFundamentalClass q] at h
    have hker := forall_sphereHurewicz_eq_zero_of_injective 2 q cubeSphereFundamentalClass h
    have hmk := (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero
      2 q cubeSphereFundamentalClass).mp hker f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 q f).mp hmk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree

theorem cubeSphereHurewiczThreeFrontier_iff_bijective_hurewiczThree
    [SimplyConnectedSpace M] (q : M) :
    (CubeSphereHurewiczThreeNullhomotopic (M := M) ∧
        CubeSphereHurewiczThreeGeneration (M := M)) ↔
      Function.Bijective (hurewiczThree q) :=
  show (CubeSphereHurewiczThreeNullhomotopic (M := M) ∧
      CubeSphereHurewiczThreeGeneration (M := M)) ↔
        Function.Injective (hurewiczThree q) ∧ Function.Surjective (hurewiczThree q) from
    and_congr (cubeSphereHurewiczThreeNullhomotopic_iff_injective_hurewiczThree q)
      (cubeSphereHurewiczThreeGeneration_iff_surjective_hurewiczThree q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_iff_bijective_hurewiczThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_iff_bijective_hurewiczThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_iff_bijective_hurewiczThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_iff_bijective_hurewiczThree

theorem sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup
    (hH₂ : Subsingleton (integralSingularHomology 2 M)) :
    SphereHurewiczTwoCanonical M ↔ ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) := by
  constructor
  · intro h q
    exact homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical h hH₂ q
  · intro h q
    have hq := h q
    have hH := hH₂
    exact IsSphereHurewiczIsomorphism.of_subsingleton 1 q (integralLiftedSphereGenerator.{u} 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup

theorem sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    SphereHurewiczThreeCanonical M ↔
      ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) →
        Function.Bijective (hurewiczThree q) := by
  constructor
  · intro h q hq
    rw [← sphereHurewicz_cubeSphereFundamentalClass q]
    exact (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 q hgen (h q hq)).1
  · intro h q hq
    refine ⟨(bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 q
        cubeSphereFundamentalClass hgen).mp ?_,
      sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator hgen
        q (integralLiftedSphereGenerator.{u} 2)
        (integralLiftedSphereGenerator_isGenerator 2)⟩
    rw [sphereHurewicz_cubeSphereFundamentalClass q]
    exact h q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree

theorem cubeSphereHurewiczThreeFrontier_of_canonical_inputs (x : M) [SimplyConnectedSpace M]
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hcanonTwo : SphereHurewiczTwoCanonical M)
    (hcanonThree : SphereHurewiczThreeCanonical M) :
    HurewiczTwoSphereNullhomotopic M ∧ CubeSphereHurewiczThreeNullhomotopic (M := M) ∧
      CubeSphereHurewiczThreeGeneration (M := M) := by
  have hπ₂ : Subsingleton (HomotopyGroup (Fin 2) M x) :=
    homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hcanonTwo hH₂ x
  have hiso : IsSphereHurewiczIsomorphism 2 M x cubeSphereFundamentalClass :=
    IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hgen (hcanonThree x hπ₂)
  refine ⟨hurewiczTwoSphereNullhomotopic_of_hurewiczTwoBijective
      (hurewiczTwoBijective_of_sphereHurewiczTwoCanonical hcanonTwo) x, ?_, ?_⟩
  · intro f hf
    have hker := forall_sphereHurewicz_eq_zero_of_injective 2 x cubeSphereFundamentalClass hiso.1.1
    have hmk := (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 2 x
      cubeSphereFundamentalClass).mp hker f hf
    exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 2 x f).mp hmk
  · change ∀ y : integralSingularHomology 3 M,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, M),
          freeSphereHomologyImage (X := M) 2 cubeSphereFundamentalClass
            (ZerothHomotopy.mk f) = y
    exact (surjective_sphereHurewicz_iff_forall_exists_map_eq 2 x
      cubeSphereFundamentalClass).mp hiso.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_of_canonical_inputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_of_canonical_inputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_of_canonical_inputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeFrontier_of_canonical_inputs

theorem cubeSphereHurewiczThreeGeneration_punit :
    CubeSphereHurewiczThreeGeneration (M := PUnit.{u + 1}) := by
  intro y
  refine ⟨ContinuousMap.const _ PUnit.unit, ?_⟩
  rw [freeSphereHomologyImage_const]
  exact (integralSingularHomology_subsingleton_of_contractible 3 (by norm_num)
    PUnit.{u + 1}).allEq 0 y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_punit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeGeneration_punit

theorem cubeSphereHurewiczThreeNullhomotopic_punit :
    CubeSphereHurewiczThreeNullhomotopic (M := PUnit.{u + 1}) := by
  intro f _
  refine ⟨PUnit.unit, ?_⟩
  rw [ContinuousMap.ext fun z => Subsingleton.elim (f z) PUnit.unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_punit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeSphereHurewiczThreeNullhomotopic_punit

theorem hurewiczSphereCriteria_punit :
    Subsingleton (integralSingularHomology 2 PUnit.{u + 1}) ∧
      HurewiczTwoSphereNullhomotopic PUnit.{u + 1} ∧
        CubeSphereHurewiczThreeNullhomotopic (M := PUnit.{u + 1}) ∧
          CubeSphereHurewiczThreeGeneration (M := PUnit.{u + 1}) :=
  ⟨integralSingularHomology_subsingleton_of_contractible 2 (by norm_num) PUnit.{u + 1},
    hurewiczTwoSphereCriterion_punit.2, cubeSphereHurewiczThreeNullhomotopic_punit,
    cubeSphereHurewiczThreeGeneration_punit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczSphereCriteria_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczSphereCriteria_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczSphereCriteria_punit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczSphereCriteria_punit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
