import Submission.DifferentialGeometry.Topology.Homology.SphereHurewicz
import Submission.DifferentialGeometry.Topology.Homology.SphereGenerator
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Submission.DifferentialGeometry.Topology.Homology.PathCones

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem freeSphereHomologyImage_add (n : ℕ)
    (c d : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n (c + d) a =
      freeSphereHomologyImage n c a + freeSphereHomologyImage n d a := by
  induction a using ZerothHomotopy.rec with
  | mk f => simp only [freeSphereHomologyImage_mk, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_add ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_add

theorem freeSphereHomologyImage_zero (n : ℕ)
    (a : ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n (0 : integralSingularHomology (n + 1)
      (liftedHomotopySphere.{u} n)) a = 0 := by
  induction a using ZerothHomotopy.rec with
  | mk f => simp only [freeSphereHomologyImage_mk, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_zero ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_zero

theorem freeSphereHomologyImage_neg (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : ZerothHomotopy C(_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSphereHomologyImage n (-c) a = -freeSphereHomologyImage n c a := by
  simpa using freeSphereHomologyImage_zsmul n (-1) c a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSphereHomologyImage_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSphereHomologyImage_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSphereHomologyImage_neg ``Submission.DifferentialGeometry.Topology.freeSphereHomologyImage_neg

theorem sphereHurewicz_add (n : ℕ) (x : X)
    (c d : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n x (c + d) a = sphereHurewicz n x c a + sphereHurewicz n x d a :=
  freeSphereHomologyImage_add n c d _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_add ``Submission.DifferentialGeometry.Topology.sphereHurewicz_add

theorem sphereHurewicz_neg (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    sphereHurewicz n x (-c) a = -sphereHurewicz n x c a := by
  simpa using sphereHurewicz_zsmul n (-1) x c a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_neg ``Submission.DifferentialGeometry.Topology.sphereHurewicz_neg

def IsSphereHurewiczIsomorphism (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) : Prop :=
  Function.Bijective (sphereHurewicz n x c) ∧
    ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x c (a * b) = sphereHurewicz n x c a + sphereHurewicz n x c b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism ``Submission.DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism

theorem IsSphereHurewiczIsomorphism.neg (n : ℕ) {x : X}
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHurewiczIsomorphism n X x c) :
    IsSphereHurewiczIsomorphism n X x (-c) := by
  refine ⟨?_, ?_⟩
  · have hfun : sphereHurewicz n x (-c) = fun a => -sphereHurewicz n x c a :=
      funext fun a => sphereHurewicz_neg n x c a
    rw [hfun]
    exact (Equiv.comp_bijective (sphereHurewicz n x c) (Equiv.neg _)).mpr h.1
  · intro a b
    rw [sphereHurewicz_neg, sphereHurewicz_neg, sphereHurewicz_neg, h.2 a b, neg_add]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.neg ``Submission.DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.neg

theorem IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator (n : ℕ) (x : X)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (hc : IsSphereHomologyGenerator n c)
    (h : IsSphereHurewiczIsomorphism n X x (integralLiftedSphereGenerator.{u} n)) :
    IsSphereHurewiczIsomorphism n X x c := by
  rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator n c).mp hc
    with rfl | hneg
  · exact h
  · rw [hneg]
    exact IsSphereHurewiczIsomorphism.neg n h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator ``Submission.DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator

theorem IsSphereHurewiczIsomorphism.of_subsingleton (n : ℕ) (x : X)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))
    [Subsingleton (HomotopyGroup (Fin (n + 1)) X x)]
    [Subsingleton (integralSingularHomology (n + 1) X)] :
    IsSphereHurewiczIsomorphism n X x c :=
  ⟨⟨fun a b _ => Subsingleton.elim a b,
      fun y => ⟨1, (sphereHurewicz_one n x c).trans (Subsingleton.elim 0 y)⟩⟩,
    fun _ _ => Subsingleton.elim _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_subsingleton ``Submission.DifferentialGeometry.Topology.IsSphereHurewiczIsomorphism.of_subsingleton

def SphereHurewiczTwoCanonical (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, IsSphereHurewiczIsomorphism 1 X x (integralLiftedSphereGenerator.{u} 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereHurewiczTwoCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereHurewiczTwoCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereHurewiczTwoCanonical ``Submission.DifferentialGeometry.Topology.SphereHurewiczTwoCanonical

def SphereHurewiczThreeCanonical (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x) →
    IsSphereHurewiczIsomorphism 2 X x (integralLiftedSphereGenerator.{u} 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereHurewiczThreeCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereHurewiczThreeCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereHurewiczThreeCanonical ``Submission.DifferentialGeometry.Topology.SphereHurewiczThreeCanonical

theorem sphereHurewicz_two_isomorphism_iff_canonical_generator :
    (∀ (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
      (_ : IsSphereHomologyGenerator 1 c), IsSphereHurewiczIsomorphism 1 X x c) ↔
      SphereHurewiczTwoCanonical X := by
  constructor
  · intro h x
    exact h x (integralLiftedSphereGenerator.{u} 1)
      (integralLiftedSphereGenerator_isGenerator 1)
  · intro h x c hc
    exact IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_iff_canonical_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_iff_canonical_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_iff_canonical_generator ``Submission.DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_iff_canonical_generator

theorem sphereHurewicz_three_isomorphism_iff_canonical_generator :
    (∀ (x : X) (_ : Subsingleton (HomotopyGroup (Fin 2) X x))
      (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
      (_ : IsSphereHomologyGenerator 2 c), IsSphereHurewiczIsomorphism 2 X x c) ↔
      SphereHurewiczThreeCanonical X := by
  constructor
  · intro h x hπ₂
    exact h x hπ₂ (integralLiftedSphereGenerator.{u} 2)
      (integralLiftedSphereGenerator_isGenerator 2)
  · intro h x hπ₂ c hc
    exact IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc (h x hπ₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_iff_canonical_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_iff_canonical_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_iff_canonical_generator ``Submission.DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_iff_canonical_generator

theorem sphereHurewicz_two_isomorphism_of_canonical_generator
    (h : SphereHurewiczTwoCanonical X) (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) ∧
      ∀ a b : HomotopyGroup (Fin 2) X x,
        sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 1 x hc (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_of_canonical_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_of_canonical_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_of_canonical_generator ``Submission.DifferentialGeometry.Topology.sphereHurewicz_two_isomorphism_of_canonical_generator

theorem sphereHurewicz_three_isomorphism_of_canonical_generator
    (h : SphereHurewiczThreeCanonical X) (x : X)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hc (h x hπ₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_of_canonical_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_of_canonical_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_of_canonical_generator ``Submission.DifferentialGeometry.Topology.sphereHurewicz_three_isomorphism_of_canonical_generator

theorem subsingleton_homotopyGroup_one [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 1) X x) :=
  (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).injective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_homotopyGroup_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_homotopyGroup_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_homotopyGroup_one ``Submission.DifferentialGeometry.Topology.subsingleton_homotopyGroup_one

theorem hurewicz_one_isomorphism [SimplyConnectedSpace X] (x : X)
    (c : integralSingularHomology 1 (liftedHomotopySphere.{u} 0))
    (_ : IsSphereHomologyGenerator 0 c) :
    Function.Bijective (sphereHurewicz 0 x c) ∧
      ∀ a b : HomotopyGroup (Fin 1) X x,
        sphereHurewicz 0 x c (a * b) = sphereHurewicz 0 x c a + sphereHurewicz 0 x c b := by
  have hπ : Subsingleton (HomotopyGroup (Fin 1) X x) := subsingleton_homotopyGroup_one x
  have hH : Subsingleton (integralSingularHomology 1 X) := integralSingularHomology_one_subsingleton
  exact IsSphereHurewiczIsomorphism.of_subsingleton 0 x c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewicz_one_isomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewicz_one_isomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewicz_one_isomorphism ``Submission.DifferentialGeometry.Topology.hurewicz_one_isomorphism

theorem subsingleton_homotopyGroup_of_subsingleton [Subsingleton X] (N : Type*) (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  have hge : ∀ a b : GenLoop N X x, a = b := fun a b =>
    Subtype.ext (ContinuousMap.ext fun _ => Subsingleton.elim _ _)
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => rw [hge a b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_homotopyGroup_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_homotopyGroup_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_homotopyGroup_of_subsingleton ``Submission.DifferentialGeometry.Topology.subsingleton_homotopyGroup_of_subsingleton

theorem sphereHurewiczTwoCanonical_punit : SphereHurewiczTwoCanonical PUnit.{u + 1} := by
  intro x
  have hπ : Subsingleton (HomotopyGroup (Fin 2) PUnit.{u + 1} x) :=
    subsingleton_homotopyGroup_of_subsingleton (Fin 2) x
  have hH : Subsingleton (integralSingularHomology 2 PUnit.{u + 1}) :=
    integralSingularHomology_subsingleton_of_contractible 2 (by omega) PUnit.{u + 1}
  exact IsSphereHurewiczIsomorphism.of_subsingleton 1 x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_punit ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoCanonical_punit

theorem sphereHurewiczThreeCanonical_punit : SphereHurewiczThreeCanonical PUnit.{u + 1} := by
  intro x _
  have hπ : Subsingleton (HomotopyGroup (Fin 3) PUnit.{u + 1} x) :=
    subsingleton_homotopyGroup_of_subsingleton (Fin 3) x
  have hH : Subsingleton (integralSingularHomology 3 PUnit.{u + 1}) :=
    integralSingularHomology_subsingleton_of_contractible 3 (by omega) PUnit.{u + 1}
  exact IsSphereHurewiczIsomorphism.of_subsingleton 2 x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_punit ``Submission.DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_punit

end DifferentialGeometry.Topology
