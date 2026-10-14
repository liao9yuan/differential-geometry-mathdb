import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set
open scoped _root_.Topology _root_.unitInterval

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id
    (n : ℕ) (f : C(X, X)) {x y : X}
    (hf : _root_.Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set X))
    (hhom : f.Homotopic (.id X)) (w : integralSingularHomology n X) :
    integralRelativeHomologyMap n f hf (integralAbsoluteToRelative n ({x}ᶜ) w) =
      integralAbsoluteToRelative n ({y}ᶜ) w := by
  have h := congrArg
    (fun k : integralSingularHomology n X →ₗ[ℤ] integralRelativeHomology n ({y}ᶜ) => k w)
    (integralAbsoluteToRelative_natural n f hf)
  simp only [LinearMap.comp_apply] at h
  rw [← h, integralSingularHomologyMap_homotopic n hhom, integralSingularHomologyMap_id,
    LinearMap.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id

theorem integralRelativeHomologyMap_id_of_mapsTo (n : ℕ) (A : Set X)
    (h : _root_.Set.MapsTo (ContinuousMap.id X) A A) :
    integralRelativeHomologyMap n (ContinuousMap.id X) h = LinearMap.id := by
  unfold integralRelativeHomologyMap
  rw [integralRelativeChainMap_eq_id (ContinuousMap.id X) A h rfl,
    HomologicalComplex.homologyMap_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_id_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_id_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_id_of_mapsTo ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_id_of_mapsTo

theorem injective_integralRelativeHomologyMap_of_homeomorph (n : ℕ) (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (he : _root_.Set.MapsTo e A B) (he' : _root_.Set.MapsTo e.symm B A) :
    Function.Injective (integralRelativeHomologyMap n (⟨e, e.continuous⟩ : C(X, Y)) he) := by
  rw [← integralRelativeHomologyHomeomorphIso_hom n e A B he he']
  exact (integralRelativeHomologyHomeomorphIso n e A B he he').toLinearEquiv.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_integralRelativeHomologyMap_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_integralRelativeHomologyMap_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_integralRelativeHomologyMap_of_homeomorph ``Submission.DifferentialGeometry.Topology.injective_integralRelativeHomologyMap_of_homeomorph

theorem homotopic_addRight_id (c : EuclideanSpace ℝ (Fin 3)) :
    (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3))).Homotopic
      (ContinuousMap.id _) := by
  let F : C(I × EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun p => (p.2 : EuclideanSpace ℝ (Fin 3)) + (1 - (p.1 : ℝ)) • c, by fun_prop⟩
  exact ⟨{ toContinuousMap := F
           map_zero_left := fun x => by simp [F]
           map_one_left := fun x => by simp [F] }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopic_addRight_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopic_addRight_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopic_addRight_id ``Submission.DifferentialGeometry.Topology.homotopic_addRight_id

theorem mapsTo_addRight_compl (a c : EuclideanSpace ℝ (Fin 3)) :
    _root_.Set.MapsTo (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)))
      ({a}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) ({(a + c)}ᶜ) :=
  fun _ hz h => hz (add_right_cancel h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mapsTo_addRight_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mapsTo_addRight_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mapsTo_addRight_compl ``Submission.DifferentialGeometry.Topology.mapsTo_addRight_compl

theorem integralRelativeHomologyMap_addRight_absoluteToRelative
    (n : ℕ) (a c : EuclideanSpace ℝ (Fin 3))
    (w : integralSingularHomology n (EuclideanSpace ℝ (Fin 3))) :
    integralRelativeHomologyMap n
        (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)))
        (mapsTo_addRight_compl a c)
        (integralAbsoluteToRelative n ({a}ᶜ) w) =
      integralAbsoluteToRelative n ({(a + c)}ᶜ) w :=
  integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id n _ _
    (homotopic_addRight_id c) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_addRight_absoluteToRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_addRight_absoluteToRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_addRight_absoluteToRelative ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_addRight_absoluteToRelative

end DifferentialGeometry.Topology
