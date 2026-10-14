import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fin.SuccPred

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Function

namespace DifferentialGeometry.Geometry.Topology

def HasAtLeastEnds (X : Type*) [TopologicalSpace X] (k : ℕ) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∃ x : Fin k → X,
    (∀ i, x i ∉ K) ∧ _root_.Function.Injective (fun i => connectedComponentIn Kᶜ (x i)) ∧
      ∀ i, ¬ IsCompact (closure (connectedComponentIn Kᶜ (x i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.HasAtLeastEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.HasAtLeastEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.HasAtLeastEnds ``Submission.DifferentialGeometry.Geometry.Topology.HasAtLeastEnds


def HasExactlyEnds (X : Type*) [TopologicalSpace X] (k : ℕ) : Prop :=
  HasAtLeastEnds X k ∧ ¬ HasAtLeastEnds X (k + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.HasExactlyEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.HasExactlyEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.HasExactlyEnds ``Submission.DifferentialGeometry.Geometry.Topology.HasExactlyEnds


def HasAtMostTwoEnds (X : Type*) [TopologicalSpace X] : Prop :=
  ¬ HasAtLeastEnds X 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.HasAtMostTwoEnds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.HasAtMostTwoEnds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.HasAtMostTwoEnds ``Submission.DifferentialGeometry.Geometry.Topology.HasAtMostTwoEnds

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


theorem HasAtLeastEnds.mono {k l : ℕ} (h : HasAtLeastEnds X l) (hkl : k ≤ l) :
    HasAtLeastEnds X k := by
  obtain ⟨K, hK, x, hx, hinj, hnc⟩ := h
  exact ⟨K, hK, x ∘ Fin.castLE hkl, fun i => hx (Fin.castLE hkl i),
    hinj.comp (Fin.castLE_injective hkl), fun i => hnc (Fin.castLE hkl i)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Topology.HasAtLeastEnds
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.HasAtLeastEnds.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.HasAtLeastEnds.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.HasAtLeastEnds.mono ``Submission.DifferentialGeometry.Geometry.Topology.HasAtLeastEnds.mono

private theorem hasAtLeastEnds_map (e : X ≃ₜ Y) {k : ℕ} (h : HasAtLeastEnds X k) :
    HasAtLeastEnds Y k := by
  obtain ⟨K, hK, x, hx, hinj, hnc⟩ := h
  have hc (i : Fin k) : e '' connectedComponentIn Kᶜ (x i) =
      connectedComponentIn (e '' K)ᶜ (e (x i)) := by
    simpa only [_root_.Set.image_compl_eq e.bijective] using
      e.image_connectedComponentIn (s := Kᶜ) (x := x i) (hx i)
  refine ⟨e '' K, hK.image e.continuous, e ∘ x, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha, heq⟩ := hi
    exact hx i (e.injective heq ▸ ha)
  · intro i j hij
    apply hinj
    apply (Set.image_injective.mpr e.injective)
    rw [hc i, hc j]
    exact hij
  · intro i hi
    apply hnc i
    apply e.isCompact_image.mp
    rw [e.image_closure, hc i]
    exact hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_map target :: scope.openDecls } }

theorem hasAtLeastEnds_homeomorph_iff (e : X ≃ₜ Y) (k : ℕ) :
    HasAtLeastEnds X k ↔ HasAtLeastEnds Y k :=
  ⟨hasAtLeastEnds_map e, hasAtLeastEnds_map e.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_homeomorph_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_homeomorph_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_homeomorph_iff ``Submission.DifferentialGeometry.Geometry.Topology.hasAtLeastEnds_homeomorph_iff


theorem hasExactlyEnds_homeomorph_iff (e : X ≃ₜ Y) (k : ℕ) :
    HasExactlyEnds X k ↔ HasExactlyEnds Y k := by
  simp only [HasExactlyEnds, hasAtLeastEnds_homeomorph_iff e]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasExactlyEnds_homeomorph_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasExactlyEnds_homeomorph_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasExactlyEnds_homeomorph_iff ``Submission.DifferentialGeometry.Geometry.Topology.hasExactlyEnds_homeomorph_iff


theorem hasAtMostTwoEnds_homeomorph_iff (e : X ≃ₜ Y) :
    HasAtMostTwoEnds X ↔ HasAtMostTwoEnds Y := by
  simp only [HasAtMostTwoEnds, hasAtLeastEnds_homeomorph_iff e]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_homeomorph_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_homeomorph_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_homeomorph_iff ``Submission.DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_homeomorph_iff


theorem not_hasAtLeastEnds_of_compact [CompactSpace X] {k : ℕ} (hk : 0 < k) :
    ¬ HasAtLeastEnds X k := by
  rintro ⟨K, _, x, _, _, hnc⟩
  exact hnc ⟨0, hk⟩ isClosed_closure.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.not_hasAtLeastEnds_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.not_hasAtLeastEnds_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.not_hasAtLeastEnds_of_compact ``Submission.DifferentialGeometry.Geometry.Topology.not_hasAtLeastEnds_of_compact

theorem hasAtMostTwoEnds_of_not_hasAtLeastEnds_two (h : ¬ HasAtLeastEnds X 2) :
    HasAtMostTwoEnds X := fun hthree => h (hthree.mono (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_of_not_hasAtLeastEnds_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_of_not_hasAtLeastEnds_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_of_not_hasAtLeastEnds_two ``Submission.DifferentialGeometry.Geometry.Topology.hasAtMostTwoEnds_of_not_hasAtLeastEnds_two

end DifferentialGeometry.Geometry.Topology
