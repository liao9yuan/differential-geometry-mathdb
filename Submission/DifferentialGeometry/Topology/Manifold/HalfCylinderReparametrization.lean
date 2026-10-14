import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.TopologicalSpace _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private abbrev positiveProduct : _root_.TopologicalSpace.Opens (M × ℝ) := ⟨univ ×ˢ _root_.Set.Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.positiveProduct
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.positiveProduct target :: scope.openDecls } }

variable (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (M × ℝ))
  (hfix : ∀ p : (M × ℝ), p.2 ≤ 0 → F p = p)

include hfix in
theorem halfCylinder_image_nonneg_iff (p : (M × ℝ)) : 0 ≤ (F p).2 ↔ 0 ≤ p.2 := by
  constructor
  · intro hp
    by_contra hn
    have hneg : p.2 < 0 := lt_of_not_ge hn
    rw [hfix p hneg.le] at hp
    exact (not_le_of_gt hneg) hp
  · intro hp
    by_contra hn
    have hneg : (F p).2 < 0 := lt_of_not_ge hn
    have heq : F p = p := F.injective (hfix (F p) hneg.le)
    rw [heq] at hneg
    exact (not_lt_of_ge hp) hneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.halfCylinder_image_nonneg_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.halfCylinder_image_nonneg_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.halfCylinder_image_nonneg_iff ``Submission.DifferentialGeometry.Topology.Manifold.halfCylinder_image_nonneg_iff

include hfix in
theorem halfCylinder_image_pos_iff (p : (M × ℝ)) : 0 < (F p).2 ↔ 0 < p.2 := by
  have hiff : (F p).2 ≤ 0 ↔ p.2 ≤ 0 := by
    constructor
    · intro hp
      have heq : F p = p := F.injective (hfix (F p) hp)
      exact heq ▸ hp
    · intro hp
      rw [hfix p hp]
      exact hp
  exact not_le.symm.trans (hiff.not.trans not_le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.halfCylinder_image_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.halfCylinder_image_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.halfCylinder_image_pos_iff ``Submission.DifferentialGeometry.Topology.Manifold.halfCylinder_image_pos_iff

def halfCylinderHomeomorph : {p : M × ℝ // 0 ≤ p.2} ≃ₜ {p : M × ℝ // 0 ≤ p.2} :=
  F.toHomeomorph.subtype (fun p => (halfCylinder_image_nonneg_iff F hfix p).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.halfCylinderHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.halfCylinderHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.halfCylinderHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.halfCylinderHomeomorph

def positiveCylinderDiffeomorph : (positiveProduct (M := M)) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (positiveProduct (M := M)) where
  toEquiv := (F.toHomeomorph.subtype (fun p => by
    change (True ∧ 0 < p.2) ↔ (True ∧ 0 < (F p).2)
    exact and_congr_right fun _ => (halfCylinder_image_pos_iff F hfix p).symm)).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (positiveProduct (M := M)) _).mp
    exact F.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (positiveProduct (M := M)) _).mp
    exact F.symm.contMDiff.comp contMDiff_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.positiveCylinderDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.positiveCylinderDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.positiveCylinderDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.positiveCylinderDiffeomorph

theorem range_comp_halfCylinder
    {X : Type*} (f : {p : M × ℝ // 0 ≤ p.2} → X) :
    range (f ∘ halfCylinderHomeomorph F hfix) = _root_.Set.range f :=
  (halfCylinderHomeomorph F hfix).surjective.range_comp f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.range_comp_halfCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.range_comp_halfCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.range_comp_halfCylinder ``Submission.DifferentialGeometry.Topology.Manifold.range_comp_halfCylinder


theorem exists_axial_bound_of_compact_support
    (K : Set (M × ℝ)) (hK : IsCompact K) (hF : _root_.Set.EqOn F id Kᶜ) :
    ∃ b : ℝ, ∀ q : (M × ℝ), b ≤ q.2 → F q = q := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_snd.continuousOn
  refine ⟨B + 1, ?_⟩
  intro q hq
  apply hF
  intro hqK
  have hle := hB (_root_.Set.mem_image_of_mem Prod.snd hqK)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_axial_bound_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_axial_bound_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_axial_bound_of_compact_support ``Submission.DifferentialGeometry.Topology.Manifold.exists_axial_bound_of_compact_support

end DifferentialGeometry.Topology.Manifold
