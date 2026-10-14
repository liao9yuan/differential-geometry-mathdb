import Submission.DifferentialGeometry.Topology.Handle.HalfBallRounding
import Submission.DifferentialGeometry.Topology.Diffeomorph.Graph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

open _root_.PartialDiffeomorph in
private noncomputable def cylinderCornerShear : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph.trans
    ((Diffeomorph.graphShear (f := fun _ : ℝ => (0 : ℝ))
      contDiff_const (contDiff_id.pow 2)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toDiffeomorph)

run_cmd do
  let target := ``Submission.PartialDiffeomorph.cylinderCornerShear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.cylinderCornerShear target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

open _root_.PartialDiffeomorph in
noncomputable def cylinderCorner (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
      (E × ℝ) (_root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) ∞ :=
  (halfBallCorner (n := n) r v).trans
    ((Diffeomorph.refl (𝓡 n) (_root_.Metric.sphere (0 : E) 1) ∞).prodCongr
      cylinderCornerShear).toPartialDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner ``Submission.PartialDiffeomorph.cylinderCorner

open _root_.PartialDiffeomorph in
@[simp] theorem cylinderCorner_apply (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) (p : E × ℝ) :
    cylinderCorner (n := n) r v p =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (r ^ 2 - ‖p.1‖ ^ 2, p.2)) := by
  change (_, (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 + (p.2 ^ 2 - 0), p.2)) = _
  congr 2
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_apply ``Submission.PartialDiffeomorph.cylinderCorner_apply

open _root_.PartialDiffeomorph in
@[simp] theorem cylinderCorner_symm_apply (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1)
    (p : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ)) :
    (cylinderCorner (n := n) r v).toPartialEquiv.symm p =
      (Real.sqrt (r ^ 2 - p.2.1) • p.1.val, p.2.2) := by
  change (Real.sqrt (r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2) • p.1.val, p.2.2) = _
  rw [show r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2 = r ^ 2 - p.2.1 by ring]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_symm_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_symm_apply ``Submission.PartialDiffeomorph.cylinderCorner_symm_apply

open _root_.PartialDiffeomorph in
@[simp] theorem cylinderCorner_source (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).source = {p : E × ℝ | p.1 ≠ 0} := by
  ext p
  change (p.1 ≠ 0 ∧ True) ↔ p.1 ≠ 0
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_source ``Submission.PartialDiffeomorph.cylinderCorner_source

open _root_.PartialDiffeomorph in
@[simp] theorem cylinderCorner_target (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).target = {p | p.2.1 < r ^ 2} := by
  ext p
  change (True ∧ 0 < r ^ 2 - (p.2.1 + -(p.2.2 ^ 2 - 0)) - p.2.2 ^ 2) ↔ _
  simp only [true_and, _root_.Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_target ``Submission.PartialDiffeomorph.cylinderCorner_target

open _root_.PartialDiffeomorph in
theorem cylinderCorner_isImage (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | ‖p.1‖ ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
      {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} := by
  intro p _
  change (0 ≤ (cylinderCorner (n := n) r v p).2.1 ∧
    0 ≤ (cylinderCorner (n := n) r v p).2.2) ↔ _
  rw [cylinderCorner_apply]
  exact and_congr (sub_nonneg) Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_isImage then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_isImage"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_isImage ``Submission.PartialDiffeomorph.cylinderCorner_isImage

open _root_.PartialDiffeomorph in
theorem cylinderCorner_isImage_boundary (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1) :
    (cylinderCorner (n := n) r v).toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | (‖p.1‖ ^ 2 ≤ r ^ 2 ∧ p.2 = 0) ∨
        (‖p.1‖ ^ 2 = r ^ 2 ∧ 0 ≤ p.2)}
      {p | (0 ≤ p.2.1 ∧ p.2.2 = 0) ∨ (p.2.1 = 0 ∧ 0 ≤ p.2.2)} := by
  intro p _
  change ((0 ≤ (cylinderCorner (n := n) r v p).2.1 ∧
    (cylinderCorner (n := n) r v p).2.2 = 0) ∨
    ((cylinderCorner (n := n) r v p).2.1 = 0 ∧
      0 ≤ (cylinderCorner (n := n) r v p).2.2)) ↔ _
  rw [cylinderCorner_apply]
  exact or_congr (and_congr sub_nonneg Iff.rfl)
    (and_congr (sub_eq_zero.trans eq_comm) Iff.rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_isImage_boundary then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_isImage_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_isImage_boundary ``Submission.PartialDiffeomorph.cylinderCorner_isImage_boundary

open _root_.PartialDiffeomorph in
theorem cylinderCorner_strip_subset_target (r : ℝ) (v : _root_.Metric.sphere (0 : E) 1)
    {ε : ℝ} (hε : ε < r ^ 2) :
    {p : _root_.Metric.sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      (cylinderCorner (n := n) r v).target := by
  rw [cylinderCorner_target]
  intro p hp
  exact lt_of_le_of_lt (by linarith [hp.2.1, hp.2.2]) hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.cylinderCorner_strip_subset_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.cylinderCorner_strip_subset_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.cylinderCorner_strip_subset_target ``Submission.PartialDiffeomorph.cylinderCorner_strip_subset_target

end PartialDiffeomorph
