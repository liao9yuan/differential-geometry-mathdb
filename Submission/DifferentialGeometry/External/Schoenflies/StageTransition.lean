/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.FiniteTransferTarget

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The common output of one transferred stage

Both directions of finite transfer produce the four pieces of data needed between consecutive
matched cellulations: compatible source and target refinements, growth of the realized source
skeleton, and agreement of the new skeleton homeomorphism with the old one.  `StageTransition`
packages that shared output and proves that transitions compose.

## Blueprint

* `Schoenflies.StageTransition` — one step of the quantitative-refinement recursion, stripped of
  the particular ambient graph used to construct it.
* `Schoenflies.IsPartialTransferOf.stageTransition`,
  `Schoenflies.IsTargetPartialTransferOf.stageTransition` — both finite-transfer directions
  expose the same stage interface.
* `Schoenflies.StageTransition.trans` — consecutive transferred refinements compose.
-/

open _root_.Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The information about consecutive generated pairs consumed by `StageSequence`. -/
structure StageTransition
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (par : γ → γ) : Prop where
  /-- The new source realization refines the preceding source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The target realizations refine along the same abstract parent map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The realized source skeleton grows. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- The new skeleton homeomorphism extends the preceding one. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StageTransition then
    throwError "Refusing to shadow existing declaration Schoenflies.StageTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StageTransition ``Submission.Schoenflies.StageTransition

namespace StageTransition

variable {P Q T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {par₁ par₂ : γ → γ}

/-- Target skeletons grow as well.  This follows from source-skeleton growth and agreement of
the two skeleton homeomorphisms on the old source skeleton. -/
theorem targetSkeletonSet_subset {par : γ → γ}
    (h : StageTransition T P par) : P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  rw [← P.homeo.image_skeletonSet, ← T.homeo.image_skeletonSet]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h.sourceSkeletonSet_subset hx, h.homeo_eqOn hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StageTransition.targetSkeletonSet_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.StageTransition.targetSkeletonSet_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StageTransition.targetSkeletonSet_subset ``Submission.Schoenflies.StageTransition.targetSkeletonSet_subset

/-- Consecutive stage transitions compose their parent maps and their nesting data. -/
theorem trans (h₂ : StageTransition T Q par₂) (h₁ : StageTransition Q P par₁) :
    StageTransition T P (par₁ ∘ par₂) where
  refines_src := h₂.refines_src.trans h₁.refines_src
  refines_tgt := h₂.refines_tgt.trans h₁.refines_tgt
  sourceSkeletonSet_subset :=
    h₁.sourceSkeletonSet_subset.trans h₂.sourceSkeletonSet_subset
  homeo_eqOn := by
    intro x hx
    calc
      T.homeo.toFun x = Q.homeo.toFun x :=
        h₂.homeo_eqOn (h₁.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := h₁.homeo_eqOn hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StageTransition.trans then
    throwError "Refusing to shadow existing declaration Schoenflies.StageTransition.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StageTransition.trans ``Submission.Schoenflies.StageTransition.trans

end StageTransition

/-- Direction (a)'s induction invariant supplies one stage transition. -/
theorem IsPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsPartialTransferOf.stageTransition then
    throwError "Refusing to shadow existing declaration Schoenflies.IsPartialTransferOf.stageTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsPartialTransferOf.stageTransition ``Submission.Schoenflies.IsPartialTransferOf.stageTransition

/-- Direction (b)'s induction invariant supplies the identical stage transition. -/
theorem IsTargetPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsTargetPartialTransferOf.stageTransition then
    throwError "Refusing to shadow existing declaration Schoenflies.IsTargetPartialTransferOf.stageTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsTargetPartialTransferOf.stageTransition ``Submission.Schoenflies.IsTargetPartialTransferOf.stageTransition

/-- The admissible conclusion of direction (a) forgets to the same stage transition. -/
theorem IsTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsPartialTransferOf.stageTransition

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsTransferOf.stageTransition then
    throwError "Refusing to shadow existing declaration Schoenflies.IsTransferOf.stageTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsTransferOf.stageTransition ``Submission.Schoenflies.IsTransferOf.stageTransition

/-- The admissible conclusion of direction (b) forgets to the same stage transition. -/
theorem IsTargetTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsTargetPartialTransferOf.stageTransition

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsTargetTransferOf.stageTransition then
    throwError "Refusing to shadow existing declaration Schoenflies.IsTargetTransferOf.stageTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsTargetTransferOf.stageTransition ``Submission.Schoenflies.IsTargetTransferOf.stageTransition

end Schoenflies
