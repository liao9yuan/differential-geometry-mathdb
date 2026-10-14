import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'} {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P] {n : WithTop ℕ∞}

open _root_.PartialDiffeomorph in
theorem trans_apply (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n)
    (x : M) : (Φ.trans Ψ) x = Ψ (Φ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.trans_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.trans_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.trans_apply ``Submission.PartialDiffeomorph.trans_apply

open _root_.PartialDiffeomorph in
theorem trans_source (Φ : PartialDiffeomorph I J M N n) (Ψ : PartialDiffeomorph J K N P n) :
    (Φ.trans Ψ).source = Φ.source ∩ Φ ⁻¹' Ψ.source := by
  rw [show (Φ.trans Ψ).source = (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source from rfl]
  exact PartialEquiv.trans_source _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.trans_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.trans_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.trans_source ``Submission.PartialDiffeomorph.trans_source

open _root_.PartialDiffeomorph in
theorem symm_source (Φ : PartialDiffeomorph I J M N n) : Φ.symm.source = Φ.target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.symm_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.symm_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.symm_source ``Submission.PartialDiffeomorph.symm_source

open _root_.PartialDiffeomorph in
theorem symm_target (Φ : PartialDiffeomorph I J M N n) : Φ.symm.target = Φ.source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.symm_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.symm_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.symm_target ``Submission.PartialDiffeomorph.symm_target

open _root_.PartialDiffeomorph in
theorem symm_toPartialEquiv_source (Φ : PartialDiffeomorph I J M N n) :
    Φ.symm.toPartialEquiv.source = Φ.target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.symm_toPartialEquiv_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.symm_toPartialEquiv_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.symm_toPartialEquiv_source ``Submission.PartialDiffeomorph.symm_toPartialEquiv_source

open _root_.PartialDiffeomorph in
theorem symm_toPartialEquiv_target (Φ : PartialDiffeomorph I J M N n) :
    Φ.symm.toPartialEquiv.target = Φ.source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.symm_toPartialEquiv_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.symm_toPartialEquiv_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.symm_toPartialEquiv_target ``Submission.PartialDiffeomorph.symm_toPartialEquiv_target

open _root_.PartialDiffeomorph in
theorem symm_apply_apply (Φ : PartialDiffeomorph I J M N n) {x : M} (hx : x ∈ Φ.source) :
    Φ.symm (Φ x) = x := Φ.toPartialEquiv.left_inv hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.symm_apply_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.symm_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.symm_apply_apply ``Submission.PartialDiffeomorph.symm_apply_apply

open _root_.PartialDiffeomorph in
theorem apply_symm_apply (Φ : PartialDiffeomorph I J M N n) {y : N} (hy : y ∈ Φ.target) :
    Φ (Φ.symm y) = y := Φ.toPartialEquiv.right_inv hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.apply_symm_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.apply_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.apply_symm_apply ``Submission.PartialDiffeomorph.apply_symm_apply

end PartialDiffeomorph
