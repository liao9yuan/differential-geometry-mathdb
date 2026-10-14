import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

def IsUniformStandardLifetime (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ θ : ℝ, 0 ≤ θ → θ < τ →
    (∀ S : StandardSolution, ENNReal.ofReal θ < S.val.lifetime) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime

def uniformStandardLifetime : ℝ≥0∞ :=
  ⨆ τ : {τ : ℝ // IsUniformStandardLifetime τ}, ENNReal.ofReal τ.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime

theorem IsUniformStandardLifetime.mono {τ τ' : ℝ} (h : IsUniformStandardLifetime τ)
    (hτ' : 0 < τ') (hle : τ' ≤ τ) : IsUniformStandardLifetime τ' :=
  ⟨hτ', fun θ hθ hθτ => h.2 θ hθ (hθτ.trans_le hle)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.IsUniformStandardLifetime.mono

theorem le_uniformStandardLifetime (τ : ℝ) (hτ : IsUniformStandardLifetime τ) :
    ENNReal.ofReal τ ≤ uniformStandardLifetime :=
  le_iSup (fun r : {r : ℝ // IsUniformStandardLifetime r} => ENNReal.ofReal r.val) ⟨τ, hτ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.le_uniformStandardLifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.le_uniformStandardLifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.le_uniformStandardLifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.le_uniformStandardLifetime

theorem uniformStandardLifetime_slab (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) :
    (∀ S : StandardSolution, ENNReal.ofReal θ < S.val.lifetime) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.val.metric t) x 4 (metricRm04 (S.val.metric t) x)) ≤ K := by
  obtain ⟨τ, hτ⟩ := lt_iSup_iff.mp hlt
  exact τ.property.2 θ hθ ((ENNReal.ofReal_lt_ofReal_iff τ.property.1).mp hτ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_slab

theorem uniformStandardLifetime_le_lifetime (S : StandardSolution) :
    uniformStandardLifetime ≤ S.val.lifetime := by
  by_contra hn
  obtain ⟨θ, hθ, hST, hθT⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  exact (not_lt_of_gt hST) ((uniformStandardLifetime_slab θ hθ hθT).1 S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_lifetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_lifetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_lifetime ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_lifetime

theorem isUniformStandardLifetime_iff (τ : ℝ) :
    IsUniformStandardLifetime τ ↔ 0 < τ ∧ ENNReal.ofReal τ ≤ uniformStandardLifetime := by
  constructor
  · intro h
    exact ⟨h.1, le_uniformStandardLifetime τ h⟩
  · rintro ⟨hτ, hle⟩
    refine ⟨hτ, ?_⟩
    intro θ hθ hθτ
    exact uniformStandardLifetime_slab θ hθ
      (((ENNReal.ofReal_lt_ofReal_iff hτ).mpr hθτ).trans_le hle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isUniformStandardLifetime_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isUniformStandardLifetime_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isUniformStandardLifetime_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.isUniformStandardLifetime_iff

theorem uniformStandardLifetime_pos_iff :
    0 < uniformStandardLifetime ↔ ∃ τ : ℝ, IsUniformStandardLifetime τ := by
  constructor
  · intro h
    obtain ⟨τ, _⟩ := lt_iSup_iff.mp h
    exact ⟨τ.val, τ.property⟩
  · rintro ⟨τ, hτ⟩
    exact (ENNReal.ofReal_pos.mpr hτ.1).trans_le (le_uniformStandardLifetime τ hτ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_pos_iff
end DifferentialGeometry.PDE.RicciFlow
