import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Topology
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {X : Type*}

theorem tendsto_fixedPoint_of_tendsto_apply [MetricSpace X] [Nonempty X] [CompleteSpace X]
    {Φ : X → X} {κ : ℝ≥0} (hΦ : ContractingWith κ Φ)
    {Q : ℕ → X → X} (hQΦ : ∀ N, ContractingWith κ (Q N ∘ Φ))
    (hQ : ∀ x, _root_.Filter.Tendsto (fun N => Q N x) _root_.Filter.atTop (𝓝 x)) :
    _root_.Filter.Tendsto (fun N => ContractingWith.fixedPoint (Q N ∘ Φ) (hQΦ N)) _root_.Filter.atTop
      (𝓝 (ContractingWith.fixedPoint Φ hΦ)) := by
  set a := ContractingWith.fixedPoint Φ hΦ with ha
  have hfix : Φ a = a := hΦ.fixedPoint_isFixedPt
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun N => _root_.Dist.dist a (Q N a) / (1 - (κ : ℝ)))
    (fun N => dist_nonneg) ?_ ?_
  · intro N
    have hcomp : (Q N ∘ Φ) a = Q N a := by
      simp only [Function.comp_apply, hfix]
    have h1 := (hQΦ N).dist_fixedPoint_le a
    rw [hcomp] at h1
    rw [dist_comm]
    exact h1
  · have hd : _root_.Filter.Tendsto (fun N => _root_.Dist.dist a (Q N a)) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_const_nhds (x := a) (f := _root_.Filter.atTop)).dist (hQ a)
      simpa using h
    simpa using hd.div_const (1 - (κ : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_fixedPoint_of_tendsto_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_fixedPoint_of_tendsto_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_fixedPoint_of_tendsto_apply ``Submission.DifferentialGeometry.Analysis.tendsto_fixedPoint_of_tendsto_apply

theorem tendsto_fixedPoint_of_projected_contraction
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {Φ : X → X} {κ : ℝ≥0} (hΦ : ContractingWith κ Φ)
    (P : ℕ → (X →L[ℝ] X)) (hP : ∀ x, _root_.Filter.Tendsto (fun N => P N x) _root_.Filter.atTop (𝓝 x))
    (hPΦ : ∀ N, ContractingWith κ (⇑(P N) ∘ Φ)) :
    _root_.Filter.Tendsto (fun N => ContractingWith.fixedPoint (⇑(P N) ∘ Φ) (hPΦ N)) _root_.Filter.atTop
      (𝓝 (ContractingWith.fixedPoint Φ hΦ)) :=
  tendsto_fixedPoint_of_tendsto_apply (Q := fun N => ⇑(P N)) hΦ hPΦ hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction ``Submission.DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction

end DifferentialGeometry.Analysis
