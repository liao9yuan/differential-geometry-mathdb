/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem extend_interval_homeomorph {a b c d e f : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b < c) (hde : d ≤ e) (hef : e < f)
    (hg : IsPLHomeomorphOn g (_root_.Set.Icc a b) (_root_.Set.Icc d e)) (hgb : g b = e) :
    ∃ h : ℝ → ℝ, IsPLHomeomorphOn h (_root_.Set.Icc a c) (_root_.Set.Icc d f) ∧
      EqOn h g (_root_.Set.Icc a b) ∧ h c = f := by
  obtain ⟨q, hq, hqb, hqc⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints hbc hef
  have hcompat : _root_.Set.EqOn g q (_root_.Set.Icc a b ∩ _root_.Set.Icc b c) := by
    intro x hx
    have hxb : x = b := le_antisymm hx.1.2 hx.2.1
    rw [hxb, hgb, hqb]
  have hmeet : _root_.Set.SurjOn g (_root_.Set.Icc a b ∩ _root_.Set.Icc b c) (_root_.Set.Icc d e ∩ _root_.Set.Icc e f) := by
    intro y hy
    have hye : y = e := le_antisymm hy.1.2 hy.2.1
    exact ⟨b, ⟨⟨hab, le_rfl⟩, ⟨le_rfl, hbc.le⟩⟩, hgb.trans hye.symm⟩
  obtain ⟨h, hh, hhg, hhq⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hg hq hcompat hmeet
  rw [_root_.Set.Icc_union_Icc_eq_Icc hab hbc.le, _root_.Set.Icc_union_Icc_eq_Icc hde hef.le] at hh
  exact ⟨h, hh, hhg, (hhq ⟨hbc.le, le_rfl⟩).trans hqc⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.extend_interval_homeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.extend_interval_homeomorph target :: scope.openDecls } }

theorem exists_isPLHomeomorphOn_Icc_map_three_points
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : ℝ}
    (ha₀ : a₀ < a₁) (ha₁ : a₁ < a₂) (ha₂ : a₂ < a₃) (ha₃ : a₃ < a₄)
    (hb₀ : b₀ < b₁) (hb₁ : b₁ < b₂) (hb₂ : b₂ < b₃) (hb₃ : b₃ < b₄) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (_root_.Set.Icc a₀ a₄) (_root_.Set.Icc b₀ b₄) ∧
      f a₀ = b₀ ∧ f a₁ = b₁ ∧ f a₂ = b₂ ∧ f a₃ = b₃ ∧ f a₄ = b₄ := by
  obtain ⟨f₀, hf₀, hf₀l, hf₀r⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints ha₀ hb₀
  obtain ⟨f₁, hf₁, h₁₀, hf₁r⟩ :=
    extend_interval_homeomorph ha₀.le ha₁ hb₀.le hb₁ hf₀ hf₀r
  obtain ⟨f₂, hf₂, h₂₁, hf₂r⟩ := extend_interval_homeomorph
    (ha₀.le.trans ha₁.le) ha₂ (hb₀.le.trans hb₁.le) hb₂ hf₁ hf₁r
  obtain ⟨f₃, hf₃, h₃₂, hf₃r⟩ := extend_interval_homeomorph
    (ha₀.le.trans (ha₁.le.trans ha₂.le)) ha₃
    (hb₀.le.trans (hb₁.le.trans hb₂.le)) hb₃ hf₂ hf₂r
  refine ⟨f₃, hf₃, ?_, ?_, ?_, ?_, hf₃r⟩
  · exact (h₃₂ ⟨le_rfl, ha₀.le.trans (ha₁.le.trans ha₂.le)⟩).trans
      ((h₂₁ ⟨le_rfl, ha₀.le.trans ha₁.le⟩).trans
        ((h₁₀ ⟨le_rfl, ha₀.le⟩).trans hf₀l))
  · exact (h₃₂ ⟨ha₀.le, ha₁.le.trans ha₂.le⟩).trans
      ((h₂₁ ⟨ha₀.le, ha₁.le⟩).trans ((h₁₀ ⟨ha₀.le, le_rfl⟩).trans hf₀r))
  · exact (h₃₂ ⟨ha₀.le.trans ha₁.le, ha₂.le⟩).trans
      ((h₂₁ ⟨ha₀.le.trans ha₁.le, le_rfl⟩).trans hf₁r)
  · exact (h₃₂ ⟨ha₀.le.trans (ha₁.le.trans ha₂.le), le_rfl⟩).trans hf₂r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_map_three_points then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_map_three_points"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_map_three_points ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_Icc_map_three_points

theorem IsPLHomeomorphOn.exists_parametrization_three_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {γ : ℝ → E} {T : Set E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) T)
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1) :
    ∃ δ : ℝ → E, IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) T ∧
      δ 0 = γ 0 ∧ δ (1 / 4) = γ a ∧ δ (1 / 2) = γ b ∧
      δ (3 / 4) = γ c ∧ δ 1 = γ 1 := by
  obtain ⟨f, hf, hf₀, hf₁, hf₂, hf₃, hf₄⟩ :=
    exists_isPLHomeomorphOn_Icc_map_three_points
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 3 / 4) (by norm_num : (3 : ℝ) / 4 < 1)
      ha hab hbc hc
  exact ⟨γ ∘ f, hf.trans hγ, congrArg γ hf₀, congrArg γ hf₁, congrArg γ hf₂,
    congrArg γ hf₃, congrArg γ hf₄⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_parametrization_three_points then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_parametrization_three_points"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_parametrization_three_points ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_parametrization_three_points

end DifferentialGeometry.Topology.PiecewiseLinear
