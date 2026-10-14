/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X : Type*} [TopologicalSpace X] {A A₀ A₁ : Set X}

theorem IsAnnulusOn.isCompact (hann : IsAnnulusOn A A₀ A₁) : IsCompact A := by
  obtain ⟨φ, -, -⟩ := hann
  have : CompactSpace A := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact

theorem IsAnnulusOn.isCompact_first (hann : IsAnnulusOn A A₀ A₁) : IsCompact A₀ := by
  obtain ⟨φ, h₀, -⟩ := hann
  rw [h₀]
  apply IsCompact.image _ continuous_subtype_val
  apply IsCompact.image _ φ.continuous
  exact (isClosed_eq continuous_snd.subtype_val continuous_const).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_first ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_first

theorem IsAnnulusOn.isCompact_second (hann : IsAnnulusOn A A₀ A₁) : IsCompact A₁ := by
  obtain ⟨φ, -, h₁⟩ := hann
  rw [h₁]
  apply IsCompact.image _ continuous_subtype_val
  apply IsCompact.image _ φ.continuous
  exact (isClosed_eq continuous_snd.subtype_val continuous_const).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_second ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.isCompact_second

end DifferentialGeometry.Topology.PiecewiseLinear
