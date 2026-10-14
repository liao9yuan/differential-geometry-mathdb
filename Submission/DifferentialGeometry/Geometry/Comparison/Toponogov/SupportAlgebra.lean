/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.Convexity
import Mathlib.Analysis.Calculus.Deriv.Pow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Toponogov

def lowerSupportAt_sq_sub_sq_of_energy
    {distance energy energyDeriv : ℝ → ℝ} {J U : Set ℝ}
    {r₀ L energySecond : ℝ}
    (hU : U ∈ 𝓝 r₀) (hUJ : U ⊆ J)
    (hmajor : ∀ r ∈ U, distance r ^ 2 ≤ L * energy r)
    (hcontact : distance r₀ ^ 2 = L * energy r₀)
    (henergy : ∀ r ∈ U, HasDerivAt energy (energyDeriv r) r)
    (henergy' : HasDerivAt energyDeriv energySecond r₀)
    (hsecond : L * energySecond ≤ 2) :
    LowerSupportAt (fun r ↦ r ^ 2 - distance r ^ 2) J r₀ := by
  refine
    { support := fun r ↦ r ^ 2 - L * energy r
      supportDeriv := fun r ↦ 2 * r - L * energyDeriv r
      supportSecondDeriv := 2 - L * energySecond
      domain := U
      domain_mem_nhds := hU
      domain_subset := hUJ
      support_le := ?_
      support_eq := ?_
      hasDerivAt_support := ?_
      hasDerivAt_supportDeriv := ?_
      supportSecondDeriv_nonneg := ?_ }
  · intro r hr
    nlinarith [hmajor r hr]
  · nlinarith [hcontact]
  · intro r hr
    convert! (hasDerivAt_pow 2 r).sub ((henergy r hr).const_mul L) using 1
    all_goals ring
  · convert! ((hasDerivAt_id r₀).const_mul 2).sub
      (henergy'.const_mul L) using 1
    all_goals ring
  · linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_energy ``Submission.DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_energy

def lowerSupportAt_sq_sub_sq_of_zero
    {distance : ℝ → ℝ} {J U : Set ℝ} {r₀ : ℝ}
    (hU : U ∈ 𝓝 r₀) (hUJ : U ⊆ J)
    (hdistance_nonneg : ∀ r ∈ U, 0 ≤ distance r)
    (hdistance_le : ∀ r ∈ U, distance r ≤ |r - r₀|)
    (hdistance_zero : distance r₀ = 0) :
    LowerSupportAt (fun r ↦ r ^ 2 - distance r ^ 2) J r₀ := by
  refine
    { support := fun r ↦ 2 * r₀ * r - r₀ ^ 2
      supportDeriv := fun _ ↦ 2 * r₀
      supportSecondDeriv := 0
      domain := U
      domain_mem_nhds := hU
      domain_subset := hUJ
      support_le := ?_
      support_eq := ?_
      hasDerivAt_support := ?_
      hasDerivAt_supportDeriv := ?_
      supportSecondDeriv_nonneg := le_rfl }
  · intro r hr
    have hsquare : distance r ^ 2 ≤ |r - r₀| ^ 2 :=
      (sq_le_sq₀ (hdistance_nonneg r hr) (abs_nonneg _)).2
        (hdistance_le r hr)
    rw [sq_abs] at hsquare
    nlinarith
  · rw [hdistance_zero]
    ring
  · intro r _hr
    convert! ((hasDerivAt_id r).const_mul (2 * r₀)).sub_const (r₀ ^ 2) using 1
    all_goals ring
  · exact hasDerivAt_const r₀ (2 * r₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_zero ``Submission.DifferentialGeometry.Toponogov.lowerSupportAt_sq_sub_sq_of_zero

end DifferentialGeometry.Toponogov
