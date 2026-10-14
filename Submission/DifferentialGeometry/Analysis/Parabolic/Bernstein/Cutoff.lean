import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic

structure ShiCutoffLowerSupportAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T ε : Real)
    (χ : Real → M → Real)
    (t : Real) (x : M) where
  phi : Real → M → Real
  eq_at : phi t x = χ t x
  lower_nhds :
    ∀ᶠ p in 𝓝[spacetimeSlab (M := M) T] (t, x),
      0 ≤ phi p.1 p.2 ∧ phi p.1 p.2 ≤ χ p.1 p.2
  time_diff :
    DifferentiableWithinAt Real (fun s => phi s x) (Set.Icc 0 T) t
  space_diff_nhds :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (phi t) y
  grad_diff :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (phi t) y) x
  grad_sq_le :
    (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (phi t) x)
        (gradientFun (I := I) (G.metric t) (phi t) x) ≤
      ε * phi t x
  parabolic_le :
    parabolicOperatorWithDrift (I := I) G T
      (fun _ y => (0 : TangentSpace I y)) phi t x ≤ ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffLowerSupportAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffLowerSupportAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffLowerSupportAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffLowerSupportAt

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.Analysis.Parabolic

structure ParabolicCutoff
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T ε : Real) where
  chi : Real → M → Real
  support : Set M
  err_nonneg : 0 ≤ ε
  support_compact : IsCompact support
  support_zero :
    ∀ t, t ∈ Set.Icc 0 T → ∀ x, x ∉ support → chi t x = 0
  range :
    ∀ t, t ∈ Set.Icc 0 T → ∀ x, chi t x ∈ Set.Icc (0 : Real) 1
  joint_cont :
    ContinuousOn (fun p : Real × M ↦ chi p.1 p.2)
      (Set.Icc 0 T ×ˢ support)
  lowerSupport :
    ∀ t, t ∈ Set.Icc 0 T → 0 < t → ∀ x, 0 < chi t x →
      Nonempty (PDE.RicciFlow.ShiCutoffLowerSupportAt (I := I) G T ε chi t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff

theorem ParabolicCutoff.isCompact_slab
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T ε : Real}
    (cut : ParabolicCutoff (I := I) G T ε) :
    IsCompact (Set.Icc 0 T ×ˢ cut.support) :=
  isCompact_Icc.prod cut.support_compact

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.isCompact_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.isCompact_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.isCompact_slab ``Submission.DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.isCompact_slab

theorem ParabolicCutoff.mem_support_of_pos
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T ε t : Real}
    (cut : ParabolicCutoff (I := I) G T ε)
    (ht : t ∈ Set.Icc 0 T) {x : M} (hx : 0 < cut.chi t x) :
    x ∈ cut.support := by
  by_contra hmem
  rw [cut.support_zero t ht x hmem] at hx
  exact lt_irrefl 0 hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.mem_support_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.mem_support_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.mem_support_of_pos ``Submission.DifferentialGeometry.Analysis.Parabolic.ParabolicCutoff.mem_support_of_pos

end DifferentialGeometry.Analysis.Parabolic
