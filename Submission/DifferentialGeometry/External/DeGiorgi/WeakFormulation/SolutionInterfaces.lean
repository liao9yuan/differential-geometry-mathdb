-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.BilinearForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Weak Formulation: Solution Interfaces

This module packages weak problems together with the weak-solution,
subsolution, and supersolution interfaces built from the bilinear form.
-/

noncomputable section

open _root_.MeasureTheory
open scoped _root_.InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

/-- A weak elliptic Dirichlet problem on an open bounded domain. -/
structure WeakProblem where
  Ω : Set E
  hΩ : IsOpen Ω
  hΩ_bdd : Bornology.IsBounded Ω
  coeff : EllipticCoeff d Ω
  rhs : (E → ℝ) → ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.WeakProblem then
    throwError "Refusing to shadow existing declaration DeGiorgi.WeakProblem"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.WeakProblem ``Submission.DeGiorgi.WeakProblem

/-- `u` is a weak solution of the variational problem `P` if it lies in
`H₀¹(P.Ω)` and satisfies the weak identity against every `H₀¹` test function. -/
def IsWeakSolution (P : WeakProblem (d := d)) (u : E → ℝ) : Prop :=
  MemH01 u P.Ω ∧
  ∀ (hwu : MemW1pWitness 2 u P.Ω) (v : E → ℝ), MemH01 v P.Ω →
    ∀ (hwv : MemW1pWitness 2 v P.Ω),
      bilinFormOfCoeff P.coeff hwu hwv = P.rhs v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsWeakSolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsWeakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsWeakSolution ``Submission.DeGiorgi.IsWeakSolution

/-- `u` is a weak subsolution of `-div(A∇u) ≤ 0` on `Ω`. -/
def IsSubsolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → bilinFormOfCoeff A hu hφ ≤ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSubsolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSubsolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSubsolution ``Submission.DeGiorgi.IsSubsolution

/-- `u` is a weak supersolution of `-div(A∇u) ≥ 0` on `Ω`. -/
def IsSupersolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      (∀ x, 0 ≤ φ x) → 0 ≤ bilinFormOfCoeff A hu hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSupersolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSupersolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSupersolution ``Submission.DeGiorgi.IsSupersolution

/-- `u` is a weak solution of the homogeneous equation iff it is both a weak
subsolution and a weak supersolution. -/
def IsSolution {Ω : Set E} (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  IsSubsolution A u ∧ IsSupersolution A u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution ``Submission.DeGiorgi.IsSolution

/-- `u` is a local weak solution of the homogeneous equation on `Ω` if it lies
in `W^{1,2}(Ω)` and the bilinear form vanishes against every `H₀¹(Ω)` test
function. This is the equality-form local weak-solution interface used by the
Harnack and Holder statements. -/
def IsHomogeneousWeakSolution {Ω : Set E}
    (A : EllipticCoeff d Ω) (u : E → ℝ) : Prop :=
  MemW1p 2 u Ω ∧
  ∀ (hu : MemW1pWitness 2 u Ω)
    (φ : E → ℝ), MemH01 φ Ω →
    ∀ (hφ : MemW1pWitness 2 φ Ω),
      bilinFormOfCoeff A hu hφ = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsHomogeneousWeakSolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsHomogeneousWeakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsHomogeneousWeakSolution ``Submission.DeGiorgi.IsHomogeneousWeakSolution

/-- Extract Sobolev membership from a subsolution. -/
theorem isSubsolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSubsolution A u) : MemW1p 2 u Ω :=
  h.left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isSubsolution_memW1p then
    throwError "Refusing to shadow existing declaration DeGiorgi.isSubsolution_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isSubsolution_memW1p ``Submission.DeGiorgi.isSubsolution_memW1p

/-- Extract Sobolev membership from a supersolution. -/
theorem isSupersolution_memW1p {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsSupersolution A u) : MemW1p 2 u Ω :=
  h.left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isSupersolution_memW1p then
    throwError "Refusing to shadow existing declaration DeGiorgi.isSupersolution_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isSupersolution_memW1p ``Submission.DeGiorgi.isSupersolution_memW1p

/-- A homogeneous weak solution is a subsolution. -/
theorem isHomogeneousWeakSolution_isSubsolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSubsolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isHomogeneousWeakSolution_isSubsolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.isHomogeneousWeakSolution_isSubsolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isHomogeneousWeakSolution_isSubsolution ``Submission.DeGiorgi.isHomogeneousWeakSolution_isSubsolution

/-- A homogeneous weak solution is a supersolution. -/
theorem isHomogeneousWeakSolution_isSupersolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSupersolution A u := by
  refine ⟨h.1, ?_⟩
  intro hu φ hφ hφw hφ_nonneg
  have hEq : bilinFormOfCoeff A hu hφw = 0 := h.2 hu φ hφ hφw
  simp [hEq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isHomogeneousWeakSolution_isSupersolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.isHomogeneousWeakSolution_isSupersolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isHomogeneousWeakSolution_isSupersolution ``Submission.DeGiorgi.isHomogeneousWeakSolution_isSupersolution

/-- A homogeneous weak solution is both a subsolution and a supersolution. -/
theorem isHomogeneousWeakSolution_isSolution
    {Ω : Set E} {A : EllipticCoeff d Ω} {u : E → ℝ}
    (h : IsHomogeneousWeakSolution A u) :
    IsSolution A u :=
  ⟨isHomogeneousWeakSolution_isSubsolution h,
    isHomogeneousWeakSolution_isSupersolution h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isHomogeneousWeakSolution_isSolution then
    throwError "Refusing to shadow existing declaration DeGiorgi.isHomogeneousWeakSolution_isSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isHomogeneousWeakSolution_isSolution ``Submission.DeGiorgi.isHomogeneousWeakSolution_isSolution

end DeGiorgi
