import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.BilinearForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.RealInnerProductSpace

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem matMulE_one (v : V) : matMulE 1 v = v := by
  ext i
  simp only [matMulE_apply, Matrix.one_mulVec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.matMulE_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.matMulE_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.matMulE_one ``Submission.DeGiorgi.matMulE_one

def EllipticCoeff.identity (d : ℕ) [NeZero d] (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    EllipticCoeff d Ω where
  a := fun _ => 1
  lam := 1
  Λ := 1
  measurable_comp := fun _ _ => measurable_const
  hlam := zero_lt_one
  hΛ := le_rfl
  coercive := Eventually.of_forall fun _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]
  coercive_inv := Eventually.of_forall fun _ v => by
    rw [inv_one, one_mul, inv_one, matMulE_one, real_inner_self_eq_norm_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.identity then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.identity ``Submission.DeGiorgi.EllipticCoeff.identity

theorem EllipticCoeff.identity_a [NeZero d] (Ω : Set V) (x : V) :
    (EllipticCoeff.identity d Ω).a x = 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.identity_a then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.identity_a"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.identity_a ``Submission.DeGiorgi.EllipticCoeff.identity_a

theorem EllipticCoeff.identity_lam [NeZero d] (Ω : Set V) :
    (EllipticCoeff.identity d Ω).lam = 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.identity_lam then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.identity_lam"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.identity_lam ``Submission.DeGiorgi.EllipticCoeff.identity_lam

theorem EllipticCoeff.identity_Λ [NeZero d] (Ω : Set V) :
    (EllipticCoeff.identity d Ω).Λ = 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.EllipticCoeff.identity_Λ then
    throwError "Refusing to shadow existing declaration DeGiorgi.EllipticCoeff.identity_Λ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.EllipticCoeff.identity_Λ ``Submission.DeGiorgi.EllipticCoeff.identity_Λ

theorem bilinFormOfCoeff_identity [NeZero d] {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    bilinFormOfCoeff (EllipticCoeff.identity d Ω) hu hv =
      ∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (hv.weakGrad x) := by
  simp only [bilinFormOfCoeff, bilinFormIntegrandOfCoeff, EllipticCoeff.identity, matMulE_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.bilinFormOfCoeff_identity then
    throwError "Refusing to shadow existing declaration DeGiorgi.bilinFormOfCoeff_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.bilinFormOfCoeff_identity ``Submission.DeGiorgi.bilinFormOfCoeff_identity

end DeGiorgi

end
