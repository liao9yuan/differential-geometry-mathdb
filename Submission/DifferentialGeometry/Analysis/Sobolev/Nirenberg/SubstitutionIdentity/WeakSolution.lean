import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Localization
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open scoped _root_.InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ v, MemH01 v Omega →
      ∀ hv : MemW1pWitness 2 v Omega,
        bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    ∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
        ∫ x in Omega, f x * nirenbergTestFunction k h eta u x
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  let htest := MemW1pWitness.nirenbergTestFunction (d := d) hOmega hu heta heta_cpt k h hroom
  have hsrc := hweak (nirenbergTestFunction k h eta u)
    (memH01_nirenbergTestFunction (d := d) hOmega hu heta heta_cpt k h hroom)
    htest
  rw [bilinFormOfCoeff] at hsrc
  have htest_grad : ∀ x i, htest.weakGrad x i =
      diffQuot k (-h) (fun y =>
        (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
          2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
            diffQuot k h u y) x := by
    intro x i
    exact MemW1pWitness.nirenbergTestFunction_weakGrad_apply (d := d) hOmega hu heta heta_cpt k h hroom x i
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using (RCLike.inner_apply' a b)
  simpa [bilinFormIntegrandOfCoeff, PiLp.inner_apply,
    matMulE_apply, Matrix.mulVec, dotProduct, hscalar, htest_grad, mul_comm]
    using hsrc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction then
    throwError "Refusing to shadow existing declaration DeGiorgi.integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction ``Submission.DeGiorgi.integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction

theorem IsSolution.integral_sum_mul_diffQuot_eq_zero
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u : E → ℝ}
    (hsol : IsSolution A u)
    (hu : MemW1pWitness 2 u Omega)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ)
    (hroom : Metric.cthickening |h| (tsupport eta) ⊆ Omega) :
    ∫ x in Omega, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = 0 := by
  simpa using integral_sum_mul_diffQuot_eq_integral_mul_nirenbergTestFunction
    (f := fun _ => 0) hOmega hu
    (fun v hv0 hv => by
      simpa using hsol.bilinFormOfCoeff_eq_zero hOmega hu hv0 hv)
    heta heta_cpt k h hroom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero ``Submission.DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero

theorem IsSolution.integral_sum_mul_diffQuot_eq_zero_univ
    {A : EllipticCoeff d (Set.univ : Set E)} {u : E → ℝ}
    (hsol : IsSolution A u)
    (hu : MemW1pWitness 2 u Set.univ)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta) (k : Fin d) (h : ℝ) :
    ∫ x, ∑ i : Fin d,
        (∑ j : Fin d, A.a x i j * hu.weakGrad x j) *
          diffQuot k (-h) (fun y =>
            (eta y) ^ 2 * diffQuot k h (fun z => hu.weakGrad z i) y +
              2 * eta y * (fderiv ℝ eta y) (EuclideanSpace.single i 1) *
                diffQuot k h u y) x
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = 0 := by
  simpa only [Measure.restrict_univ] using
    hsol.integral_sum_mul_diffQuot_eq_zero isOpen_univ hu heta heta_cpt k h
      (Set.subset_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero_univ then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero_univ ``Submission.DeGiorgi.IsSolution.integral_sum_mul_diffQuot_eq_zero_univ

end DeGiorgi
