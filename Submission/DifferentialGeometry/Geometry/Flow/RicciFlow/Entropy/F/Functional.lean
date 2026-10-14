import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.Formula
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.GradientFormula
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.Higher
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Components
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import Submission.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.LogDensity
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.RicciCoord
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {M : Type*}


variable {M : Type*}

def expNegPotentialDensity (potential : M -> Real) : M -> Real :=
  fun x => Real.exp (-(potential x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity

def expNegPotentialWeightedMeasure [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M)
    (potential : M -> Real) : _root_.MeasureTheory.Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (expNegPotentialDensity potential x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure

theorem expNegPotentialWeightedMeasure_integral_eq_base
    [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M) (potential integrand : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu) :
    (∫ x, integrand x ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, expNegPotentialDensity potential x * integrand x ∂mu := by
  rw [expNegPotentialWeightedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    integrand]
  apply _root_.MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnonneg : 0 ≤ expNegPotentialDensity potential x :=
    le_of_lt (Real.exp_pos _)
  simp [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure_integral_eq_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure_integral_eq_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure_integral_eq_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialWeightedMeasure_integral_eq_base

theorem expWeightedIBP_of_baseIntegral_zero [MeasurableSpace M]
    (mu : _root_.MeasureTheory.Measure M) (potential lapPotential gradPotentialNormSq : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu)
    (hbase :
      ∫ x,
        expNegPotentialDensity potential x *
          (lapPotential x - gradPotentialNormSq x)
        ∂mu = 0) :
    ∫ x, (lapPotential x - gradPotentialNormSq x)
      ∂(expNegPotentialWeightedMeasure mu potential) = 0 := by
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := mu) (potential := potential)
    (integrand := fun x : M => lapPotential x - gradPotentialNormSq x)
    hmeas]
  exact hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIBP_of_baseIntegral_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIBP_of_baseIntegral_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIBP_of_baseIntegral_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIBP_of_baseIntegral_zero

def fFunctionalBracket (scalarCurvature gradPotentialNormSq : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + gradPotentialNormSq x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalBracket

def fFunctionalClosedBracket (scalarCurvature lapPotential : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + lapPotential x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracket ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracket

def fFunctionalClosedBracketVariation
    (scalarCurvatureVariation lapPotentialVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + lapPotentialVariation x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracketVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracketVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracketVariation ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalClosedBracketVariation

def fFunctional [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
    ∂(expNegPotentialWeightedMeasure mu potential)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional

theorem fFunctional_eq_integral [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    fFunctional mu scalarCurvature gradPotentialNormSq potential =
      ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
        ∂(expNegPotentialWeightedMeasure mu potential) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional_eq_integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctional_eq_integral

def fFunctionalAlong [MeasurableSpace M] (mu : Real -> _root_.MeasureTheory.Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s => fFunctional (mu s) (scalarCurvature s) (gradPotentialNormSq s)
    (potential s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalAlong ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalAlong

def FFunctionalHasFirstVariationAt [MeasurableSpace M]
    (mu : Real -> _root_.MeasureTheory.Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential)
    firstVariation s0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.FFunctionalHasFirstVariationAt

def fFunctionalFirstVariation [MeasurableSpace M]
    (mu : Real -> _root_.MeasureTheory.Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential) s0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation

theorem fFunctionalFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> _root_.MeasureTheory.Measure M}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      FFunctionalHasFirstVariationAt mu scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    fFunctionalFirstVariation mu scalarCurvature gradPotentialNormSq potential s0 =
      firstVariation := by
  unfold fFunctionalFirstVariation FFunctionalHasFirstVariationAt at *
  exact h.deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation_eq_of_hasFirstVariationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation_eq_of_hasFirstVariationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation_eq_of_hasFirstVariationAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.fFunctionalFirstVariation_eq_of_hasFirstVariationAt

theorem expNegPotentialDensity_hasDerivAt
    {potentialPath : Real -> M -> Real} {s0 : Real}
    {potentialVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real => expNegPotentialDensity (potentialPath s) x)
      (-(potentialVariation x) *
        expNegPotentialDensity (potentialPath s0) x)
      s0 := by
  have h := (hpotential_deriv x).neg.exp
  simpa [expNegPotentialDensity, mul_comm, mul_left_comm, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expNegPotentialDensity_hasDerivAt

def expWeightedMeasureVariationFactor
    (potentialVariation metricVariationTrace : M -> Real) : M -> Real :=
  fun x => metricVariationTrace x / 2 - potentialVariation x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureVariationFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureVariationFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureVariationFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedMeasureVariationFactor

def expWeightedIntegralVariationIntegrand
    (potential potentialVariation metricVariationTrace phi phiVariation :
      M -> Real) :
    M -> Real :=
  fun x =>
    expNegPotentialDensity potential x *
      (phiVariation x +
        phi x *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIntegralVariationIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIntegralVariationIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIntegralVariationIntegrand ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.expWeightedIntegralVariationIntegrand

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
