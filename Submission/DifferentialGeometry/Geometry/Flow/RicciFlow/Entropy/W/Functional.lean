import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.MeasureTheory

variable {M : Type*}

def perelmanDensityPrefactor (n : Nat) (tau : Real) : Real :=
  Real.rpow (4 * Real.pi * tau) (-(n : Real) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensityPrefactor

def perelmanDensity (n : Nat) (tau : Real) (potential : M -> Real) : M -> Real :=
  fun x => perelmanDensityPrefactor n tau * Real.exp (-(potential x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity

def perelmanWeightedMeasure [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M) (n : Nat)
    (tau : Real) (potential : M -> Real) : _root_.MeasureTheory.Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (perelmanDensity n tau potential x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanWeightedMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanWeightedMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanWeightedMeasure ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanWeightedMeasure

def wEntropyBracket (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : M -> Real :=
  fun x =>
    tau * (scalarCurvature x + gradPotentialNormSq x) + potential x - (n : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket

def wFunctional [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M) (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
    ∂(perelmanWeightedMeasure mu n tau potential)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional

theorem wFunctional_eq_integral [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M) (n : Nat)
    (tau : Real) (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂(perelmanWeightedMeasure mu n tau potential) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_eq_integral ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_eq_integral

theorem wFunctional_base [MeasurableSpace M]
    (mu : _root_.MeasureTheory.Measure M) (n : Nat) (tau : Real)
    (scalarCurvature gradPotentialNormSq potential : M -> Real)
    (htau : 0 ≤ tau)
    (hmeas : AEMeasurable
      (fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x)) mu) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      ∫ x, perelmanDensity n tau potential x *
        wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x ∂mu := by
  unfold wFunctional perelmanWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hnonneg : 0 ≤ perelmanDensity n tau potential x := by
    unfold perelmanDensity perelmanDensityPrefactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) htau) _)
      (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_base ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_base

private theorem wEntropyBracket_scale_eq {n : Nat} {tau c : Real}
    {scalarCurvature gradPotentialNormSq scaledScalarCurvature
      scaledGradPotentialNormSq potential : M -> Real}
    (hscalar : ∀ x : M, c * scaledScalarCurvature x = scalarCurvature x)
    (hgrad : ∀ x : M, c * scaledGradPotentialNormSq x = gradPotentialNormSq x)
    (x : M) :
    wEntropyBracket n (c * tau) scaledScalarCurvature
        scaledGradPotentialNormSq potential x =
      wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x := by
  unfold wEntropyBracket
  have hmain :
      (c * tau) * (scaledScalarCurvature x + scaledGradPotentialNormSq x) =
        tau * (scalarCurvature x + gradPotentialNormSq x) := by
    calc
      (c * tau) * (scaledScalarCurvature x + scaledGradPotentialNormSq x)
          = tau * (c * scaledScalarCurvature x + c * scaledGradPotentialNormSq x) := by
            ring
      _ = tau * (scalarCurvature x + gradPotentialNormSq x) := by
            rw [hscalar x, hgrad x]
  rw [hmain]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket_scale_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyBracket_scale_eq target :: scope.openDecls } }

theorem wFunctional_scale_invariant_of_weightedMeasure_eq [MeasurableSpace M]
    {mu scaledMu : _root_.MeasureTheory.Measure M} {n : Nat} {tau c : Real}
    {scalarCurvature gradPotentialNormSq scaledScalarCurvature
      scaledGradPotentialNormSq potential : M -> Real}
    (hmeasure :
      perelmanWeightedMeasure scaledMu n (c * tau) potential =
        perelmanWeightedMeasure mu n tau potential)
    (hscalar : ∀ x : M, c * scaledScalarCurvature x = scalarCurvature x)
    (hgrad : ∀ x : M, c * scaledGradPotentialNormSq x = gradPotentialNormSq x) :
    wFunctional scaledMu n (c * tau) scaledScalarCurvature
        scaledGradPotentialNormSq potential =
      wFunctional mu n tau scalarCurvature gradPotentialNormSq potential := by
  unfold wFunctional
  rw [hmeasure]
  exact _root_.MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall fun x =>
    wEntropyBracket_scale_eq (M := M) hscalar hgrad x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_scale_invariant_of_weightedMeasure_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_scale_invariant_of_weightedMeasure_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_scale_invariant_of_weightedMeasure_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_scale_invariant_of_weightedMeasure_eq

theorem wFunctional_diffeomorphism_invariant_of_map [MeasurableSpace M]
    {mu pullbackMu : _root_.MeasureTheory.Measure M} {n : Nat} {tau : Real}
    {scalarCurvature gradPotentialNormSq potential : M -> Real} (phi : M -> M)
    (hphi :
      AEMeasurable phi
        (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))))
    (hbracket :
      _root_.MeasureTheory.AEStronglyMeasurable
        (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)
        (perelmanWeightedMeasure mu n tau potential))
    (hmeasure :
      Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))) =
        perelmanWeightedMeasure mu n tau potential) :
    wFunctional mu n tau scalarCurvature gradPotentialNormSq potential =
      wFunctional pullbackMu n tau (fun x => scalarCurvature (phi x))
        (fun x => gradPotentialNormSq (phi x)) (fun x => potential (phi x)) := by
  unfold wFunctional
  have hbracket_map :
      _root_.MeasureTheory.AEStronglyMeasurable
        (wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential)
        (Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)))) := by
    rw [hmeasure]
    exact hbracket
  calc
    (∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂perelmanWeightedMeasure mu n tau potential)
        =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential x
        ∂Measure.map phi
          (perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x))) := by
        rw [hmeasure]
    _ =
      ∫ x, wEntropyBracket n tau scalarCurvature gradPotentialNormSq potential (phi x)
        ∂perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)) :=
        MeasureTheory.integral_map hphi hbracket_map
    _ =
      ∫ x, wEntropyBracket n tau (fun y => scalarCurvature (phi y))
          (fun y => gradPotentialNormSq (phi y)) (fun y => potential (phi y)) x
        ∂perelmanWeightedMeasure pullbackMu n tau (fun x => potential (phi x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_diffeomorphism_invariant_of_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_diffeomorphism_invariant_of_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_diffeomorphism_invariant_of_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctional_diffeomorphism_invariant_of_map

def wFunctionalAlong [MeasurableSpace M] (mu : Real -> _root_.MeasureTheory.Measure M) (n : Nat)
    (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s =>
    wFunctional (mu s) n (tau s) (scalarCurvature s)
      (gradPotentialNormSq s) (potential s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctionalAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctionalAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctionalAlong ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wFunctionalAlong

def WEntropyHasFirstVariationAt [MeasurableSpace M] (mu : Real -> _root_.MeasureTheory.Measure M)
    (n : Nat) (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt
    (wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential)
    firstVariation s0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.WEntropyHasFirstVariationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.WEntropyHasFirstVariationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.WEntropyHasFirstVariationAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.WEntropyHasFirstVariationAt

def wEntropyFirstVariation [MeasurableSpace M] (mu : Real -> _root_.MeasureTheory.Measure M)
    (n : Nat) (tau : Real -> Real)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential) s0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation

theorem wEntropyFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> _root_.MeasureTheory.Measure M} {n : Nat} {tau : Real -> Real}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      WEntropyHasFirstVariationAt mu n tau scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    wEntropyFirstVariation mu n tau scalarCurvature gradPotentialNormSq
        potential s0 = firstVariation := by
  unfold wEntropyFirstVariation WEntropyHasFirstVariationAt at *
  exact h.deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation_eq_of_hasFirstVariationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation_eq_of_hasFirstVariationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation_eq_of_hasFirstVariationAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariation_eq_of_hasFirstVariationAt

def wEntropyFirstVariationBeforeIntegrationByPartsIntegrand (n : Nat) (tau tauVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess : M -> Real) :
    M -> Real :=
  fun x =>
    -tau * metricVariationRicciHess x +
      tau * (metricVariationTrace x / 2 - potentialVariation x) *
        (2 * lapPotential x - gradPotentialNormSq x + scalarCurvature x +
          (potential x - (n : Real)) / tau) +
      (potentialVariation x +
        (1 - (n : Real) / 2) * tauVariation *
          (scalarCurvature x + gradPotentialNormSq x) -
        ((n : Real) * tauVariation) / (2 * tau) *
          (potential x - (n : Real)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand

def wEntropyFirstVariationIntegratedByPartsIntegrand (n : Nat) (tau tauVariation : Real)
    (scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real) : M -> Real :=
  fun x =>
    (-tau * metricVariationRicciHess x + tauVariation * metricRicciHess x +
        metricVariationTrace x / 2 -
        ((n : Real) * tauVariation) / (2 * tau)) +
      tau *
        (metricVariationTrace x / 2 - potentialVariation x -
          ((n : Real) * tauVariation) / (2 * tau)) *
        (scalarCurvature x + 2 * lapPotential x - gradPotentialNormSq x +
          (potential x - (n : Real) - 1) / tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationIntegratedByPartsIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationIntegratedByPartsIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationIntegratedByPartsIntegrand ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationIntegratedByPartsIntegrand

private theorem wEntropyFirstVariationBeforeIntegrationByPartsIntegrand_eq_integrated_add_remainder
    {n : Nat} {tau tauVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (htau : tau ≠ 0) {x : M}
    (hmetricRicciHess :
      metricRicciHess x = scalarCurvature x + lapPotential x) :
    wEntropyFirstVariationBeforeIntegrationByPartsIntegrand n tau tauVariation scalarCurvature
        lapPotential gradPotentialNormSq potential potentialVariation
        metricVariationTrace metricVariationRicciHess x =
      wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation scalarCurvature
          lapPotential gradPotentialNormSq potential potentialVariation
          metricVariationTrace metricVariationRicciHess metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) := by
  unfold wEntropyFirstVariationBeforeIntegrationByPartsIntegrand
    wEntropyFirstVariationIntegratedByPartsIntegrand
  rw [hmetricRicciHess]
  field_simp [htau]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand_eq_integrated_add_remainder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.wEntropyFirstVariationBeforeIntegrationByPartsIntegrand_eq_integrated_add_remainder target :: scope.openDecls } }

theorem w_entropy_first_variation_eq_integrated_by_parts [MeasurableSpace M]
    {weightedMeasure : _root_.MeasureTheory.Measure M} {n : Nat} {tau tauVariation firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationBeforeIntegrationByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      _root_.MeasureTheory.Integrable
        (fun x =>
          wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      _root_.MeasureTheory.Integrable
        (fun x =>
          (((n : Real) - 1) * tauVariation) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    firstVariation =
      ∫ x, wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
  rw [hpre]
  have hpoint :
      (fun x =>
        wEntropyFirstVariationBeforeIntegrationByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x)
        =ᵐ[weightedMeasure]
      fun x =>
        wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) := by
    filter_upwards [hmetricRicciHess] with x hx
    exact wEntropyFirstVariationBeforeIntegrationByPartsIntegrand_eq_integrated_add_remainder
      (M := M) (n := n) (tauVariation := tauVariation) htau hx
  calc
    (∫ x, wEntropyFirstVariationBeforeIntegrationByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
        ∂weightedMeasure)
        =
      ∫ x,
        wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x +
        (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x)
        ∂weightedMeasure := _root_.MeasureTheory.integral_congr_ae hpoint
    _ =
      (∫ x, wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x ∂weightedMeasure) +
        ∫ x, (((n : Real) - 1) * tauVariation) *
          (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure := by
        rw [_root_.MeasureTheory.integral_add hfinal_int hibp_int]
    _ =
      (∫ x, wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess
          metricRicciHess x ∂weightedMeasure) +
        (((n : Real) - 1) * tauVariation) *
          ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure := by
        rw [_root_.MeasureTheory.integral_const_mul]
    _ =
      ∫ x, wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
        rw [hibp, _root_.MulZeroClass.mul_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts

theorem w_entropy_first_variation_eq_integrated_by_parts_of_has_first_variation_at
    [MeasurableSpace M]
    {muPath : Real -> _root_.MeasureTheory.Measure M} {n : Nat} {tauPath : Real -> Real}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {weightedMeasure : _root_.MeasureTheory.Measure M} {s0 tau tauVariation firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      metricRicciHess : M -> Real}
    (hderiv :
      WEntropyHasFirstVariationAt muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 firstVariation)
    (htau : tau ≠ 0)
    (hpre :
      firstVariation =
        ∫ x, wEntropyFirstVariationBeforeIntegrationByPartsIntegrand n tau tauVariation
          scalarCurvature lapPotential gradPotentialNormSq potential
          potentialVariation metricVariationTrace metricVariationRicciHess x
          ∂weightedMeasure)
    (hmetricRicciHess :
      ∀ᵐ x ∂weightedMeasure,
        metricRicciHess x = scalarCurvature x + lapPotential x)
    (hfinal_int :
      _root_.MeasureTheory.Integrable
        (fun x =>
          wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
            scalarCurvature lapPotential gradPotentialNormSq potential
            potentialVariation metricVariationTrace metricVariationRicciHess
            metricRicciHess x)
        weightedMeasure)
    (hibp_int :
      _root_.MeasureTheory.Integrable
        (fun x =>
          (((n : Real) - 1) * tauVariation) *
            (lapPotential x - gradPotentialNormSq x))
        weightedMeasure)
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x) ∂weightedMeasure = 0) :
    wEntropyFirstVariation muPath n tauPath scalarCurvaturePath
        gradPotentialNormSqPath potentialPath s0 =
      ∫ x, wEntropyFirstVariationIntegratedByPartsIntegrand n tau tauVariation
        scalarCurvature lapPotential gradPotentialNormSq potential
        potentialVariation metricVariationTrace metricVariationRicciHess
        metricRicciHess x ∂weightedMeasure := by
  rw [wEntropyFirstVariation_eq_of_hasFirstVariationAt hderiv]
  exact w_entropy_first_variation_eq_integrated_by_parts
    (M := M) (weightedMeasure := weightedMeasure) htau hpre
    hmetricRicciHess hfinal_int hibp_int hibp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts_of_has_first_variation_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts_of_has_first_variation_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts_of_has_first_variation_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_entropy_first_variation_eq_integrated_by_parts_of_has_first_variation_at

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
