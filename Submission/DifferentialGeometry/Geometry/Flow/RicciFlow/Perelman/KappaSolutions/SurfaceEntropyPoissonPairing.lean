import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open scoped _root_.Manifold _root_.ContDiff

section MeanVariance

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [CompactSpace α]

private theorem mean_variance_pairing
    (μ : _root_.MeasureTheory.Measure α) [_root_.MeasureTheory.IsFiniteMeasure μ] [NeZero μ]
    {R : α → Real} (hR : Continuous R) :
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, r - R x ∂μ) = 0 ∧
      -(∫ x, R x * (r - R x) ∂μ) = ∫ x, (R x - r) ^ 2 ∂μ := by
  let A := μ.real Set.univ
  let C := ∫ x, R x ∂μ
  let r := C / A
  change (∫ x, r - R x ∂μ) = 0 ∧
    -(∫ x, R x * (r - R x) ∂μ) = ∫ x, (R x - r) ^ 2 ∂μ
  have hAne : A ≠ 0 := _root_.MeasureTheory.measureReal_univ_ne_zero
  have hRint : _root_.MeasureTheory.Integrable R μ :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ x, r - R x ∂μ) = 0 := by
    rw [_root_.MeasureTheory.integral_sub (_root_.MeasureTheory.integrable_const r) hRint, _root_.MeasureTheory.integral_const, smul_eq_mul]
    change A * (C / A) - C = 0
    field_simp [hAne]
    ring
  have hdevmean : (∫ x, R x - r ∂μ) = 0 := by
    rw [_root_.MeasureTheory.integral_sub hRint (_root_.MeasureTheory.integrable_const r), _root_.MeasureTheory.integral_const, smul_eq_mul]
    change C - A * (C / A) = 0
    field_simp [hAne]
    ring
  have hdevint : _root_.MeasureTheory.Integrable (fun x => R x - r) μ :=
    hRint.sub (_root_.MeasureTheory.integrable_const r)
  have hsquareint : _root_.MeasureTheory.Integrable (fun x => (R x - r) ^ 2) μ :=
    ((hR.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hmean, ?_⟩
  calc
    -(∫ x, R x * (r - R x) ∂μ) = ∫ x, -(R x * (r - R x)) ∂μ :=
      (_root_.MeasureTheory.integral_neg _).symm
    _ = ∫ x, ((R x - r) ^ 2 + r * (R x - r)) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = (∫ x, (R x - r) ^ 2 ∂μ) + r * (∫ x, R x - r ∂μ) := by
      rw [_root_.MeasureTheory.integral_add hsquareint (hdevint.const_mul r), _root_.MeasureTheory.integral_const_mul]
    _ = ∫ x, (R x - r) ^ 2 ∂μ := by rw [hdevmean, _root_.MulZeroClass.mul_zero, add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mean_variance_pairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mean_variance_pairing target :: scope.openDecls } }

end MeanVariance

section MetricScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [CompactSpace M] [Nonempty M]

local instance entropyPairingMeasurable : MeasurableSpace M := borel M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingMeasurable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingMeasurable
local instance entropyPairingBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingBorel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingBorel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingBorel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.entropyPairingBorel

theorem surfaceEntropy_poisson_rhs_integral_zero
    (g : SmoothRiemannianMetric I M) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, r - R x ∂μ) = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact (mean_variance_pairing μ (metricScalar_smooth g).continuous).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_rhs_integral_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_rhs_integral_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_rhs_integral_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_rhs_integral_zero

theorem surfaceEntropy_poisson_gradient_pairing [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g f x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (∫ x, g.inner x
      ((gradG (I := I) g ⟨R, metricScalar_smooth g⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ) =
      ∫ x, (R x - r) ^ 2 ∂μ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let r := (∫ x, R x ∂μ) / μ.real Set.univ
  let : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g (metricScalar_smooth g) f.contMDiff
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ x, g.inner x
      ((gradG (I := I) g ⟨R, metricScalar_smooth g⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ) =
        -(∫ x, R x * ΔG (I := I) g f x ∂μ) := hgreen
    _ = -(∫ x, R x * (r - R x) ∂μ) := by
      congr 1
      apply _root_.MeasureTheory.integral_congr_ae
      exact Eventually.of_forall (fun x => congrArg (fun z => R x * z) (hpoisson x))
    _ = ∫ x, (R x - r) ^ 2 ∂μ :=
      (mean_variance_pairing μ (metricScalar_smooth g).continuous).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_gradient_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_gradient_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_gradient_pairing ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceEntropy_poisson_gradient_pairing

end MetricScalar

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
