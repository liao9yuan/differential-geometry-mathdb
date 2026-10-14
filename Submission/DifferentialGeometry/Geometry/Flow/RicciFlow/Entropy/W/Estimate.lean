import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.GradientIdentities
import Submission.DifferentialGeometry.Analysis.Integration.EntropyJensen
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem w_square_form
    (mu : _root_.MeasureTheory.Measure M) (g : SmoothRiemannianMetric I M) (n : Nat)
    {tau : Real} (htau : 0 < tau) (scalarCurvature : M -> Real)
    {v : M -> Real} (hv : ContMDiff I 𝓘(Real, Real) ∞ v)
    (hpos : ∀ x : M, 0 < v x) :
    wFunctional mu n tau scalarCurvature
        (fun x =>
          g.inner x
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x)
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x))
        (perelmanPotential n tau (fun y => v y * v y)) =
      ∫ x,
        4 * tau * g.inner x
            (gradientFun (I := I) g v x)
            (gradientFun (I := I) g v x) +
          tau * scalarCurvature x * (v x * v x) -
          (v x * v x) * Real.log (v x * v x) +
          (Real.log (perelmanDensityPrefactor n tau) - (n : Real)) *
            (v x * v x) ∂mu := by
  let density : M -> Real := fun x => v x * v x
  let potential : M -> Real := perelmanPotential n tau density
  let gradSq : M -> Real := fun x =>
    g.inner x
      (gradientFun (I := I) g potential x)
      (gradientFun (I := I) g potential x)
  have hdensity : perelmanDensity n tau potential = density := by
    exact density_potential n density htau fun x => mul_pos (hpos x) (hpos x)
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x)) mu := by
    rw [hdensity]
    exact (ENNReal.continuous_ofReal.comp (hv.mul hv).continuous).aemeasurable
  rw [show
    wFunctional mu n tau scalarCurvature
        (fun x =>
          g.inner x
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x)
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x))
        (perelmanPotential n tau (fun y => v y * v y)) =
      wFunctional mu n tau scalarCurvature gradSq potential by rfl]
  rw [wFunctional_base mu n tau scalarCurvature gradSq potential htau.le hmeas]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [congrFun hdensity x]
  change
    (v x * v x) *
        (tau * (scalarCurvature x + gradSq x) + potential x - (n : Real)) = _
  rw [show potential x =
      -Real.log (v x * v x) + Real.log (perelmanDensityPrefactor n tau) by
    exact potential_square n hpos htau x]
  have henergy :
      (v x * v x) * gradSq x =
        4 * g.inner x
          (gradientFun (I := I) g v x)
          (gradientFun (I := I) g v x) := by
    exact square_pot_energy (I := I) g n hv hpos htau x
  linear_combination tau * henergy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_square_form

theorem w_form_upper
    {α : Type*} [MeasurableSpace α] (μ : _root_.MeasureTheory.Measure α) [_root_.MeasureTheory.IsFiniteMeasure μ]
    {U : Set α} {v R gradSq : α → Real} {tau K G C : Real}
    (hvmeas : Measurable v) (hv2i : _root_.MeasureTheory.Integrable (fun x => v x ^ 2) μ)
    (hmass : (∫ x, v x ^ 2 ∂μ) = 1)
    (hent : _root_.MeasureTheory.Integrable (fun x => v x ^ 2 * Real.log (v x ^ 2)) μ)
    (hsupp : Function.support v ⊆ U)
    (hgradi : _root_.MeasureTheory.Integrable gradSq μ) (hgrad : (∫ x, gradSq x ∂μ) ≤ G)
    (hRi : _root_.MeasureTheory.Integrable (fun x => R x * v x ^ 2) μ)
    (hR : ∀ x ∈ U, R x ≤ K) (htau : 0 ≤ tau) :
    (∫ x, 4 * tau * gradSq x + tau * R x * v x ^ 2 -
        v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) ≤
      4 * tau * G + tau * K + Real.log (μ U).toReal + C := by
  have hsupp2 : Function.support (fun x => v x ^ 2) ⊆ U := by
    intro x hx
    apply hsupp
    intro hvx
    exact hx (by norm_num [hvx])
  have hent_le :
      -(∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤ Real.log (μ U).toReal :=
    DifferentialGeometry.Analysis.Integration.entropy_support_le μ
      (hvmeas.pow_const 2) hv2i (fun x => sq_nonneg (v x)) hmass hent hsupp2
  have hscalar : (∫ x, R x * v x ^ 2 ∂μ) ≤ K := by
    calc
      (∫ x, R x * v x ^ 2 ∂μ) ≤ ∫ x, K * v x ^ 2 ∂μ := by
        apply _root_.MeasureTheory.integral_mono hRi (hv2i.const_mul K)
        intro x
        by_cases hvx : v x = 0
        · norm_num [hvx]
        · exact mul_le_mul_of_nonneg_right (hR x (hsupp hvx)) (sq_nonneg (v x))
      _ = K := by
        rw [_root_.MeasureTheory.integral_const_mul, hmass, mul_one]
  have hdir_le :
      4 * tau * (∫ x, gradSq x ∂μ) ≤ 4 * tau * G :=
    mul_le_mul_of_nonneg_left hgrad (mul_nonneg (by norm_num) htau)
  have hscalar_le :
      tau * (∫ x, R x * v x ^ 2 ∂μ) ≤ tau * K :=
    mul_le_mul_of_nonneg_left hscalar htau
  let entropy : α → Real := fun x => v x ^ 2 * Real.log (v x ^ 2)
  have hdir_i : _root_.MeasureTheory.Integrable (fun x => (4 * tau) * gradSq x) μ :=
    hgradi.const_mul _
  have hscal_i : _root_.MeasureTheory.Integrable (fun x => tau * (R x * v x ^ 2)) μ :=
    hRi.const_mul _
  have hnorm_i : _root_.MeasureTheory.Integrable (fun x => C * v x ^ 2) μ :=
    hv2i.const_mul _
  calc
    (∫ x, 4 * tau * gradSq x + tau * R x * v x ^ 2 -
        v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) =
        4 * tau * (∫ x, gradSq x ∂μ) +
          tau * (∫ x, R x * v x ^ 2 ∂μ) -
          (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) + C := by
      calc
        (∫ x, 4 * tau * gradSq x + tau * R x * v x ^ 2 -
            v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2 ∂μ) =
            (∫ x, (4 * tau) * gradSq x + tau * (R x * v x ^ 2) - entropy x ∂μ) +
              ∫ x, C * v x ^ 2 ∂μ := by
          simpa only [entropy, Pi.add_apply, Pi.sub_apply, mul_assoc] using
            _root_.MeasureTheory.integral_add ((hdir_i.add hscal_i).sub hent) hnorm_i
        _ = ((∫ x, (4 * tau) * gradSq x + tau * (R x * v x ^ 2) ∂μ) -
              ∫ x, entropy x ∂μ) + ∫ x, C * v x ^ 2 ∂μ := by
          congr 1
          simpa only [Pi.add_apply] using _root_.MeasureTheory.integral_sub (hdir_i.add hscal_i) hent
        _ = (((∫ x, (4 * tau) * gradSq x ∂μ) +
              ∫ x, tau * (R x * v x ^ 2) ∂μ) -
              ∫ x, entropy x ∂μ) + ∫ x, C * v x ^ 2 ∂μ := by
          rw [_root_.MeasureTheory.integral_add hdir_i hscal_i]
        _ = 4 * tau * (∫ x, gradSq x ∂μ) +
              tau * (∫ x, R x * v x ^ 2 ∂μ) -
              (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) + C := by
          dsimp only [entropy]
          rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, hmass]
          ring
    _ ≤ 4 * tau * G + tau * K + Real.log (μ U).toReal + C := by
      linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_form_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_form_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_form_upper ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_form_upper

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
