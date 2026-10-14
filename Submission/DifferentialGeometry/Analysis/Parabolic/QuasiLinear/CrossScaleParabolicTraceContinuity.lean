import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Regularity.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}
variable (u : CrossScaleField (I := I) (M := M) g r s a T)

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private theorem coeffFun_sq_le_initial_add_integral_norm (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2 +
        ∫ τ in _root_.Set.Ioc 0 T, ‖u.energyIntegrand i τ‖ := by
  rw [u.perMode_energyIdentity i ht]
  gcongr
  calc
    ∫ s in (0 : ℝ)..t, u.energyIntegrand i s ≤ ‖∫ s in (0 : ℝ)..t, u.energyIntegrand i s‖ := Real.le_norm_self _
    _ ≤ ∫ s in _root_.Set.Ioc (0 : ℝ) T, ‖u.energyIntegrand i s‖ :=
      u.norm_intervalIntegral_energyIntegrand_le hT i ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.coeffFun_sq_le_initial_add_integral_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.coeffFun_sq_le_initial_add_integral_norm target :: scope.openDecls } }

theorem continuousOn_repr : ContinuousOn u.repr (_root_.Set.Icc 0 T) := by
  rcases lt_or_ge 0 T with hT | hT
  swap
  · exact (_root_.Set.subsingleton_Icc_of_ge hT).continuousOn _
  have hzero : (0 : ℝ) ∈ _root_.Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  refine TensorHs.continuousOn_of_coeff_of_summable_bound
    (f := u.repr) (σ := a + 1) (K := _root_.Set.Icc (0 : ℝ) T)
    (B := fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (u.coeffFun i 0) ^ 2 + ∫ τ in _root_.Set.Ioc 0 T, ‖u.energyIntegrand i τ‖) ?_ ?_ ?_
  · intro i
    refine (u.continuousOn_coeffFun i).congr ?_
    intro t ht
    exact u.repr_coeff hT ht i
  · exact (u.summable_coeffFun_sq hT hzero).add
      (u.summable_integral_norm_energyIntegrand ⟨hT.le, le_rfl⟩)
  · intro t ht i
    rw [u.repr_coeff hT ht i]
    exact u.coeffFun_sq_le_initial_add_integral_norm hT i ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_repr ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField.continuousOn_repr

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField
