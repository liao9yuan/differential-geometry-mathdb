import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionFinite
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

theorem heatEvolutionField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (b + 1)) :
    (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith)).compLpL 2 (timeMeasure T)
        (heatEvolutionField b T u₀) =
      heatEvolutionField a T (tensorHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀) := by
  apply Lp.ext
  filter_upwards [(tensorHsInclusion (show a + 2 ≤ b + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (heatEvolutionField b T u₀),
    (heatEvolutionCrossScale hT hc u₀).link,
    (heatEvolutionCrossScale hT hc
      (tensorHsInclusion (show a + 1 ≤ b + 1 by linarith) u₀)).link,
    _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t hinc hhi hlo ht
  rw [hinc]
  apply TensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply]
  have hhi' := congrArg (fun x => x.coeff i) hhi
  have hlo' := congrArg (fun x => x.coeff i) hlo
  change (heatEvolutionField b T u₀ t).coeff i =
      ((heatEvolution b T u₀).toFun t).coeff i at hhi'
  change (heatEvolutionField a T (tensorHsInclusion
      (show a + 1 ≤ b + 1 by linarith) u₀) t).coeff i =
      ((heatEvolution a T (tensorHsInclusion
        (show a + 1 ≤ b + 1 by linarith) u₀)).toFun t).coeff i at hlo'
  rw [heatEvolution_toFun_coeff hT hc u₀ i ht] at hhi'
  rw [heatEvolution_toFun_coeff hT hc _ i ht] at hlo'
  exact hhi'.trans hlo'.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatEvolutionField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatEvolutionField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatEvolutionField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatEvolutionField_compLpL_tensorHsInclusion

variable {ι : Type*} [Fintype ι]

theorem heatVectorField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 1))) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))).compLpL
        2 (timeMeasure T) (heatVectorField b T u₀) =
      heatVectorField a T (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)) u₀) := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [heatVectorField, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact heatEvolutionField_compLpL_tensorHsInclusion hab hT hc (u₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_compLpL_tensorHsInclusion

theorem heatDuhamelVectorField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))).compLpL
        2 (timeMeasure T) (heatDuhamelVectorField hT u₀ F) =
      heatDuhamelVectorField hT
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)) u₀)
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) F) := by
  rw [heatDuhamelVectorField_eq_add hT hc, map_add,
    heatVectorField_compLpL_tensorHsInclusion hab hT.le hc,
    maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion hab hT hc, map_zero,
    heatDuhamelVectorField_eq_add hT hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_compLpL_tensorHsInclusion

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
