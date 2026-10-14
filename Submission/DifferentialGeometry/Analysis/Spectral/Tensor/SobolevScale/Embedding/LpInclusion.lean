import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
import Submission.DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap
import Mathlib.MeasureTheory.Function.LpSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem tensorHsPi_ae_eq_of_inclusion
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hdb : d ≤ b)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : _root_.MeasureTheory.Measure Ω}
    (Z : _root_.MeasureTheory.Lp (PiLp 2 (fun _ : ι => TensorHs g r s b)) p μ)
    (W : Ω → PiLp 2 (fun _ : ι => TensorHs g r s a)) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hab)
    let Q := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hcd)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hca)
    let U := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hdb)
    (fun t => P (Z t)) =ᵐ[μ] W →
    (fun t => Q ((U.compLpL p μ Z) t)) =ᵐ[μ] (fun t => L (W t)) := by
  intro P Q L U hZW
  filter_upwards [U.coeFn_compLpL Z, hZW] with t ht hpt
  rw [ht, ← hpt]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsPi_ae_eq_of_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsPi_ae_eq_of_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsPi_ae_eq_of_inclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHsPi_ae_eq_of_inclusion

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
end
