import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (-w) = -covGrad g r s w := by
  rw [← neg_one_smul ℝ w, covGrad_smul, neg_one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_neg ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_neg

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (w₁ - w₂) = covGrad g r s w₁ - covGrad g r s w₂ := by
  rw [sub_eq_add_neg, covGrad_add, covGrad_neg, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_sub ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_sub

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_add (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ + w₂)
      = iteratedCovGrad g r s j w₁ + iteratedCovGrad g r s j w₂ := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_add ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_add

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (c • w) = c • iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_neg (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (-w) = -iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_neg ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_neg

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem iteratedCovGrad_sub (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ - w₂)
      = iteratedCovGrad g r s j w₁ - iteratedCovGrad g r s j w₂ := by
  rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_sub ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_sub

end Spectral
end Analysis
end DifferentialGeometry

end
