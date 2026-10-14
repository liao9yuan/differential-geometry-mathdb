import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def paramGramMatrix (g : SmoothRiemannianMetric I M)
    (Ψ : E → M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun w => Matrix.of fun i j =>
    g.inner (Ψ w)
      (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramGramMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramGramMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramGramMatrix ``Submission.DifferentialGeometry.Integral.Measure.paramGramMatrix

@[simp] lemma paramGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : E → M)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      g.inner (Ψ w)
        (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramGramMatrix_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramGramMatrix_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramGramMatrix_apply ``Submission.DifferentialGeometry.Integral.Measure.paramGramMatrix_apply

def paramDensity (g : SmoothRiemannianMetric I M)
    (Ψ : E → M) : E → ℝ :=
  fun w => Real.sqrt (paramGramMatrix (I := I) g Ψ w).det

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramDensity ``Submission.DifferentialGeometry.Integral.Measure.paramDensity

@[simp] lemma paramDensity_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : E → M)
    (w : E) :
    paramDensity (I := I) g Ψ w =
      Real.sqrt (paramGramMatrix (I := I) g Ψ w).det := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramDensity_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramDensity_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramDensity_apply ``Submission.DifferentialGeometry.Integral.Measure.paramDensity_apply

end DifferentialGeometry.Integral.Measure
