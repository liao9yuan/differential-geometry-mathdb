import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianMass

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem normalizedShrinkerMass_eq_one_of_isGaussian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1)
    (hnormal : hamiltonNormalized g f 1) :
    normalizedShrinkerMass g f = 1 := by
  rw [normalizedShrinkerMass_eq_const_mul_lintegral,
    isGaussianGradientRicciSoliton_lintegral_exp_neg_of_hamiltonNormalized hGaussian hnormal,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi) _),
    ← Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi)]
  simp only [neg_div, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_isGaussian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_isGaussian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_isGaussian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_isGaussian

theorem normalizedShrinkerMass_eq_one_of_scalar_eq_zero
    [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton g f)
    {x : M} (hx : metricScalarAt g x = 0) :
    normalizedShrinkerMass g f = 1 :=
  normalizedShrinkerMass_eq_one_of_isGaussian
    (normalizedGradientRicciSoliton_isGaussian_of_scalar_eq_zero h hx)
    (normalizedGradientRicciSoliton_hamilton_normalized h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normalizedShrinkerMass_eq_one_of_scalar_eq_zero

theorem scalar_pos_of_normalizedShrinkerMass_ne_one
    [ConnectedSpace M] [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton g f)
    (hmass : normalizedShrinkerMass g f ≠ 1) (x : M) :
    0 < metricScalarAt g x :=
  lt_of_le_of_ne (normalizedGradientRicciSoliton_scalar_nonneg h x)
    (fun hx => hmass (normalizedShrinkerMass_eq_one_of_scalar_eq_zero h hx.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_pos_of_normalizedShrinkerMass_ne_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_pos_of_normalizedShrinkerMass_ne_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_pos_of_normalizedShrinkerMass_ne_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalar_pos_of_normalizedShrinkerMass_ne_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
