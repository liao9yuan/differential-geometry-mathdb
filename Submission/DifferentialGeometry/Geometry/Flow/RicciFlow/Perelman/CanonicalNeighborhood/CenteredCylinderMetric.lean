import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckRecentering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereTwoDimension target :: scope.openDecls } }

theorem scalarOneShrinkingCylinderMetric_pullback_lineTranslation
    (t : ℝ) (ht : t < 1) (c : ℝ) :
    Diffeomorph.pullbackMetricCross (scalarOneShrinkingCylinderMetric t ht)
      (cylinderLineTranslation c) = scalarOneShrinkingCylinderMetric t ht := by
  apply SmoothRiemannianMetric.ext_inner
  rintro ⟨y, s⟩ ⟨v, a⟩ ⟨w, b⟩
  erw [Diffeomorph.pullbackMetricCross_inner, mfderiv_cylinderLineTranslation,
    mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply,
    scalarOneShrinkingCylinderMetric_inner, scalarOneShrinkingCylinderMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_pullback_lineTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_pullback_lineTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_pullback_lineTranslation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarOneShrinkingCylinderMetric_pullback_lineTranslation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem cylinderLineTranslation_centered_pullback
    (g : ℝ → SmoothRiemannianMetric I M)
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0, Diffeomorph.pullbackMetricCross (g t) d =
      scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) (p : M) :
    let z := d.symm p
    let e := (cylinderLineTranslation z.2).trans d
    e (z.1, 0) = p ∧
      (∀ y : SpatialNeckCylinder, e y = d (y.1, y.2 + z.2)) ∧
      ∀ t : ℝ, ∀ ht : t ≤ 0, Diffeomorph.pullbackMetricCross (g t) e =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  dsimp only
  refine ⟨?_, fun _ => rfl, ?_⟩
  · change d ((d.symm p).1, 0 + (d.symm p).2) = p
    rw [zero_add]
    exact d.apply_symm_apply p
  · intro t ht
    rw [← Diffeomorph.pullbackMetricCross_trans, hmetric t ht,
      scalarOneShrinkingCylinderMetric_pullback_lineTranslation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_centered_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_centered_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_centered_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderLineTranslation_centered_pullback

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
