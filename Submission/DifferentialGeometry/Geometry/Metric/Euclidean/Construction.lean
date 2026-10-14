import Submission.DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_metric_of_bilinearField [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∀ x v w, g.inner x v w = B x v w := by
  apply Geometry.smoothMetric_of_localCoeff B hsymm hpos
  intro x₀ i j
  simp only [Geometry.frameVec, TangentBundle.symmL_model_space]
  exact ((hB.clm_apply contDiff_const).clm_apply contDiff_const).contMDiff.contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_metric_of_bilinearField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.exists_metric_of_bilinearField target :: scope.openDecls } }

def smoothMetricOfBilinearField [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) : SmoothRiemannianMetric 𝓘(ℝ, E) E :=
  (exists_metric_of_bilinearField B hsymm hpos hB).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField ``Submission.DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField

theorem smoothMetricOfBilinearField_inner [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) (x v w : E) :
    (smoothMetricOfBilinearField B hsymm hpos hB).inner x v w = B x v w :=
  (exists_metric_of_bilinearField B hsymm hpos hB).choose_spec x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField_inner

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_metric_inner (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ContDiff ℝ ∞ (fun x : E =>
      (show E →L[ℝ] E →L[ℝ] ℝ from by exact g.inner x)) := by
  apply ContMDiff.contDiff
  intro x
  have hs := g.contMDiff x
  rw [_root_.Bundle.contMDiffAt_section] at hs
  have heq : (fun y : E =>
      ((_root_.FiberBundle.trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace 𝓘(ℝ, E) y →L[ℝ]
          TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) x) ⟨y, g.inner y⟩).2) =
      (fun y : E => (show E →L[ℝ] E →L[ℝ] ℝ from by exact g.inner y)) := by
    funext y
    ext v w
    rw [Geometry.metricCoeffInModel_apply]
    · simp only [TangentBundle.symmL_model_space]
      rfl
    · exact Set.mem_univ y
  rwa [heq] at hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.contDiff_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.contDiff_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.contDiff_metric_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.contDiff_metric_inner

end DifferentialGeometry.Geometry.Riemannian
