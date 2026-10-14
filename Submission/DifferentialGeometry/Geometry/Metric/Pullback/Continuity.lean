import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem contMDiffAt_zero_source_mfderiv {f : V → M} {x : V}
    (hf : ContMDiffAt 𝓘(ℝ, V) I 1 f x) :
    ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V →L[ℝ] E)) 0
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, V) I f y⟩ :
        _root_.Bundle.TotalSpace (V →L[ℝ] E)
          (fun m => Bundle.Trivial M V m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le (by norm_num), ?_⟩
  have hd := hf.mfderiv_const (m := 0) (by norm_num)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiffAt_zero_source_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiffAt_zero_source_mfderiv target :: scope.openDecls } }

theorem continuousOn_pullback_metric_coefficients_of_contMDiffOn_one
    (g : SmoothRiemannianMetric I M)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I 1 f U) :
    ContinuousOn (pullbackMetricCoefficients g f) U := by
  suffices h : ContDiffOn ℝ 0 (pullbackMetricCoefficients g f) U from h.continuousOn
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hD := contMDiffAt_zero_source_mfderiv hfx
  have hG := (g.contMDiff.of_le (by norm_num : (0 : ℕ∞ω) ≤ ∞)).contMDiffAt.comp x
    (hfx.of_le (by norm_num))
  have hB := hG.clm_bundle_bilinearComp
    (U₁ := TangentSpace I) (U₂ := TangentSpace I) (U₃ := Bundle.Trivial M ℝ)
    (U₄ := Bundle.Trivial M V) (U₅ := Bundle.Trivial M V) hD hD
  have h := (contMDiffAt_totalSpace.mp hB).2.contDiffAt
  refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [] with y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_pullback_metric_coefficients_of_contMDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_pullback_metric_coefficients_of_contMDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_pullback_metric_coefficients_of_contMDiffOn_one ``Submission.DifferentialGeometry.Geometry.continuousOn_pullback_metric_coefficients_of_contMDiffOn_one

end DifferentialGeometry.Geometry

end
