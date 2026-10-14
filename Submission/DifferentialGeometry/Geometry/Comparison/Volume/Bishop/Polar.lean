import Submission.DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Radial
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Filter _root_.Metric _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.MeasureTheory _root_.Submission.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [Nontrivial E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [Nontrivial E] in
private lemma smul_mem_ball
    {R : ℝ} (hR : 0 < R) (u : _root_.Metric.sphere (0 : E) 1) (r : _root_.Set.Ioi (0 : ℝ)) :
    r.1 • u.1 ∈ _root_.Metric.ball (0 : E) R ↔ r ∈ _root_.Set.Iio (⟨R, hR⟩ : _root_.Set.Ioi (0 : ℝ)) := by
  have hu : ‖u.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using u.2
  rw [_root_.Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg r.2.le, hu,
    mul_one]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.smul_mem_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.smul_mem_ball target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem normalImage_polar
    (g : SmoothRiemannianMetric I M) (p : M)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ (expMapDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (expMapDiffeo (I := I) g p '' B) =
      ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ),
          B.indicator
            (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  let Ψ := expMapDiffeo (I := I) g p
  let F : E → ℝ≥0∞ :=
    B.indicator (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
  have hcont : ContinuousOn (normalChartDensity (I := I) g p) Ψ.source := by
    simpa only [normalChartDensity, Ψ] using
      paramDensity_contOn (I := I) g Ψ
  have hF : AEMeasurable F (modelHaar (E := E)) := by
    apply (aemeasurable_indicator_iff hB_meas).mpr
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hcont.mono hB_source).aemeasurable hB_meas)
  calc
    riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) =
        ∫⁻ w in B, ENNReal.ofReal (normalChartDensity (I := I) g p w)
          ∂(modelHaar (E := E)) := by
      simpa only [Ψ, normalChartDensity] using
        riemannianVolumeMeasure_image_param_eq (I := I) (M := M) g Ψ
          hB_meas hB_source
    _ = ∫⁻ w, F w ∂(modelHaar (E := E)) := by
      rw [_root_.MeasureTheory.lintegral_indicator hB_meas]
    _ = ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
          ∫⁻ r : _root_.Set.Ioi (0 : ℝ), F (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(modelHaar (E := E)).toSphere :=
      lintegral_polar (modelHaar (E := E)) F hF
    _ = ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
          ∫⁻ r : _root_.Set.Ioi (0 : ℝ),
            B.indicator
              (fun w => ENNReal.ofReal (normalChartDensity (I := I) g p w))
              (r.1 • u.1)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
          ∂(modelHaar (E := E)).toSphere := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalImage_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalImage_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalImage_polar ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalImage_polar

omit [NeZero (Module.finrank ℝ E)] in
theorem normalBall_polar
    (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    (hsource : _root_.Metric.ball (0 : E) R ⊆ (expMapDiffeo (I := I) g p).source) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (expMapDiffeo (I := I) g p '' _root_.Metric.ball (0 : E) R) =
      ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ) in _root_.Set.Iio (⟨R, hR⟩ : _root_.Set.Ioi (0 : ℝ)),
          ENNReal.ofReal (normalChartDensity (I := I) g p (r.1 • u.1))
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(modelHaar (E := E)).toSphere := by
  rw [normalImage_polar (I := I) g p measurableSet_ball hsource]
  apply _root_.MeasureTheory.lintegral_congr
  intro u
  rw [← _root_.MeasureTheory.lintegral_indicator measurableSet_Iio]
  apply _root_.MeasureTheory.lintegral_congr
  intro r
  by_cases hr : r ∈ _root_.Set.Iio (⟨R, hR⟩ : _root_.Set.Ioi (0 : ℝ))
  · have hb : r.1 • u.1 ∈ _root_.Metric.ball (0 : E) R :=
      (smul_mem_ball (E := E) hR u r).2 hr
    simp only [Set.indicator_of_mem hr, Set.indicator_of_mem hb]
  · have hb : r.1 • u.1 ∉ _root_.Metric.ball (0 : E) R := fun h =>
      hr ((smul_mem_ball (E := E) hR u r).1 h)
    simp only [Set.indicator_of_notMem hr, Set.indicator_of_notMem hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalBall_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalBall_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalBall_polar ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.normalBall_polar

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
