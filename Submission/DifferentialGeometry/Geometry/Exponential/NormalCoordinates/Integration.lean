import Submission.DifferentialGeometry.Geometry.Exponential.VolumeDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : MeasurableSet K) (hKdom : K ⊆ expDomain (I := I) g p) :
    (∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) v)
      ∂(modelHaar (E := E))) =
    ∫⁻ w in (euclideanNormalFrame (I := I) g p) ⁻¹' K,
      ENNReal.ofReal (curveDensity (I := I) g
        (radialCurve (I := I) g p (euclideanNormalFrame (I := I) g p w))
        (fun i => radialJacobiField (I := I) g p (euclideanNormalFrame (I := I) g p w)
          (normalBasis (I := I) g p i)) 1)
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := normalBasis (I := I) g p
  let L : F ≃L[ℝ] E := euclideanNormalFrame (I := I) g p
  let D : E → ℝ := fun v => curveDensity (I := I) g (radialCurve (I := I) g p v)
    (fun i => radialJacobiField (I := I) g p v (b i)) 1
  have hbmap :
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map L.toLinearEquiv = b := by
    ext i
    change euclideanNormalFrame (I := I) g p
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i) = normalBasis (I := I) g p i
    simpa only [EuclideanSpace.basisFun_apply] using euclideanNormalFrame_single g p i
  have hmap : Measure.map L (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure F) = b.addHaar := by
    calc
      _ = Measure.map L (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.addHaar := by
        rw [(EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume]
      _ = ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
          L.toLinearEquiv).addHaar := Module.Basis.map_addHaar _ _
      _ = b.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : _root_.MeasureTheory.MeasurePreserving L (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure F) b.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [lintegral_paramDensity_expMap_eq_lintegral_curveDensity_addHaar (I := I) g p b hK hKdom]
  exact (hmp.setLIntegral_comp_preimage_emb L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => ENNReal.ofReal (D v)) K).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
