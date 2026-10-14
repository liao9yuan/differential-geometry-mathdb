import Submission.DifferentialGeometry.Geometry.HarmonicMap.ChartMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Manifold
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem contDiffOn_chart_harmonic_map_source
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) :
    ContDiffOn ℝ ∞ (fun q : V × H × (V →L[ℝ] H) =>
      (WithLp.toLp 2 (fun k => -(∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm q.2.1) *
          (q.2.2 (EuclideanSpace.single j 1)) a *
          (q.2.2 (EuclideanSpace.single j 1)) b)) : H))
      (Set.univ ×ˢ (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ×ˢ Set.univ) := by
  apply contDiffOn_piLp' 2
  intro k
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro j hj
  apply ContDiffOn.sum
  intro a ha
  apply ContDiffOn.sum
  intro b hb
  have hΓ : ContDiffOn ℝ ∞ (chartChristoffel g p a b k) (extChartAt 𝓘(ℝ, E) p).target := by
    simpa only [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq] using
      chartChristoffel_contDiffOn_interior g p a b k
  have hcomp : ContDiffOn ℝ ∞ (fun q : V × H × (V →L[ℝ] H) =>
      chartChristoffel g p a b k ((toEuclidean (E := E)).symm q.2.1))
      (Set.univ ×ˢ (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ×ˢ Set.univ) :=
    hΓ.comp ((toEuclidean (E := E)).symm.contDiff.comp_contDiffOn
      (contDiffOn_fst.comp contDiffOn_snd (_root_.Set.mapsTo_univ _ _)))
      (fun q hq => toEuclidean_symm_mem_target hq.2.1)
  have hD (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (fun q : V × H × (V →L[ℝ] H) =>
      (q.2.2 (EuclideanSpace.single j 1)) i) :=
    (contDiff_piLp_apply (p := 2) (i := i)).comp
      ((contDiff_snd.comp contDiff_snd).clm_apply contDiff_const)
  exact (hcomp.mul (hD a).contDiffOn).mul (hD b).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_chart_harmonic_map_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_chart_harmonic_map_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_chart_harmonic_map_source ``Submission.DifferentialGeometry.Geometry.contDiffOn_chart_harmonic_map_source

end DifferentialGeometry.Geometry

end
