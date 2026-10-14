import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartPullbackLp
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Manifold _root_.Metric
open scoped _root_.ENNReal _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Sobolev.Chart

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_smoothMap_mul_chartDensity_eq_one
    (q : SmoothRiemannianMetric I M) (α : M) {Ω K : Set EuStd}
    (hΩ : IsOpen Ω) (hΩs : Ω ⊆ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (hK : IsCompact K) (hKs : K ⊆ Ω) :
    ∃ φ : C^∞⟮I, M; ℝ⟯,
      tsupport (φ : M → ℝ) ⊆ (extChartAt I α).symm '' ((toEuclidean (E := E)).symm '' Ω) ∧
      ∀ z ∈ K, chartDensity (I := I) q α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
          φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1 := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood hK hΩ hKs
  let e := toEuclidean (E := E)
  let ρ := fun z => chartDensityOnE (I := I) q α (e.symm z)
  let ψ := fun z => χ z / ρ z
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ (extChartAt I α).target := by
    obtain ⟨y, hy, he⟩ := hΩs hz
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ Ω :=
    (chartDensityOnE_contDiffOn (I := I) q α).comp e.symm.contDiff.contDiffOn (fun _ hz => hy hz)
  have hρpos {z : EuStd} (hz : z ∈ Ω) : 0 < ρ z := by
    apply chartDensity_pos (I := I) q α
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target (hy hz)
  have hψχ : tsupport ψ ⊆ tsupport χ := by
    simpa only [ψ, div_eq_mul_inv] using (tsupport_mul_subset_left (f := χ) (g := fun z => (ρ z)⁻¹))
  have hψs : tsupport ψ ⊆ Ω := hψχ.trans hχs
  have hψc : HasCompactSupport ψ := hχc.of_isClosed_subset (isClosed_tsupport _) hψχ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hχ.contDiffOn.div hρ (fun _ hz => ne_of_gt (hρpos hz))).contDiff_of_tsupport_subset hΩ hψs
  let φ : C^∞⟮I, M; ℝ⟯ := ⟨chartPullback I α ψ,
    chartPullback_contMDiff α hψ hψc (hψs.trans (hΩs.trans (_root_.Set.image_mono interior_subset)))⟩
  refine ⟨φ, (tsupport_chartPullback_subset α hψc
    (hψs.trans (hΩs.trans (_root_.Set.image_mono interior_subset)))).trans (_root_.Set.image_mono (_root_.Set.image_mono hψs)), ?_⟩
  intro z hz
  have ht := hy (hKs hz)
  have hs := (extChartAt I α).map_target ht
  rw [extChartAt_source] at hs
  change ρ z * chartPullback I α ψ ((extChartAt I α).symm (e.symm z)) = 1
  rw [chartPullback_apply_of_mem α ψ hs, (extChartAt I α).right_inv ht,
    ContinuousLinearEquiv.apply_symm_apply]
  dsimp only [ψ]
  rw [hχone z (_root_.Metric.self_subset_cthickening _ hz)]
  exact mul_one_div_cancel (ne_of_gt (hρpos (hKs hz)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one

end DifferentialGeometry.Analysis.Sobolev.Chart
