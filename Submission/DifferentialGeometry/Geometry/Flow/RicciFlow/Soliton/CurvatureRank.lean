import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankScaling
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree

theorem canonicalMetric_metricCurvatureOperatorRankAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (hdim : Module.finrank ℝ E = 3) :
    metricCurvatureOperatorRankAt
        (canonicalMetric g f sigma hcomplete hsol ht) x hdim =
      metricCurvatureOperatorRankAt g
        (canonicalFlowDiffeomorph g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) hdim := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Φ := canonicalFlowDiffeomorph g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  have hdim' (y : M) : Module.finrank ℝ (TangentSpace I y) = 3 := by
    rw [show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
    exact hdim
  rw [canonicalMetric, ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    metricCurvatureOperatorRankAt_localPull _ _ _ _ (hdim' x) (hdim' (Φ x)),
    metricCurvatureOperatorRankAt_scaleMetric _ _ _ _ (hdim' (Φ x))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt

end DifferentialGeometry.PDE.RicciFlow.Soliton

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
  (IsSolutionOn curvatureOperator_nonnegative_of_complete_ancient
    curvatureOperatorImageAt_finrank_eq_at_later_time
    curvatureOperatorImageAt_finrank_trichotomy_at_later_time)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Soliton
  (canonicalTimeDomain canonicalSolutionOn canonicalSolutionOn_metric_zero
    canonicalSolutionOn_isSolutionOn canonicalSolutionOn_complete)

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt g y
        ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩) := by
  let b : ℝ := (σ + 1)⁻¹
  have hden : 0 < σ + 1 := by linarith
  have hb : 0 < b := inv_pos.mpr hden
  have hσb : σ * b < 1 := by
    have hdiv : σ * b = σ / (σ + 1) := by
      dsimp [b]
      rw [div_eq_mul_inv]
    rw [hdiv]
    exact (div_lt_iff₀ hden).2 (by linarith)
  let D := RealTimeInterval.infiniteOpen b 0 hb
  have hD : D.carrier ⊆ canonicalTimeDomain σ := by
    intro t ht
    change 0 < 1 - σ * t
    have ht' : t < b := ht
    have hmul : σ * t ≤ σ * b := mul_le_mul_of_nonneg_left ht'.le hσ
    linarith
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : _root_.Set.Icc (-1 : ℝ) 0 ⊆ D.regular := by
    intro t ht
    change t < b
    exact ht.2.trans_lt hb
  have hR : ∀ r ∈ _root_.Set.Icc (-1 : ℝ) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun t ht => ht.trans_lt (hr.2.trans_lt hb))
      (fun t ht => ht.trans (hr.2.trans_lt hb))
      (fun t ht => canonicalSolutionOn_complete g f σ hcomplete hsol D hD
        (ht.trans_lt (hr.2.trans_lt hb))) hdim x
  have heq := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim
    (show (-1 : ℝ) < 0 by norm_num) hreg hR x y
  have hzero : S.family.metric 0 = g := by
    exact canonicalSolutionOn_metric_zero g f σ hcomplete hsol D
  rw [hzero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq

theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_eq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x y : M) :
    DimensionThree.metricCurvatureOperatorRankAt g x hdim =
      DimensionThree.metricCurvatureOperatorRankAt g y hdim := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim, metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g y hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq g f hσ hcomplete hsol hdim x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x : M) :
    let q := Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    q = 0 ∨ q = 1 ∨ q = 3 := by
  let b : ℝ := (σ + 1)⁻¹
  have hden : 0 < σ + 1 := by linarith
  have hb : 0 < b := inv_pos.mpr hden
  have hσb : σ * b < 1 := by
    have hdiv : σ * b = σ / (σ + 1) := by
      dsimp [b]
      rw [div_eq_mul_inv]
    rw [hdiv]
    exact (div_lt_iff₀ hden).2 (by linarith)
  let D := RealTimeInterval.infiniteOpen b 0 hb
  have hD : D.carrier ⊆ canonicalTimeDomain σ := by
    intro t ht
    change 0 < 1 - σ * t
    have ht' : t < b := ht
    have hmul : σ * t ≤ σ * b := mul_le_mul_of_nonneg_left ht'.le hσ
    linarith
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : _root_.Set.Icc (-1 : ℝ) 0 ⊆ D.regular := by
    intro t ht
    change t < b
    exact ht.2.trans_lt hb
  have hR : ∀ r ∈ _root_.Set.Icc (-1 : ℝ) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun t ht => ht.trans_lt (hr.2.trans_lt hb))
      (fun t ht => ht.trans (hr.2.trans_lt hb))
      (fun t ht => canonicalSolutionOn_complete g f σ hcomplete hsol D hD
        (ht.trans_lt (hr.2.trans_lt hb))) hdim x
  have heq := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    (show (-1 : ℝ) < 0 by norm_num) hreg hR x
  have hzero : S.family.metric 0 = g := by
    exact canonicalSolutionOn_metric_zero g f σ hcomplete hsol D
  rw [hzero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy


theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x : M) :
    metricCurvatureOperatorRankAt g x hdim = 0 ∨
      metricCurvatureOperatorRankAt g x hdim = 1 ∨
      metricCurvatureOperatorRankAt g x hdim = 3 := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy g f hσ hcomplete hsol hdim x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy


end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree

theorem canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : DimensionThree.metricCurvatureOperatorRankAt g x₀ hdim = 1)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain σ) (x : M) :
    DimensionThree.metricCurvatureOperatorRankAt
      (canonicalMetric g f σ hcomplete hsol ht) x hdim = 1 := by
  rw [canonicalMetric_metricCurvatureOperatorRankAt]
  exact (gradientRicciSoliton_metricCurvatureOperatorRankAt_eq g f hσ hcomplete hsol hdim _ x₀).trans hrank

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one

theorem canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : DimensionThree.metricCurvatureOperatorRankAt g x₀ hdim = 1)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain σ) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (canonicalMetric g f σ hcomplete hsol ht) x
      ⟨metricRm04At (canonicalMetric g f σ hcomplete hsol ht) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (canonicalMetric g f σ hcomplete hsol ht) x⟩) = 1 := by
  rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
  exact canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one
    g f hσ hcomplete hsol hdim hrank ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one

end DifferentialGeometry.PDE.RicciFlow.Soliton
