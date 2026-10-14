import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Soliton
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton g f sigma)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    metricAlgebraicCurvatureTensorAt (canonicalMetric g f sigma hcomplete hsol ht) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let Phi := canonicalFlowDiffeomorph g f sigma hcomplete hsol (canonicalFlowParameter sigma t)
  rw [metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff]
  intro n c v w
  have hbase := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
    g (Phi x)).mp (hcone (Phi x)) n c
      (fun i => mfderiv I I Phi x (v i)) (fun i => mfderiv I I Phi x (w i))
  have hRm (i j : Fin n) :
      metricRm04StandardAt (canonicalMetric g f sigma hcomplete hsol ht) x
        (v i) (w i) (w j) (v j) =
      (1 - sigma * t) * metricRm04StandardAt g (Phi x)
        (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j)) := by
    exact canonicalMetric_metricRm04 g f sigma hcomplete hsol ht x
      (![v i, w i, w j, v j])
  simp_rw [hRm]
  have heq : (∑ i, ∑ j, c i * c j * ((1 - sigma * t) *
      metricRm04StandardAt g (Phi x) (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j)))) =
      (1 - sigma * t) * (∑ i, ∑ j, c i * c j *
      metricRm04StandardAt g (Phi x) (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
        (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact mul_nonneg (mem_canonicalTimeDomain_iff.mp ht).le hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperator_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperator_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperator_nonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.canonicalMetric_curvatureOperator_nonnegative

end DifferentialGeometry.PDE.RicciFlow.Soliton

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
  (IsSolutionOn
    curvatureOperatorImageAt_finrank_eq_at_later_time
    curvatureOperatorImageAt_finrank_trichotomy_at_later_time)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Soliton
  (zero_mem_canonicalTimeDomain canonicalMetricFamily canonicalMetricFamily_eq canonicalMetric_curvatureOperator_nonnegative canonicalTimeDomain canonicalSolutionOn canonicalSolutionOn_metric_zero
    canonicalSolutionOn_isSolutionOn canonicalSolutionOn_complete)

private theorem exists_nonnegative_canonical_slab
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ (D : RealTimeInterval) (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D),
      IsSolutionOn S ∧ ∃ s : ℝ, s < 0 ∧ _root_.Set.Icc s 0 ⊆ D.regular ∧
      (∀ r ∈ _root_.Set.Icc s 0, ∀ x : M,
        (⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) ∧
      S.family.metric 0 = g := by
  have hopen : IsOpen (canonicalTimeDomain σ) :=
    isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨a, b, hzero, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds (zero_mem_canonicalTimeDomain σ))
  let D := RealTimeInterval.openInterval a b 0 hzero
  have hD : D.carrier ⊆ canonicalTimeDomain σ := hsub
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : _root_.Set.Icc (a / 2) 0 ⊆ D.regular := by
    intro t ht
    change a < t ∧ t < b
    constructor <;> linarith [hzero.1, hzero.2, ht.1, ht.2]
  have hR : ∀ r ∈ _root_.Set.Icc (a / 2) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    have hrD : r ∈ canonicalTimeDomain σ := hD (D.regular_subset (hreg hr))
    change metricAlgebraicCurvatureTensorAt (canonicalMetricFamily g f σ hcomplete hsol r) x ∈ _
    rw [canonicalMetricFamily_eq g f σ hcomplete hsol hrD]
    exact canonicalMetric_curvatureOperator_nonnegative g f σ hcomplete hsol hcone hrD x
  exact ⟨D, S, hS, a / 2, by linarith [hzero.1], hreg, hR,
    canonicalSolutionOn_metric_zero g f σ hcomplete hsol D⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.exists_nonnegative_canonical_slab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.exists_nonnegative_canonical_slab target :: scope.openDecls } }

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt g y
        ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩) := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim
    hs hreg hR x y
  rw [hzero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative

theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x y : M) :
    DimensionThree.metricCurvatureOperatorRankAt g x hdim =
      DimensionThree.metricCurvatureOperatorRankAt g y hdim := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim, metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g y hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq_of_nonnegative g f σ hcomplete hsol hdim hcone x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_eq_of_nonnegative

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) :
    let q := Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩)
    q = 0 ∨ q = 1 ∨ q = 3 := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    hs hreg hR x
  rw [hzero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative


theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M) :
    metricCurvatureOperatorRankAt g x hdim = 0 ∨
      metricCurvatureOperatorRankAt g x hdim = 1 ∨
      metricCurvatureOperatorRankAt g x hdim = 3 := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_trichotomy_of_nonnegative g f σ hcomplete hsol hdim hcone x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative


theorem gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ y : M, metricAlgebraicCurvatureTensorAt g y ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    Connection.IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt g x
        ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) := by
  obtain ⟨D, S, hS, s, hs, hreg, hR, hzero⟩ :=
    exists_nonnegative_canonical_slab g f σ hcomplete hsol hcone
  have heq := DifferentialGeometry.PDE.RicciFlow.curvatureOperatorKernelAt_parallel_at_later_time S hS hdim
    hs hreg hR
  rw [hzero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperatorKernelAt_parallel_of_nonnegative

end DifferentialGeometry.Geometry
