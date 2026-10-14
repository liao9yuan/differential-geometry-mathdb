import Submission.DifferentialGeometry.Geometry.Metric.LocalProduct
import Submission.DifferentialGeometry.Geometry.Connection.GlobalParallelLineFamily
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureLine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

theorem exists_global_product_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {U : Set ℝ} (hU : IsOpen U) (hreg : U ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hg : RiemannianMetricComplete (I := I) (S.family.metric t₀))
    (hR : ∀ t ∈ U, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ J, RiemannianMetricComplete (I := I) (S.family.metric t) →
                RiemannianMetricComplete
                  (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              ∀ t ∈ J, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ)) := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  obtain ⟨s, -, hunit, hparallel, hdual⟩ :=
    exists_global_parallel_unit_section_of_curvatureOperatorImage_rank_eq_one
      S hS hdim hU hreg hJ hJsub ht₀ hR hrank
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod, -, -⟩ :=
    exists_global_product_metric_family_from_common_parallel_unit_section (m := 2)
      (fun t : J => S.family.metric t.1) ⟨t₀, ht₀⟩ hg s
      (hunit t₀ ht₀) (fun t => hparallel t.1 t.2) (fun t => hdual t.1 t.2)
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  classical
  let h' : ℝ → SmoothRiemannianMetric
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N :=
    fun t => if ht : t ∈ J then h ⟨t, ht⟩ else h ⟨t₀, ht₀⟩
  refine ⟨N, htop, hcs, hmanifold, ht2, hσ, h', F, hconn, hsimply, ?_, ?_⟩
  · intro t ht hc
    simpa only [h', dif_pos ht] using hcomp ⟨t, ht⟩ hc
  · intro t ht
    simpa only [h', dif_pos ht] using hprod ⟨t, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_global_product_of_curvatureOperatorImage_rank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_global_product_of_curvatureOperatorImage_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_global_product_of_curvatureOperatorImage_rank_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_global_product_of_curvatureOperatorImage_rank_eq_one

theorem exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {α β : ℝ} (hreg : _root_.Set.Ioo α β ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ _root_.Set.Ioo α β)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hg : RiemannianMetricComplete (I := I) (S.family.metric t₀))
    (hR : ∀ t ∈ _root_.Set.Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ J, RiemannianMetricComplete (I := I) (S.family.metric t) →
                RiemannianMetricComplete
                  (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              ∀ t ∈ J, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ)) := by
  exact exists_global_product_of_curvatureOperatorImage_rank_eq_one
    S hS isOpen_Ioo hreg hJ hJsub ht₀ hg hR hrank

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one

end DifferentialGeometry.PDE.RicciFlow

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [SimplyConnectedSpace M]

theorem exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ}
    (hcar : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    {t₀ : ℝ} (ht₀ : t₀ ∈ _root_.Set.Ioo a b)
    (hg : RiemannianMetricComplete (S.family.metric t₀))
    (hR : ∀ t ∈ _root_.Set.Ioo a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ _root_.Set.Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (Phi : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ _root_.Set.Icc a b, Diffeomorph.pullbackMetricCross (S.family.metric t) Phi =
                (h t).prod (euclideanMetric (E := ℝ))) := by
  obtain ⟨N, htop, hcs, hman, ht2, hσ, h, Phi, hconn, hsimply, _, hprod⟩ :=
    exists_global_product_of_curvatureOperatorImage_rank_eq_one S hS isOpen_Ioo hreg
      _root_.Set.ordConnected_Ioo Subset.rfl ht₀ hg hR hrank
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hσ
  have hlocal (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :
      localPullMetric (S.family.metric t) Phi Phi.isLocalDiffeomorph =
        (h t).prod (euclideanMetric (E := ℝ)) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    exact hprod t ht
  obtain ⟨k, _, _, hk⟩ := exists_metric_prod_eq_on_closure_of_localPullMetric
    S.family.metric h (fun _ => euclideanMetric (E := ℝ)) Phi Phi.isLocalDiffeomorph
    (0 : ℝ) (show _root_.Set.Icc a b ⊆ closure (_root_.Set.Ioo a b) by rw [closure_Ioo (ht₀.1.trans ht₀.2).ne])
    (fun t ht x u v => (hS.smoothMetric.coeff_cont x u v t (hcar ht)).mono
      (Ioo_subset_Icc_self.trans hcar))
    (fun _ _ _ _ _ => continuousWithinAt_const) hlocal
  refine ⟨N, htop, hcs, hman, ht2, hσ, k, Phi, hconn, hsimply, ?_⟩
  intro t ht
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact hk t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one

end DifferentialGeometry.PDE.RicciFlow
