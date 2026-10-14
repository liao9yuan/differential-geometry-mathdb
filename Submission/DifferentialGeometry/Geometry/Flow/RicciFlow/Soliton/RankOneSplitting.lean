import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CompleteTrichotomy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Curvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRank
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureKernel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Soliton
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

theorem gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    {σ : Real} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ (by change Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3; simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1)
    :
    HasCurvatureSurfaceProductSplitting (I := I) (M := M) g := by
  have hkern := gradientRicciSoliton_curvatureOperatorKernelAt_parallel g f hσ hcomplete hsol
    (by simp [DifferentialGeometry.Topology.Morse.MorseModel])
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  have hdim : Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hrank' : Module.finrank Real (curvatureOperatorImageAt g x₀
      ⟨metricRm04At g x₀, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x₀⟩) = 1 := by
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
    exact hrank
  have hrankall : ∀ x, Module.finrank Real (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) = 1 := by
    intro x
    exact (gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq g f hσ hcomplete hsol hdim x x₀).trans hrank'
  have hscalar : ∀ x, 0 < metricScalarAt g x := by
    intro x
    exact metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim g x (gradientRicciSoliton_curvatureOperator_nonnegative g f hσ hcomplete hsol hdim x) (hrankall x)
  obtain ⟨S, hSrank, hSfiber, hSparallel⟩ := exists_smooth_parallel_curvatureOperatorImageLine
    hdim g (metricRm04 g) (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule g x) hrankall hkern
  obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσN, h,
      hconnected, hsimplyConnected, hhcomplete, F, hF, hmetric⟩ :=
    exists_global_product_diffeomorph_of_parallel_line (I := I) (M := M) (m := 2) g hcomplete S hSrank hSparallel
  let _ : TopologicalSpace N := topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N := hcs
  let _ : IsManifold (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) (∞ : WithTop ℕ∞) N := hmanifold
  let _ : T2Space N := ht2
  let _ : SigmaCompactSpace N := hσN
  let P : GlobalSurfaceProductSplitting (I := I) (M := M) g := {
    N := N
    metricN := h
    connectedN := hconnected
    simplyConnectedN := hsimplyConnected
    completeN := hhcomplete
    F := F
    line := liftTangentSubbundle (I := I) (M := M) S
    line_rank := by simpa using hSrank
    line_parallel := liftTangentSubbundle_isParallel_of_rank_eq_one g S hSrank hSparallel
    line_compatibility := hF
    isometry := hmetric
  }
  refine ⟨S, P, hSrank, hSfiber, ?_, ?_⟩
  · intro y
    rw [liftTangentSubbundle_fiber]
  · intro y
    have hprod := metricScalarAt_prod_flat P.metricN y (0 : Real)
    have hpull := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross
      (I := (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(Real, Real))
      (J := I) (g := liftedMetric (I := I) g) (Phi := P.F) (x := (y, 0))
    have heqscalar := congrArg
      (fun q : SmoothRiemannianMetric
        ((𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(Real, Real))
        (P.N × Real) => metricScalarAt q (y, 0)) (P.pullbackMetric_eq_prod g)
    rw [hprod] at heqscalar
    rw [← heqscalar, hpull, metricScalarAt_lifted]
    exact hscalar _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one
end DifferentialGeometry.Geometry
