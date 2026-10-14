import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveSmoothLift
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoverCovariantDerivative
import Mathlib.Analysis.Calculus.TangentCone.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem uniqueMDiffWithinAt_of_mem_Ico_or_Icc {s u t : ℝ} {J : Set ℝ} (hsu : s < u)
    (hJ : J = _root_.Set.Ico s u ∨ J = _root_.Set.Icc s u) (ht : t ∈ J) :
    UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t := by
  have h : UniqueDiffWithinAt ℝ J t := by
    rcases hJ with rfl | rfl
    · exact uniqueDiffOn_Ico s u t ht
    · exact uniqueDiffOn_Icc hsu t ht
  exact h.uniqueMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniqueMDiffWithinAt_of_mem_Ico_or_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniqueMDiffWithinAt_of_mem_Ico_or_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniqueMDiffWithinAt_of_mem_Ico_or_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.uniqueMDiffWithinAt_of_mem_Ico_or_Icc

namespace ProductCurve

omit [CompleteSpace E] in
theorem map_isSolutionOn_of_frontiers
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {J : Set ℝ}
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t)
    (hc : c.IsSolutionOn g lambda J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  exact c.map_isSolutionOn_of_isSolutionOn A g lambda hlambda huniq hc hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_isSolutionOn_of_frontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_isSolutionOn_of_frontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_isSolutionOn_of_frontiers ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.map_isSolutionOn_of_frontiers

omit [CompleteSpace E] in
theorem isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {J : Set ℝ}
    (hyc : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J))
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t)
    (hm : letI := A.charts
      letI := A.smoothManifold
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    c.IsSolutionOn g lambda J := by
  let := A.charts
  let := A.smoothManifold
  have hc : c.SmoothOn (I := I) J := (c.coverSmoothLift_of_continuousOn_height A J hyc) hm.smooth
  refine ⟨hc, (c.map_immersedOn_iff A hc).mp hm.immersed, ?_⟩
  intro x t ht
  have h1 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
      (c.coverLift x t) (c.velocity (I := I) J x t) =
      c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
    (c.map_velocity_eq A J hc x t ht (huniq t ht)).symm
  have h2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
      (c.coverLift x t) (c.curvatureVector (I := I) g lambda x t) =
      c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
    (c.map_curvatureVector_eq A g lambda hlambda hc hU x t ht).trans
      (hm.equation x t ht).symm
  exact (A.cover_derivative_bijective (c.coverLift x t)).injective (h1.trans h2.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem Field.smoothOn_X (c : ProductCurve M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J) :
    (c.X (I := I)).SmoothOn (I := I) J := by
  have hjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) ((_root_.Set.univ : Set ℝ) ×ˢ J) := by
    intro p hp
    exact (hc.1 p hp).prodMk (hc.2 p hp).contMDiffWithinAt
  have hcover : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) ((_root_.Set.univ : Set ℝ) ×ˢ J) := by
    have h := hjoint
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hj := ContMDiffOn.time_mfderivWithin (I := 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, ℝ))
    (N := M × ℝ) (γ := fun x t => c.coverLift x t) (s := (_root_.Set.univ : Set ℝ)) (u := J)
    (n := ∞) (m := ∞) hcover uniqueDiffOn_univ le_rfl
  intro t ht
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x : ℝ => (⟨c.coverLift x t, mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun y => c.coverLift y t) _root_.Set.univ x (1 : ℝ)⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) univ :=
    hj.comp (contMDiffOn_id.prodMk contMDiffOn_const) (fun x _ => ⟨mem_univ x, ht⟩)
  exact contMDiffOn_univ.mp (hslice.congr (fun x _ => by
    have hx : mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun y => c.coverLift y t) _root_.Set.univ x
        (1 : ℝ) = c.X (I := I) x t := by
      rw [mfderivWithin_univ]
      exact c.cover_spatial_derivative (I := I) J hc x t ht
    rw [hx]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field.smoothOn_X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field.smoothOn_X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field.smoothOn_X ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.Field.smoothOn_X

omit [CompleteSpace E] in
theorem product_solution_iff_of_frontiers
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {s u : ℝ} (hsu : s < u) {J : Set ℝ}
    (hJ : J = _root_.Set.Ico s u ∨ J = _root_.Set.Icc s u)
    (hyc : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (_root_.Set.univ ×ˢ J))
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.IsSolutionOn g lambda J ↔
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t :=
    fun _ ht => uniqueMDiffWithinAt_of_mem_Ico_or_Icc hsu hJ ht
  exact ⟨c.map_isSolutionOn_of_frontiers A g lambda hlambda hU huniq,
    c.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift A g lambda hlambda
      hyc hU huniq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.product_solution_iff_of_frontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.product_solution_iff_of_frontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.product_solution_iff_of_frontiers ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.product_solution_iff_of_frontiers

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
