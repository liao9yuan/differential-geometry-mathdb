import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureContractions
import Mathlib.Data.Finset.Order

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature (RealTimeInterval)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] {D : RealTimeInterval} {a b : ℝ}

theorem RicciBackground.exists_uniform_product_curvature_bounds
    (A : QuotientProductAtlas I M) (B : RicciBackground (I := I) (M := M) D a b) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ p : M, ∀ kind : CurvatureTensorKind, ∀ j ≤ m,
        Real.sqrt (normSq0S (B.family.metric t) p (kind.arity + j)
          (kind.field B.family j t p)) ≤ C) ∧
      (∀ lambda : ℝ, ∀ hlambda : 0 < lambda,
        letI := A.charts
        letI := A.smoothManifold
        let G := quotientProductFamily A B.family lambda hlambda
        ∀ t ∈ _root_.Set.Icc a b, ∀ q : M × Surgery.Topology.Circle,
          ∀ kind : CurvatureTensorKind, ∀ j ≤ m,
            Real.sqrt (normSq0S (G.metric t) q (kind.arity + j)
              (kind.field G j t q)) ≤ C) := by
  classical
  choose K hK hbase hprod using fun j => B.exists_uniform_product_iterCov_bounds A j
  obtain ⟨C₀, hC₀⟩ := Finset.exists_le ((Finset.range (m + 1)).image K)
  have hKC (j : ℕ) (hj : j ≤ m) : K j ≤ _root_.Max.max 1 C₀ :=
    (hC₀ (K j) (Finset.mem_image_of_mem K (Finset.mem_range.mpr (by omega)))).trans
      (le_max_right 1 C₀)
  refine ⟨max 1 C₀, le_max_left 1 C₀, ?_, ?_⟩
  · intro t ht p kind j hj
    have hbound : normSq0S (B.family.metric t) p (kind.arity + j)
        (kind.field B.family j t p) ≤ (K j) ^ 2 := by
      cases kind with
      | ricci => exact (hbase j t ht p).2
      | riemann => exact (hbase j t ht p).1
    calc
      _ ≤ Real.sqrt ((K j) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = K j := Real.sqrt_sq (zero_le_one.trans (hK j))
      _ ≤ _root_.Max.max 1 C₀ := hKC j hj
  · intro lambda hlambda
    let _ := A.charts
    let _ := A.smoothManifold
    dsimp only
    intro t ht q kind j hj
    have hbound : normSq0S ((quotientProductFamily A B.family lambda hlambda).metric t) q
        (kind.arity + j) (kind.field (quotientProductFamily A B.family lambda hlambda) j t q) ≤
        (K j) ^ 2 := by
      cases kind with
      | ricci => exact (hprod j lambda hlambda t ht q).2
      | riemann => exact (hprod j lambda hlambda t ht q).1
    calc
      _ ≤ Real.sqrt ((K j) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = K j := Real.sqrt_sq (zero_le_one.trans (hK j))
      _ ≤ _root_.Max.max 1 C₀ := hKC j hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.exists_uniform_product_curvature_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.exists_uniform_product_curvature_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.exists_uniform_product_curvature_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.RicciBackground.exists_uniform_product_curvature_bounds

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
