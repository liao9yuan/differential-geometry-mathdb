import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

theorem mfderiv_chartHeight_inwardCoordAt
    (p y : BoundaryManifold (𝓡∂ n) M)
    (hy : (y : M) ∈ (chartAt (EuclideanHalfSpace n) (p : M)).source) :
    (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) (p : M)) (y : M))
      (inwardCoordAt p y) = (1 : ℝ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let u : E := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  have hv : inwardCoordAt p y =
      (mfderivWithin 𝓘(ℝ, E) (𝓡∂ n) (extChartAt (𝓡∂ n) (p : M)).symm
        (_root_.Set.range (𝓡∂ n)) (extChartAt (𝓡∂ n) (p : M) (y : M))) u := by
    unfold inwardCoordAt
    rw [← (_root_.FiberBundle.trivializationAt E (TangentSpace (𝓡∂ n)) (p : M)).symmL_apply (R := ℝ) hy]
    rw [TangentBundle.symmL_trivializationAt hy]
    rfl
  rw [mfderiv_chartHeight (n := n) (p : M) hy]
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := 𝓡∂ n) (x := (p : M)) (y := (y : M)) (by simpa only [extChartAt_source] using hy)
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ, E)
    (extChartAt (𝓡∂ n) (p : M) (y : M)) →L[ℝ] E => A u) hcomp
  rw [hv]
  change (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n))
    ((mfderiv (𝓡∂ n) 𝓘(ℝ, E) (extChartAt (𝓡∂ n) (p : M)) (y : M))
      ((mfderivWithin 𝓘(ℝ, E) (𝓡∂ n) (extChartAt (𝓡∂ n) (p : M)).symm
        (_root_.Set.range (𝓡∂ n)) (extChartAt (𝓡∂ n) (p : M) (y : M))) u)) = 1
  change (mfderiv (𝓡∂ n) 𝓘(ℝ, E) (extChartAt (𝓡∂ n) (p : M)) (y : M))
      ((mfderivWithin 𝓘(ℝ, E) (𝓡∂ n) (extChartAt (𝓡∂ n) (p : M)).symm
        (_root_.Set.range (𝓡∂ n)) (extChartAt (𝓡∂ n) (p : M) (y : M))) u) = u at hh
  rw [hh]
  simp [u, EuclideanSpace.proj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.mfderiv_chartHeight_inwardCoordAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.mfderiv_chartHeight_inwardCoordAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.mfderiv_chartHeight_inwardCoordAt ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.mfderiv_chartHeight_inwardCoordAt


theorem proj_inwardCoordAt_pos
    (p y : BoundaryManifold (𝓡∂ n) M)
    (hy : (y : M) ∈ (chartAt (EuclideanHalfSpace n) (p : M)).source) :
    0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (inwardCoordAt p y) := by
  obtain ⟨c, hc, he⟩ := mfderiv_chartHeight_eq_pos_smul_proj (n := n) (p : M) hy y.2
  have hh := mfderiv_chartHeight_inwardCoordAt p y hy
  erw [he] at hh
  change c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (inwardCoordAt p y) = 1 at hh
  have hpos : 0 < c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (inwardCoordAt p y) := by
    rw [hh]
    exact zero_lt_one
  exact (mul_pos_iff_of_pos_left hc).mp hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.proj_inwardCoordAt_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.proj_inwardCoordAt_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.proj_inwardCoordAt_pos ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.proj_inwardCoordAt_pos

instance instHasOrientableBoundary : HasOrientableBoundary (I := 𝓡∂ n) M where
  inwardCoord_chart_consistent := by
    intro p q y hp hq
    let v₀ : EuclideanSpace ℝ (Fin n) := inwardCoordAt p y
    let v₁ : EuclideanSpace ℝ (Fin n) := inwardCoordAt q y
    let L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)
    have hp0 : 0 < L (inwardCoordAt p y) := proj_inwardCoordAt_pos p y hp
    have hq0 : 0 < L (inwardCoordAt q y) := proj_inwardCoordAt_pos q y hq
    let c : ℝ := L (inwardCoordAt p y) / L (inwardCoordAt q y)
    refine ⟨c, div_pos hp0 hq0, ?_⟩
    change inwardCoordAt p y - c • inwardCoordAt q y ∈ (boundaryInclusionMfderiv y).range
    rw [range_boundaryInclusionMfderiv_eq_ker_proj]
    change L (v₀ - c • v₁) = 0
    rw [map_sub, map_smul]
    change L (inwardCoordAt p y) -
      (L (inwardCoordAt p y) / L (inwardCoordAt q y)) * L (inwardCoordAt q y) = 0
    rw [div_mul_cancel₀ _ (ne_of_gt hq0), sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.instHasOrientableBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.instHasOrientableBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.instHasOrientableBoundary ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.instHasOrientableBoundary

end DifferentialGeometry.Manifold.BoundaryCollar
