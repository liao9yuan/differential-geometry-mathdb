import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def metricComparisonOnSelf (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (id : M → M) U times order eps where
  pullback s := metricTensorField (I := I3) (g s)
  pullback_eq := by
    intro s y hy v
    rw [metricTensorField_apply, mfderiv_id]
    rfl
  jet _ _ := 0
  jet_zero := by
    intro s y v
    simp [metricTensorField_apply, sub_self]
  jet_succ := by
    intro b s hs y hy v
    simp
  equivalence := by
    intro s hs y hy v
    have hnn := inner_self_nonneg (g s) y v
    simp only [metricTensorField_apply]
    constructor <;> nlinarith
  close := by
    intro a b hab s hs y hy
    have hz : tensor02CovDerivNormWith (I := I3) a 0 (g s) (g s) y = 0 := by
      rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
        covDerivOfField_zero_tensor]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero]
    exact hz.le.trans heps.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnSelf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnSelf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnSelf ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnSelf

def metricComparisonOnRefl (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (PartialDiffeomorph.refl (I := I3) M : M → M) U times order eps := by
  have hid : (↑(PartialDiffeomorph.refl (I := I3) M) : M → M) = id := by
    funext x
    rfl
  rw [hid]
  exact metricComparisonOnSelf g U times order heps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnRefl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnRefl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnRefl ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComparisonOnRefl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
