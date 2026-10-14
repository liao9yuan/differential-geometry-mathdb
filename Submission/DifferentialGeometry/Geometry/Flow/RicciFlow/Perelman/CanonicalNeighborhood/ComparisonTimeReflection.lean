import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
  {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : N → M} {U : Set N}

def MetricComparisonOn.reflectTime
    {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps)
    (tau : ℝ) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hmap : _root_.Set.MapsTo (fun s => tau - s) J times)
    (hdiff : ∀ b s, s ∈ J → ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      DifferentiableWithinAt ℝ (fun r => C.jet b r y v) times (tau - s)) :
    MetricComparisonOn (fun s => h (tau - s)) (fun s => g (tau - s)) F U J order eps where
  pullback s := C.pullback (tau - s)
  pullback_eq s y hy v := C.pullback_eq (tau - s) y hy v
  jet b s := (-1 : ℝ) ^ b • C.jet b (tau - s)
  jet_zero := by
    intro s y v
    simp only [pow_zero, one_smul, C.jet_zero]
  jet_succ := by
    intro b s hs y hy v
    have hd : HasDerivWithinAt (fun r => C.jet b r y v)
        (C.jet (b + 1) (tau - s) y v) times (tau - s) := by
      rw [C.jet_succ b _ (hmap hs) y hy v]
      exact (hdiff b s hs y hy v).hasDerivWithinAt
    have ht : HasDerivAt (fun r : ℝ => tau - r) (-1) s := (hasDerivAt_id s).const_sub tau
    have hh := ((hd.scomp s ht.hasDerivWithinAt hmap).const_mul ((-1 : ℝ) ^ b)).derivWithin (hJ s hs)
    simpa only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, Function.comp_def, pow_succ, mul_assoc] using hh.symm
  equivalence s hs y hy v := C.equivalence _ (hmap hs) y hy v
  close := by
    intro a b hab s hs y hy
    rw [tensor02CovDerivNormWith_smul]
    simpa only [abs_pow, abs_neg, abs_one, one_pow, one_mul] using C.close a b hab _ (hmap hs) y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.reflectTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.reflectTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.reflectTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.reflectTime

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
