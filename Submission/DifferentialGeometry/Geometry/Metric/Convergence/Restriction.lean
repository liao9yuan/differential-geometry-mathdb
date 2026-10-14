import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.Compactness
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem MetricCInfConvergenceOnCompacts.comp_subseq
    {G : ℕ → SmoothRiemannianMetric I M} {g r : SmoothRiemannianMetric I M}
    (h : MetricCInfConvergenceOnCompacts G g r)
    {rho : ℕ → ℕ} (hrho : StrictMono rho) :
    MetricCInfConvergenceOnCompacts (fun i => G (rho i)) g r := by
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := h K hK p epsilon hepsilon
  exact ⟨N, fun i hi => hN (rho i) (hi.trans (hrho.id_le i))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.comp_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.comp_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.comp_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.comp_subseq

theorem MetricCInfConvergenceOnCompacts.congr
    {G G' : ℕ → SmoothRiemannianMetric I M} {g r : SmoothRiemannianMetric I M}
    (h : MetricCInfConvergenceOnCompacts G g r) (hseq : G =ᶠ[_root_.Filter.atTop] G') :
    MetricCInfConvergenceOnCompacts G' g r := by
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := h K hK p epsilon hepsilon
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hseq
  refine ⟨max N N', fun i hi => ?_⟩
  rw [← hN' i (le_max_right N N' |>.trans hi)]
  exact hN i (le_max_left N N' |>.trans hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.congr ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.congr

theorem MetricCInfConvergenceOnCompacts.restrictOpen
    {G : ℕ → SmoothRiemannianMetric I M} {g r : SmoothRiemannianMetric I M}
    (h : MetricCInfConvergenceOnCompacts G g r)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] :
    MetricCInfConvergenceOnCompacts (fun i => (G i).restrictOpen U)
      (g.restrictOpen U) (r.restrictOpen U) := by
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := h (Subtype.val '' K) (hK.image continuous_subtype_val)
    p epsilon hepsilon
  refine ⟨N, fun i hi => ?_⟩
  rw [metricDerivNormSupOn_restrictOpen]
  exact hN i hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpen

theorem MetricCInfConvergenceOnCompacts.restrictOpenOfSubset
    {U V : TopologicalSpace.Opens M} [SigmaCompactSpace U]
    {G : ℕ → SmoothRiemannianMetric I U} {g r : SmoothRiemannianMetric I U}
    (h : MetricCInfConvergenceOnCompacts G g r) (hVU : V ≤ U) :
    MetricCInfConvergenceOnCompacts (fun i => (G i).restrictOpenOfSubset hVU)
      (g.restrictOpenOfSubset hVU) (r.restrictOpenOfSubset hVU) := by
  intro K hK p epsilon hepsilon
  have hK' : IsCompact (TopologicalSpace.Opens.inclusion hVU '' K) :=
    hK.image (contMDiff_inclusion (I := I) (n := ∞) hVU).continuous
  obtain ⟨N, hN⟩ := h _ hK' p (epsilon / 2) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _
    (epsilon / 2) (by positivity) ?_) (by linarith)
  intro a ha x hx
  rw [metricDerivNorm_flat]
  exact (derivNorm_le_sup hK' ha (G i) g r ⟨x, hx, rfl⟩).trans
    (hN i hi).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpenOfSubset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpenOfSubset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpenOfSubset ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.restrictOpenOfSubset

theorem metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq
    {U V W : TopologicalSpace.Opens M}
    [SigmaCompactSpace U] [SigmaCompactSpace V]
    (hWU : W ≤ U) (hWV : W ≤ V)
    {GU : ℕ → SmoothRiemannianMetric I U} {GV : ℕ → SmoothRiemannianMetric I V}
    {gU rU : SmoothRiemannianMetric I U} {gV rV : SmoothRiemannianMetric I V}
    (hU : MetricCInfConvergenceOnCompacts GU gU rU)
    (hV : MetricCInfConvergenceOnCompacts GV gV rV)
    (hsource : (fun i => (GU i).restrictOpenOfSubset hWU) =ᶠ[_root_.Filter.atTop]
      (fun i => (GV i).restrictOpenOfSubset hWV)) :
    gU.restrictOpenOfSubset hWU = gV.restrictOpenOfSubset hWV := by
  exact metricCInf_unique (fun i => (GV i).restrictOpenOfSubset hWV)
    (gU.restrictOpenOfSubset hWU) (gV.restrictOpenOfSubset hWV)
    (rU.restrictOpenOfSubset hWU) (rV.restrictOpenOfSubset hWV)
    ((hU.restrictOpenOfSubset hWU).congr hsource) (hV.restrictOpenOfSubset hWV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq

end DifferentialGeometry.CheegerGromovCompactness
