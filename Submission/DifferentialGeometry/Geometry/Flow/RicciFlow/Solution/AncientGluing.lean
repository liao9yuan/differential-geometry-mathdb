import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import Submission.DifferentialGeometry.Geometry.Metric.Family.TimeGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_ancient_solution_of_compatible_open_cover
    (U : ℕ → _root_.TopologicalSpace.Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    (g : ∀ n, ℝ → SmoothRiemannianMetric I (U n))
    (hg : ∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I) (M := U n)
      (RealTimeInterval.closed (-((n + 1 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    (hcompat : ∀ n m, ∀ t ∈ _root_.Set.Icc (-((n + 1 : ℕ) : ℝ)) 0,
      t ∈ _root_.Set.Icc (-((m + 1 : ℕ) : ℝ)) 0 →
      (g n t).restrictOpenOfSubset (inf_le_left : U n ⊓ U m ≤ U n) =
        (g m t).restrictOpenOfSubset (inf_le_right : U n ⊓ U m ≤ U m)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
      ∀ n t, t ∈ _root_.Set.Icc (-((n + 1 : ℕ) : ℝ)) 0 → (G t).restrictOpen (U n) = g n t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨G, hG⟩ := exists_metric_family_of_compatible_open_covers
    U (fun n => _root_.Set.Icc (-((n + 1 : ℕ) : ℝ)) 0) (_root_.Set.Iic 0) ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl)⟩ g (by
      intro t ht x
      obtain ⟨k, hk⟩ := hcover x
      obtain ⟨m, hm⟩ := exists_nat_ge (-t)
      refine ⟨max k m, ⟨?_, ht⟩, hU (le_max_left _ _) hk⟩
      have hn : (m : ℝ) ≤ (_root_.Max.max k m : ℕ) := Nat.cast_le.mpr (le_max_right _ _)
      rw [Nat.cast_add, Nat.cast_one]
      linarith) (fun n m t _ hn hm => hcompat n m t hn hm)
  refine ⟨G, ?_, fun n t ht => hG n t ht.2 ht⟩
  apply isSolutionOn_of_closed_backward_windows
    ({ base.metric := G } : SolutionOn (I := I) (M := M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (T := 0) Subset.rfl
  intro n
  apply isSolutionOn_of_open_cover G (fun k => U (n + k))
    (fun x => by
      obtain ⟨k, hk⟩ := hcover x
      exact ⟨k, hU (Nat.le_add_left _ _) hk⟩)
  intro k
  have hn : (n + 1 : ℕ) ≤ n + k + 1 := by omega
  have hcar : _root_.Set.Icc (0 - ((n + 1 : ℕ) : ℝ)) 0 ⊆ _root_.Set.Icc (-((n + k + 1 : ℕ) : ℝ)) 0 := by
    intro t ht
    exact ⟨by have := Nat.cast_le (α := ℝ).mpr hn; linarith [ht.1], ht.2⟩
  have hreg : _root_.Set.Ioo (0 - ((n + 1 : ℕ) : ℝ)) 0 ⊆ _root_.Set.Ioo (-((n + k + 1 : ℕ) : ℝ)) 0 := by
    intro t ht
    exact ⟨by have := Nat.cast_le (α := ℝ).mpr hn; linarith [ht.1], ht.2⟩
  have hlocal := isSolutionOn_timeRestrict (hg (n + k))
    (D' := RealTimeInterval.closed (0 - ((n + 1 : ℕ) : ℝ)) 0
      (sub_le_self _ (Nat.cast_nonneg _))) hcar hreg
  exact hlocal.congr_metric (fun t ht => (hG (n + k) t ht.2 (hcar ht)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_ancient_solution_of_compatible_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_ancient_solution_of_compatible_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_ancient_solution_of_compatible_open_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_ancient_solution_of_compatible_open_cover

end DifferentialGeometry.PDE.RicciFlow
end
