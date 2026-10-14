import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import Submission.DifferentialGeometry.Geometry.Metric.Family.TimeGluing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Family.OpenCover
import Submission.DifferentialGeometry.Topology.OpenCover.ProductContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isSolutionOn_of_open_cover
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    {ι : Type*} (U : ι → _root_.TopologicalSpace.Opens M) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hg : ∀ i, IsSolutionOn ({ base.metric := fun t => (g t).restrictOpen (U i) } :
      SolutionOn (I := I) (M := U i) D)) :
    IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M) D) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply isSolutionOn_of_reg g (MetricFamilySmoothOn.of_open_cover U hcover
    (fun i => (hg i).smoothMetric))
  · intro t ht x v w
    obtain ⟨i, hxi⟩ := hcover x
    have h := ((hg i).equation ⟨t, ht⟩ ⟨x, hxi⟩ v w).hasDerivAt (D.regular_mem_nhds ht)
    change HasDerivAt (fun s => (g s).inner x v w)
      (-2 * metricRicciAt (I := I) ((g t).restrictOpen (U i)) ⟨x, hxi⟩
        (vec2 v w)) t at h
    rw [metricRicciAt_apply_eq_ricciTensor (I := I) ((g t).restrictOpen (U i))
      (⟨x, hxi⟩ : U i) v w] at h
    have hr := DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen (I := I) (g t) (U i) (⟨x, hxi⟩ : U i) v w
    rw [mfderiv_subtype_val (I := I) (U i) (⟨x, hxi⟩ : U i)] at hr
    exact h.congr_deriv (congrArg (fun r : ℝ => -2 * r) hr)
  · apply continuousOn_of_open_cover_prod U hcover
    intro i
    have heq (q : ℝ × U i) :
        metricScalarAt (I := I) ((g q.1).restrictOpen (U i)) q.2 =
          metricScalarAt (I := I) (g q.1) (q.2 : M) :=
      metricScalarAt_restrictOpen (g q.1) (U i) q.2
    have hc : ContinuousOn
        (fun q : ℝ × U i => metricScalarAt (I := I) ((g q.1).restrictOpen (U i)) q.2)
        (D.carrier ×ˢ _root_.Set.univ) := (hg i).scalarCont
    simp only [_root_.Set.preimage_univ]
    exact hc.congr (fun q _ => (heq q).symm)
  · intro t ht x
    obtain ⟨i, hxi⟩ := hcover x
    have heq : (fun s => metricScalarAt (I := I) ((g s).restrictOpen (U i)) ⟨x, hxi⟩) =
        (fun s => metricScalarAt (I := I) (g s) x) := by
      funext s
      exact metricScalarAt_restrictOpen (g s) (U i) ⟨x, hxi⟩
    have h := (hg i).scalarTime ht Subset.rfl ⟨x, hxi⟩
    change DifferentiableWithinAt ℝ
      (fun s => metricScalarAt (I := I) ((g s).restrictOpen (U i)) ⟨x, hxi⟩) D.carrier t at h
    rwa [heq] at h
  · apply tensor0SFamilyContinuousOnSet.of_open_cover U _ hcover
    intro i
    apply (hg i).ricciCont.congr
    intro t _ x
    ext slots
    exact (metricRicci_restrictOpen_eval (g t) (U i) x slots).trans (by
      simp only [mfderiv_subtype_val_apply]
      rfl)
  · apply tensor0SFamilyContinuousOnSet.of_open_cover U _ hcover
    intro i
    apply (hg i).rm04Cont.congr
    intro t _ x
    ext slots
    exact (metricRm04_restrictOpen_eval (g t) (U i) x slots).trans (by
      simp only [mfderiv_subtype_val_apply]
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_open_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_open_cover

theorem exists_solution_of_compatible_open_cover
    {D : RealTimeInterval} {ι : Type*} (U : ι → _root_.TopologicalSpace.Opens M)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (g : ∀ i, ℝ → SmoothRiemannianMetric I (U i))
    (hg : ∀ i, IsSolutionOn ({ base.metric := g i } : SolutionOn (I := I) (M := U i) D))
    (hcompat : ∀ i j t, t ∈ D.carrier →
      (g i t).restrictOpenOfSubset (inf_le_left : U i ⊓ U j ≤ U i) =
        (g j t).restrictOpenOfSubset (inf_le_right : U i ⊓ U j ≤ U j)) :
    ∃ G : ℝ → SmoothRiemannianMetric I M,
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I) (M := M) D) ∧
      ∀ i t, t ∈ D.carrier → (G t).restrictOpen (U i) = g i t := by
  obtain ⟨G, hG⟩ := DifferentialGeometry.Geometry.Metric.exists_metric_family_of_compatible_open_covers U
    (fun _ => D.carrier) D.carrier ⟨D.initial, D.initial_mem⟩ g
    (fun t ht x => by
      obtain ⟨i, hi⟩ := hcover x
      exact ⟨i, ht, hi⟩)
    (fun i j t ht _ _ => hcompat i j t ht)
  refine ⟨G, isSolutionOn_of_open_cover G U hcover (fun i => ?_),
    fun i t ht => hG i t ht ht⟩
  exact (hg i).congr_metric (fun t ht => (hG i t ht ht).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_solution_of_compatible_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_solution_of_compatible_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_solution_of_compatible_open_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_solution_of_compatible_open_cover

end DifferentialGeometry.PDE.RicciFlow
end
