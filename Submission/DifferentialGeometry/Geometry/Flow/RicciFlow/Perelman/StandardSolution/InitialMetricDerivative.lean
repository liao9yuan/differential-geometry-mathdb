import Mathlib.Analysis.Calculus.FDeriv.Extend
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem metric_right_derivative_of_interior
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t => (g t).inner x v w) (_root_.Set.Ico a b))
    (hRic : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun t => ricciTensor (g t) x v w) (_root_.Set.Ico a b))
    (hRF : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (g t).inner x v w)
      (-2 * ricciTensor (g a) x v w) (_root_.Set.Ici a) a := by
  have ha : a ∈ _root_.Set.Ico a b := ⟨le_rfl, hab⟩
  have hlim := ((hRic x v w) a ha).mono _root_.Set.Ioo_subset_Ico_self
  change _root_.Filter.Tendsto (fun t => ricciTensor (g t) x v w)
    (𝓝[_root_.Set.Ioo a b] a) (𝓝 (ricciTensor (g a) x v w)) at hlim
  rw [nhdsWithin_Ioo_eq_nhdsGT hab] at hlim
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hRF t ht x v w).differentiableAt.differentiableWithinAt)
    (((hg x v w) a ha).mono _root_.Set.Ioo_subset_Ico_self) (Ioo_mem_nhdsGT hab)
  apply (tendsto_const_nhds.mul hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  exact (hRF t ht x v w).deriv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_right_derivative_of_interior

variable [CompleteSpace E]

theorem initial_metric_derivative
    {a b : ℝ} (hab : a < b)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab))
    (hS : IsSolutionOn S) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun t => (S.base.metric t).inner x v w)
      (-2 * ricciTensor (S.base.metric a) x v w) (_root_.Set.Ici a) a := by
  apply metric_right_derivative_of_interior hab S.base.metric
  · exact hS.smoothMetric.coeff_cont
  · intro y u z
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : _root_.Set.Ico a b => ricciTensor (S.base.metric t.val) y u z)
    have h := hS.ricciCont.eval_continuous
      (P := _root_.Set.Ico a b) (τ := Subtype.val) (b := fun _ => y)
      continuous_subtype_val (fun t => t.property) continuous_const
      (v := fun i _ => vec2 u z i) (fun _ => continuous_const)
    simpa only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using h
  · intro t ht y u z
    have h := metricDerivAt S hS ⟨t, ht⟩ y u z
    change HasDerivAt (fun s => (S.base.metric s).inner y u z)
      (-2 * metricRicciAt (S.base.metric t) y (vec2 u z)) t at h
    rw [metricRicciAt_apply_eq_ricciTensor] at h
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative ``Submission.DifferentialGeometry.PDE.RicciFlow.initial_metric_derivative
end DifferentialGeometry.PDE.RicciFlow
