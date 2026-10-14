import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]


theorem solution_metric_eq_of_eqOn_Ioo
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a b : ℝ} (hab : a < b)
    (hslab₁ : Set.Icc a b ⊆ D₁.carrier)
    (hslab₂ : Set.Icc a b ⊆ D₂.carrier)
    (heq : ∀ t ∈ Set.Ioo a b, S₁.base.metric t = S₂.base.metric t) :
    S₁.base.metric b = S₂.base.metric b := by
  have hin : (S₁.base.metric b).inner = (S₂.base.metric b).inner := by
    funext x
    ext v w
    have hnear₁ : D₁.carrier ∈ 𝓝[<] b :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Ioo_subset_Icc_self.trans hslab₁)
    have hnear₂ : D₂.carrier ∈ 𝓝[<] b :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Ioo_subset_Icc_self.trans hslab₂)
    have h₁ := ((hS₁.smoothMetric.coeff_cont x v w) b
      (hslab₁ ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear₁
    have h₂ := ((hS₂.smoothMetric.coeff_cont x v w) b
      (hslab₂ ⟨hab.le, le_rfl⟩)).mono_of_mem_nhdsWithin hnear₂
    have hev : (fun t => (S₁.base.metric t).inner x v w) =ᶠ[𝓝[Set.Iio b] b]
        (fun t => (S₂.base.metric t).inner x v w) := by
      filter_upwards [Ioo_mem_nhdsLT hab] with t ht
      rw [heq t ht]
    have h₁' : _root_.Filter.Tendsto (fun t => (S₂.base.metric t).inner x v w)
        (𝓝[Set.Iio b] b) (𝓝 ((S₁.base.metric b).inner x v w)) := h₁.congr' hev
    exact tendsto_nhds_unique h₁' h₂
  generalize S₁.base.metric b = g₁ at hin ⊢
  generalize S₂.base.metric b = g₂ at hin ⊢
  cases g₁
  cases g₂
  cases hin
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solution_metric_eq_of_eqOn_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solution_metric_eq_of_eqOn_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solution_metric_eq_of_eqOn_Ioo ``Submission.DifferentialGeometry.PDE.RicciFlow.solution_metric_eq_of_eqOn_Ioo

theorem solution_metric_eqOn_Icc_of_eqOn_Ico
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a b : ℝ} (hab : a < b)
    (hslab₁ : _root_.Set.Icc a b ⊆ D₁.carrier)
    (hslab₂ : _root_.Set.Icc a b ⊆ D₂.carrier)
    (heq : _root_.Set.EqOn S₁.base.metric S₂.base.metric (_root_.Set.Ico a b)) :
    EqOn S₁.base.metric S₂.base.metric (_root_.Set.Icc a b) := by
  intro t ht
  rcases ht.2.eq_or_lt with htb | htb
  · subst t
    exact solution_metric_eq_of_eqOn_Ioo S₁ S₂ hS₁ hS₂ hab hslab₁ hslab₂
      (fun t ht => heq ⟨ht.1.le, ht.2⟩)
  · exact heq ⟨ht.1, htb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.solution_metric_eqOn_Icc_of_eqOn_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.solution_metric_eqOn_Icc_of_eqOn_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.solution_metric_eqOn_Icc_of_eqOn_Ico ``Submission.DifferentialGeometry.PDE.RicciFlow.solution_metric_eqOn_Icc_of_eqOn_Ico

end DifferentialGeometry.PDE.RicciFlow
