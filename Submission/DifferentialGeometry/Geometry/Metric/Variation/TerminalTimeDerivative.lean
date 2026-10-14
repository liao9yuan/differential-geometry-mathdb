import Submission.DifferentialGeometry.Geometry.Metric.Variation.TimeDerivative
import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem metricTime_hasDerivWithinAt_terminal
    (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ} {x : M}
    {A B : ℝ → Tensor0SSpace r I x} {a b : ℝ} (hab : a < b)
    (hA : ContinuousWithinAt A (Set.Iio b) b)
    (hB : ContinuousWithinAt B (Set.Iio b) b)
    (hcor : ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (A t) (ricciSharp (g t) x))
      (Set.Iio b) b)
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt A
      (B t - covariantEndomorphismAction0S (A t) (ricciSharp (g t) x)) t) :
    HasDerivWithinAt A
      (B b - covariantEndomorphismAction0S (A b) (ricciSharp (g b) x))
      (Set.Iic b) b := by
  refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo a b)
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    (hA.mono Set.Ioo_subset_Iio_self) (Ioo_mem_nhdsLT hab) ?_
  exact (hB.sub hcor).tendsto.congr'
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
      fun t ht => (hderiv t ht).deriv).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricTime_hasDerivWithinAt_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricTime_hasDerivWithinAt_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricTime_hasDerivWithinAt_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricTime_hasDerivWithinAt_terminal

theorem iteratedMetricTimeDerivWithin_eq_of_terminal_tower
    (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ} {x : M}
    (A : ℝ → Tensor0SSpace r I x) (B : ℕ → ℝ → Tensor0SSpace r I x)
    {a b : ℝ} (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioc a b, B 0 t = A t)
    (hB : ∀ q, ContinuousWithinAt (B q) (Set.Iio b) b)
    (hcor : ∀ q, ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x))
      (Set.Iio b) b)
    (hderiv : ∀ q, ∀ t ∈ Set.Ioo a b, HasDerivAt (B q)
      (B (q + 1) t - covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x)) t) :
    ∀ q, ∀ t ∈ Set.Ioc a b,
      iteratedMetricTimeDerivWithin g (Set.Iic b) A q t = B q t ∧
      DifferentiableWithinAt ℝ
        (iteratedMetricTimeDerivWithin g (Set.Iic b) A q) (Set.Iic b) t := by
  have hwithin (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ioc a b) :
      HasDerivWithinAt (B q)
        (B (q + 1) t - covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x))
        (Set.Iic b) t := by
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hderiv q t ⟨ht.1, htb⟩).hasDerivWithinAt
    · exact metricTime_hasDerivWithinAt_terminal g hab (hB q) (hB (q + 1))
        (hcor q) (hderiv q)
  have hlocal (t : ℝ) (ht : t ∈ Set.Ioc a b) : Set.Ioc a b ∈ 𝓝[Set.Iic b] t := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1),
      self_mem_nhdsWithin] with s hs hs'
    exact ⟨hs, hs'⟩
  have heq : ∀ q, ∀ t ∈ Set.Ioc a b,
      iteratedMetricTimeDerivWithin g (Set.Iic b) A q t = B q t := by
    intro q
    induction q with
    | zero => exact fun t ht => (hzero t ht).symm
    | succ q ih =>
      intro t ht
      have hevent : iteratedMetricTimeDerivWithin g (Set.Iic b) A q =ᶠ[𝓝[Set.Iic b] t] B q :=
        Filter.eventuallyEq_of_mem (hlocal t ht) fun s hs => ih s hs
      have hd := (hwithin q t ht).congr_of_eventuallyEq hevent (ih t ht)
      have huniq : UniqueDiffWithinAt ℝ (Set.Iic b) t := uniqueDiffOn_Iic b t ht.2
      change metricTimeDerivWithin g (Set.Iic b)
        (iteratedMetricTimeDerivWithin g (Set.Iic b) A q) t = B (q + 1) t
      rw [metricTimeDerivWithin_eq_of_hasDerivWithinAt g hd huniq, ih t ht]
      exact sub_add_cancel _ _
  intro q t ht
  refine ⟨heq q t ht, ?_⟩
  exact ((hwithin q t ht).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hlocal t ht) fun s hs => heq q s hs)
    (heq q t ht)).differentiableWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower

open _root_.Set in
theorem iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc
    (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ} {x : M}
    (A : ℝ → Tensor0SSpace r I x) (B : ℕ → ℝ → Tensor0SSpace r I x)
    {c a b : ℝ} (hca : c ≤ a) (hab : a < b)
    (hzero : ∀ t ∈ Set.Ioc a b, B 0 t = A t)
    (hB : ∀ q, ContinuousWithinAt (B q) (Set.Iio b) b)
    (hcor : ∀ q, ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x))
      (Set.Iio b) b)
    (hderiv : ∀ q, ∀ t ∈ Set.Ioo a b, HasDerivAt (B q)
      (B (q + 1) t - covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x)) t) :
    ∀ q, ∀ t ∈ Set.Ioc a b,
      iteratedMetricTimeDerivWithin g (Set.Icc c b) A q t = B q t ∧
      DifferentiableWithinAt ℝ
        (iteratedMetricTimeDerivWithin g (Set.Icc c b) A q) (Set.Icc c b) t := by
  have hwithin (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ioc a b) :
      HasDerivWithinAt (B q)
        (B (q + 1) t - covariantEndomorphismAction0S (B q t) (ricciSharp (g t) x))
        (Set.Icc c b) t := by
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · exact (hderiv q t ⟨ht.1, htb⟩).hasDerivWithinAt
    · exact (metricTime_hasDerivWithinAt_terminal g hab (hB q) (hB (q + 1))
        (hcor q) (hderiv q)).mono (fun z hz => hz.2)
  have hlocal (t : ℝ) (ht : t ∈ Set.Ioc a b) : Set.Ioc a b ∈ 𝓝[Set.Icc c b] t := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1), self_mem_nhdsWithin] with s hs hs'
    exact ⟨hs, hs'.2⟩
  have heq : ∀ q, ∀ t ∈ Set.Ioc a b,
      iteratedMetricTimeDerivWithin g (Set.Icc c b) A q t = B q t := by
    intro q
    induction q with
    | zero => exact fun t ht => (hzero t ht).symm
    | succ q ih =>
      intro t ht
      have hevent : iteratedMetricTimeDerivWithin g (Set.Icc c b) A q =ᶠ[𝓝[Set.Icc c b] t] B q :=
        Filter.eventuallyEq_of_mem (hlocal t ht) fun s hs => ih s hs
      have hd := (hwithin q t ht).congr_of_eventuallyEq hevent (ih t ht)
      have huniq : UniqueDiffWithinAt ℝ (Set.Icc c b) t :=
        uniqueDiffOn_Icc (hca.trans_lt hab) t ⟨(hca.trans_lt ht.1).le, ht.2⟩
      change metricTimeDerivWithin g (Set.Icc c b)
        (iteratedMetricTimeDerivWithin g (Set.Icc c b) A q) t = B (q + 1) t
      rw [metricTimeDerivWithin_eq_of_hasDerivWithinAt g hd huniq, ih t ht]
      exact sub_add_cancel _ _
  intro q t ht
  refine ⟨heq q t ht, ?_⟩
  exact ((hwithin q t ht).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hlocal t ht) fun s hs => heq q s hs)
    (heq q t ht)).differentiableWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.iteratedMetricTimeDerivWithin_eq_of_terminal_tower_Icc

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
