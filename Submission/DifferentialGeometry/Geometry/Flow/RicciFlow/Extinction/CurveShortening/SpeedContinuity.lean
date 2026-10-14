import Submission.DifferentialGeometry.Bundle.VelocityLift.Continuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]

theorem immersedOn_closure_of_speed_lower_bound
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ} {c : CurveMap M} {m : ℝ → ℝ}
    (hspeed : ∀ x, ContinuousOn (fun t => c.speed g x t) (closure J))
    (hm : ∀ x, 0 < m x) (hbound : ∀ x t, t ∈ J → m x ≤ c.speed g x t) :
    c.ImmersedOn (I := I) (closure J) := by
  intro x t ht
  have hs : ContinuousOn (fun t => c.speed g x t) (closure J) := hspeed x
  have hclosed : m x ≤ c.speed g x t :=
    le_on_closure (fun s hs => hbound x s hs) continuousOn_const hs ht
  intro hzero
  have hzero' : c.speed g x t = 0 := by simp [speed, hzero]
  exact (hm x).not_ge (hzero' ▸ hclosed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_closure_of_speed_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_closure_of_speed_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_closure_of_speed_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_closure_of_speed_lower_bound

variable [FiniteDimensional ℝ E]

theorem continuousOn_speed_of_leftInverse
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) {c : CurveMap M}
    (e : M → F) (r : F → M) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U)
    (hmem : ∀ x t, t ∈ J → e (c.lift x t) ∈ U)
    (hleft : ∀ x t, t ∈ J → r (e (c.lift x t)) = c.lift x t)
    (hslice : ∀ t ∈ J, Differentiable ℝ (fun x => e (c.lift x t)))
    (hval : ContinuousOn (fun p : ℝ × ℝ => e (c.lift p.1 p.2)) (_root_.Set.univ ×ˢ J))
    (hder : ContinuousOn (fun p : ℝ × ℝ => deriv (fun x => e (c.lift x p.2)) p.1)
      (_root_.Set.univ ×ˢ J)) :
    ContinuousOn (fun p : ℝ × ℝ => c.speed g p.1 p.2) (_root_.Set.univ ×ˢ J) := by
  have hX := continuousOn_velocityLift_slice_of_leftInverse c.lift e r hU hr
    hmem hleft hslice hval hder
  rw [continuousOn_iff_continuous_domRestrict]
  have hXs := continuousOn_iff_continuous_domRestrict.mp hX
  have ht : Continuous (fun p : ↥(_root_.Set.univ ×ˢ J) => (⟨p.1.2, p.2.2⟩ : J)) :=
    (show Continuous (fun p : ↥((_root_.Set.univ : Set ℝ) ×ˢ J) => p.1.2) from
      continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hq := (metricTimeBundleQuad_cont_of_metricFamilySmoothOn g hG hJ).comp
    (ht.prodMk hXs)
  exact Real.continuous_sqrt.comp hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_speed_of_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_speed_of_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_speed_of_leftInverse ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_speed_of_leftInverse

theorem immersedOn_Icc_of_leftInverse_of_speed_lower_bound
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {a T m : ℝ} (haT : a < T) (hJ : _root_.Set.Icc a T ⊆ D.carrier)
    {c : CurveMap M} (e : M → F) (r : F → M) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U)
    (hmem : ∀ x t, t ∈ _root_.Set.Icc a T → e (c.lift x t) ∈ U)
    (hleft : ∀ x t, t ∈ _root_.Set.Icc a T → r (e (c.lift x t)) = c.lift x t)
    (hslice : ∀ t ∈ _root_.Set.Icc a T, Differentiable ℝ (fun x => e (c.lift x t)))
    (hval : ContinuousOn (fun p : ℝ × ℝ => e (c.lift p.1 p.2)) (_root_.Set.univ ×ˢ _root_.Set.Icc a T))
    (hder : ContinuousOn (fun p : ℝ × ℝ => deriv (fun x => e (c.lift x p.2)) p.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a T))
    (hm : 0 < m) (hbound : ∀ x t, t ∈ _root_.Set.Ico a T → m ≤ c.speed g x t) :
    c.ImmersedOn (I := I) (_root_.Set.Icc a T) := by
  have hspeed := continuousOn_speed_of_leftInverse hG hJ e r hU hr
    hmem hleft hslice hval hder
  have hclosure : closure (_root_.Set.Ico a T) = _root_.Set.Icc a T := closure_Ico haT.ne
  rw [← hclosure] at hspeed ⊢
  apply immersedOn_closure_of_speed_lower_bound (m := fun _ => m) ?_ (fun _ => hm) hbound
  intro x
  exact hspeed.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun s hs => ⟨mem_univ x, hs⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_Icc_of_leftInverse_of_speed_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_Icc_of_leftInverse_of_speed_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_Icc_of_leftInverse_of_speed_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.immersedOn_Icc_of_leftInverse_of_speed_lower_bound

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
