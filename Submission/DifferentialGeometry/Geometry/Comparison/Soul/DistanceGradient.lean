import Submission.DifferentialGeometry.Geometry.Comparison.Soul.DistanceEscape
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Mathlib.Analysis.Calculus.TangentCone.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem dist_intrinsicGeodesic_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    _root_.Dist.dist (intrinsicGeodesic g hEnorm p v s) (intrinsicGeodesic g hEnorm p v t) ≤
      Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm p v hst
  rw [← IsRiemannianManifold.out (I := I), edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hst))).mp h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.dist_intrinsicGeodesic_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.dist_intrinsicGeodesic_le target :: scope.openDecls } }

theorem infDist_intrinsicGeodesic_to_set
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} {q : M} {u : TangentSpace I q}
    (hu : g.inner q u u = 1)
    (hend : intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 (Metric.infDist q S)) :
    Metric.infDist (intrinsicGeodesic g hEnorm q u t) S = Metric.infDist q S - t := by
  let γ := intrinsicGeodesic g hEnorm q u
  have hupper : Metric.infDist (γ t) S ≤ Metric.infDist q S - t := by
    have h := dist_intrinsicGeodesic_le g hEnorm q u ht.2
    rw [hu, Real.sqrt_one, one_mul] at h
    exact (Metric.infDist_le_dist_of_mem hend).trans h
  have hdist : _root_.Dist.dist q (γ t) ≤ t := by
    have h := dist_intrinsicGeodesic_le g hEnorm q u ht.1
    simpa only [intrinsicGeodesic_zero, hu, Real.sqrt_one, one_mul, sub_zero] using h
  have htriangle : Metric.infDist q S ≤ Metric.infDist (γ t) S + _root_.Dist.dist q (γ t) :=
    Metric.infDist_le_infDist_add_dist
  exact le_antisymm hupper (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.infDist_intrinsicGeodesic_to_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.infDist_intrinsicGeodesic_to_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.infDist_intrinsicGeodesic_to_set ``Submission.DifferentialGeometry.Geometry.Topology.infDist_intrinsicGeodesic_to_set

theorem gradient_infDist_inner_minimizing
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} {q : M} (hq : 0 < Metric.infDist q S)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => Metric.infDist x S) q)
    {u : TangentSpace I q} (hu : g.inner q u u = 1)
    (hend : intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S) :
    g.inner q (gradientFun g (fun x => Metric.infDist x S) q) u = -1 := by
  let f := fun x : M => Metric.infDist x S
  let γ := intrinsicGeodesic g hEnorm q u
  have hγ0 : γ 0 = q := intrinsicGeodesic_zero g hEnorm q u
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm q u
  have hcomp := hasDerivAt_comp_mfderiv_along I f γ 0
    (by simpa only [hγ0] using hd) (hγ.contMDiffAt.mdifferentiableAt (by simp))
  have hlinear : HasDerivAt (fun t : ℝ => f q - t) (-1) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).const_sub (f q) using 1
  have hevent : (fun t : ℝ => f (γ t)) =ᶠ[𝓝[_root_.Set.Ici 0] 0] (fun t => f q - t) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hq)] with t ht ht'
    exact infDist_intrinsicGeodesic_to_set g hEnorm hu hend ⟨ht, ht'.le⟩
  have hright : HasDerivWithinAt (fun t => f (γ t)) (-1) (_root_.Set.Ici 0) 0 :=
    hlinear.hasDerivWithinAt.congr_of_eventuallyEq hevent (by rw [hγ0, sub_zero])
  have heq := UniqueDiffWithinAt.eq_deriv (_root_.Set.Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici 0)
    hcomp.hasDerivWithinAt hright
  change mvfderiv (I := I) f (γ 0)
    (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = -1 at heq
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (u : E) :=
    intrinsicGeodesic_mfderiv_zero g hEnorm q u
  rw [hvel] at heq
  erw [hγ0] at heq
  simpa only [inner_gradientFun] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_infDist_inner_minimizing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_infDist_inner_minimizing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_infDist_inner_minimizing ``Submission.DifferentialGeometry.Geometry.Topology.gradient_infDist_inner_minimizing

theorem gradient_infDist_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) {q : M}
    (hq : 0 < Metric.infDist q S)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => Metric.infDist x S) q) :
    g.inner q (gradientFun g (fun x => Metric.infDist x S) q)
      (gradientFun g (fun x => Metric.infDist x S) q) = 1 := by
  obtain ⟨ρ, u, hρ, hval, hupper, hu, _, hgrad⟩ :=
    infDist_upper_support g hEnorm hS hSne q hq
  have hmin : IsLocalMin (fun x => ρ x - Metric.infDist x S) q := by
    filter_upwards [hupper] with x hx
    rw [hval, sub_self]
    exact sub_nonneg.mpr hx
  have hz := gradientFun_eq_zero_of_isLocalMin g hmin
    ((hρ.mdifferentiableAt (by simp)).sub hd)
  rw [gradientFun_sub g (hρ.mdifferentiableAt (by simp)) hd] at hz
  have heq := (sub_eq_zero.mp hz).symm
  rw [heq, hgrad]
  simpa only [map_neg, neg_apply, neg_neg] using hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_infDist_normSq_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_infDist_normSq_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_infDist_normSq_eq_one ``Submission.DifferentialGeometry.Geometry.Topology.gradient_infDist_normSq_eq_one

theorem gradient_infDist_eq_neg_minimizing
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsCompact S) (hSne : S.Nonempty) {q : M}
    (hq : 0 < Metric.infDist q S)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => Metric.infDist x S) q)
    {u : TangentSpace I q} (hu : g.inner q u u = 1)
    (hend : intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S) :
    gradientFun g (fun x => Metric.infDist x S) q = -u := by
  let G := gradientFun g (fun x => Metric.infDist x S) q
  have hGG : g.inner q G G = 1 := gradient_infDist_normSq_eq_one g hEnorm hS hSne hq hd
  have hGu : g.inner q G u = -1 := gradient_infDist_inner_minimizing g hEnorm hq hd hu hend
  have huG : g.inner q u G = -1 := (g.symm q u G).trans hGu
  have hzero : g.inner q (G + u) (G + u) = 0 := by
    simp only [map_add, add_apply, hGG, hGu, huG, hu]
    norm_num
  have hsum : G + u = 0 := by
    by_contra h
    have hp := g.pos q (G + u) h
    rw [hzero] at hp
    exact lt_irrefl 0 hp
  exact eq_neg_iff_add_eq_zero.mpr hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_infDist_eq_neg_minimizing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_infDist_eq_neg_minimizing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_infDist_eq_neg_minimizing ``Submission.DifferentialGeometry.Geometry.Topology.gradient_infDist_eq_neg_minimizing

theorem infDist_gradient_smooth_outward_on
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S U : Set M} (hS : IsCompact S) (hSne : S.Nonempty) (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => Metric.infDist x S) U)
    (hpos : ∀ q ∈ U, 0 < Metric.infDist q S) :
    ContMDiffOn I I.tangent ∞
      (T% fun q => gradientFun g (fun x => Metric.infDist x S) q) U ∧
    ∀ q ∈ U, g.inner q (gradientFun g (fun x => Metric.infDist x S) q)
        (gradientFun g (fun x => Metric.infDist x S) q) = 1 ∧
      ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
        g.inner q (gradientFun g (fun x => Metric.infDist x S) q) u = -1 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    exact (gradientFun_contMDiffAt g ((hf q hq).contMDiffAt (hU.mem_nhds hq))).contMDiffWithinAt
  · intro q hq
    have hd := ((hf q hq).contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt (by simp)
    exact ⟨gradient_infDist_normSq_eq_one g hEnorm hS hSne (hpos q hq) hd,
      fun _ hu hend => gradient_infDist_inner_minimizing g hEnorm (hpos q hq) hd hu hend⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.infDist_gradient_smooth_outward_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.infDist_gradient_smooth_outward_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.infDist_gradient_smooth_outward_on ``Submission.DifferentialGeometry.Geometry.Topology.infDist_gradient_smooth_outward_on

end DifferentialGeometry.Geometry.Topology
