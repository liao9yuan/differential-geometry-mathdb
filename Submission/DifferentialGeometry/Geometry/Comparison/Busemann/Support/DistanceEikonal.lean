import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CorayGradient
import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Support.LineDistanceSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.NNReal _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (_root_.Manifold.riemannianEDist I p q).toReal = _root_.Dist.dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist target :: scope.openDecls } }

private theorem gradient_dist_of_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : M) (v : TangentSpace I q) (hv : 0 < g.inner q v v)
    (hmin : Real.sqrt (g.inner q v v) =
      dist q (intrinsicGeodesic (I := I) g hEnorm q v 1))
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => _root_.Dist.dist q y)
      (intrinsicGeodesic (I := I) g hEnorm q v 1)) :
    gradientFun (I := I) g (fun y => _root_.Dist.dist q y)
        (intrinsicGeodesic (I := I) g hEnorm q v 1) =
      (Real.sqrt (g.inner q v v))⁻¹ •
        curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1 := by
  obtain ⟨rho, hrho, hcontact, hbound, hgrad⟩ :=
    smooth_distance_upper_support_of_minimizing_exp (I := I) g hEnorm q v hv
      (by simpa only [riemannian_toReal_eq_dist (I := I)] using hmin)
  have heq := gradientFun_eq_of_differentiable_lower_support (I := I) g
    (hrho.mdifferentiableAt (by simp)) hd
    (hmin.symm.trans hcontact.symm)
    (by simpa only [riemannian_toReal_eq_dist (I := I)] using hbound)
  exact heq.symm.trans hgrad

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.gradient_dist_of_minimizing_exp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.gradient_dist_of_minimizing_exp target :: scope.openDecls } }

theorem gradient_dist_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q x : M) (hqx : q ≠ x)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => _root_.Dist.dist q y) x) :
    g.inner x (gradientFun (I := I) g (fun y => _root_.Dist.dist q y) x)
      (gradientFun (I := I) g (fun y => _root_.Dist.dist q y) x) = 1 := by
  have hfin : _root_.Manifold.riemannianEDist I q x ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top q x
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top (I := I) g hEnorm q x hfin
  rw [riemannian_toReal_eq_dist (I := I)] at hlen
  have hv : 0 < g.inner q v v := Real.sqrt_pos.mp (hlen.symm ▸ dist_pos.mpr hqx)
  have hend : intrinsicGeodesic (I := I) g hEnorm q v 1 = x := hexp
  have hmin : Real.sqrt (g.inner q v v) =
      dist q (intrinsicGeodesic (I := I) g hEnorm q v 1) := by
    rw [hend]
    exact hlen
  rw [← hend] at hd ⊢
  rw [gradient_dist_of_minimizing_exp (I := I) g hEnorm q v hv hmin hd,
    gInner_smul_self (I := I) g]
  have hspeed : g.inner (intrinsicGeodesic (I := I) g hEnorm q v 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1) =
        g.inner q v v := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q v 1
  rw [hspeed]
  simp only [inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_dist_normSq_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_dist_normSq_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_dist_normSq_eq_one ``Submission.DifferentialGeometry.Geometry.Topology.gradient_dist_normSq_eq_one

theorem gradient_const_sub_dist_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a : ℝ) (q x : M) (hxq : x ≠ q)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => _root_.Dist.dist y q) x) :
    g.inner x (gradientFun (I := I) g (fun y => a - _root_.Dist.dist y q) x)
      (gradientFun (I := I) g (fun y => a - _root_.Dist.dist y q) x) = 1 := by
  rw [gradientFun_sub (I := I) g mdifferentiableAt_const hd, gradientFun_const, zero_sub]
  simp only [map_neg, neg_apply, neg_neg]
  have h := gradient_dist_normSq_eq_one (I := I) g hEnorm q x hxq.symm
    (by simpa only [dist_comm] using hd)
  simpa only [dist_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_const_sub_dist_normSq_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_const_sub_dist_normSq_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_const_sub_dist_normSq_eq_one ``Submission.DifferentialGeometry.Geometry.Topology.gradient_const_sub_dist_normSq_eq_one

theorem exists_open_lineDistanceSupport_eikonal
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ U : Set M, IsOpen U ∧ eta s ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (lineDistanceSupport eta R) U ∧
      ∀ x ∈ U, g.inner x (gradientFun (I := I) g (lineDistanceSupport eta R) x)
        (gradientFun (I := I) g (lineDistanceSupport eta R) x) = 1 := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I)
    g hEnorm p u hu hiso s R hR
  have hne : eta s ≠ eta R := fun h => (ne_of_lt hR) (hiso.injective h)
  refine ⟨U \ {eta R}, hU.sdiff isClosed_singleton, ⟨hx, hne⟩,
    hf.mono _root_.Set.sdiff_subset, ?_⟩
  intro x hx
  have hphi := (hf x hx.1).mdifferentiableWithinAt (by simp)
  have hphiAt : MDifferentiableAt I 𝓘(ℝ, ℝ) (lineDistanceSupport eta R) x :=
    hphi.mdifferentiableAt (hU.mem_nhds hx.1)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => _root_.Dist.dist y (eta R)) x := by
    have ht := (mdifferentiableAt_const (c := R)).sub hphiAt
    change MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => R - lineDistanceSupport eta R y) x at ht
    have heq : (fun y => R - lineDistanceSupport eta R y) = fun y => _root_.Dist.dist y (eta R) := by
      funext y
      dsimp only [lineDistanceSupport]
      ring
    rwa [heq] at ht
  exact gradient_const_sub_dist_normSq_eq_one (I := I) g hEnorm R (eta R) x hx.2 hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_open_lineDistanceSupport_eikonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_open_lineDistanceSupport_eikonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_open_lineDistanceSupport_eikonal ``Submission.DifferentialGeometry.Geometry.Topology.exists_open_lineDistanceSupport_eikonal

theorem gradient_lineDistanceSupport_on_line
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    gradientFun (I := I) g (lineDistanceSupport eta R) (eta s) =
      curveVelocity (I := I) eta s := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hcont : (fun t => eta (t + s)) = intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) := by
    with_unfolding_all exact intrinsicGeodesic_continuation (I := I) g hEnorm p u s
  have hshift : Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) (t : ℝ)) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [← hcont]
    change _root_.Dist.dist (eta ((a : ℝ) + s)) (eta ((b : ℝ) + s)) = _root_.Dist.dist a b
    rw [hiso.dist_eq, dist_add_right]
    rfl
  have hv : g.inner (eta s) (curveVelocity (I := I) eta s)
      (curveVelocity (I := I) eta s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u s).trans hu
  have hend : intrinsicGeodesic (I := I) g hEnorm (eta s)
      (curveVelocity (I := I) eta s) (R - s) = eta R := by
    have h := congrFun hcont (R - s)
    simpa only [sub_add_cancel] using h.symm
  have h := gradient_intrinsic_ray_distance_support (I := I) g hEnorm (eta s)
    (curveVelocity (I := I) eta s) hv hshift s (R - s) (sub_pos.mpr hR)
  have heq : (fun x => s + (R - s) - _root_.Dist.dist x (intrinsicGeodesic (I := I) g hEnorm
      (eta s) (curveVelocity (I := I) eta s) (R - s))) = lineDistanceSupport eta R := by
    funext x
    rw [hend]
    dsimp only [lineDistanceSupport]
    ring
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.gradient_lineDistanceSupport_on_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.gradient_lineDistanceSupport_on_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.gradient_lineDistanceSupport_on_line ``Submission.DifferentialGeometry.Geometry.Topology.gradient_lineDistanceSupport_on_line

end DifferentialGeometry.Geometry.Topology

end
