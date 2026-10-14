import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrRightFirstVariation
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

private theorem antitoneOn_max_of_upper_right_slope_nonpos_on_pos
    {f : ℝ → ℝ} {a b eps : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (heps : 0 < eps)
    (hbound : ∀ t ∈ _root_.Set.Ico a b, 0 < f t → ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    AntitoneOn (fun t => _root_.Max.max (f t) eps) (_root_.Set.Icc a b) := by
  apply antitoneOn_of_upper_right_slope_nonpos
    (fun t ht => (hf t ht).max tendsto_const_nhds)
  intro t ht r hr
  by_cases hlarge : eps ≤ f t
  · have hpositive : 0 < f t := heps.trans_le hlarge
    filter_upwards [hbound t ht hpositive r hr, self_mem_nhdsWithin] with s hs hst
    have hts : 0 < s - t := sub_pos.mpr hst
    rw [slope_def_field] at hs
    have hnum : f s - f t < r * (s - t) := (div_lt_iff₀ hts).mp hs
    have hprod : 0 < r * (s - t) := mul_pos hr hts
    have hmax : _root_.Max.max (f s) eps < r * (s - t) + f t :=
      max_lt_iff.mpr ⟨by linarith, by linarith⟩
    rw [slope_def_field, max_eq_left hlarge]
    apply (div_lt_iff₀ hts).mpr
    linarith
  · have hsmall : f t < eps := lt_of_not_ge hlarge
    have hnear : ∀ᶠ s in 𝓝[_root_.Set.Icc a b] t, f s < eps :=
      (hf t (_root_.Set.Ico_subset_Icc_self ht)).eventually (Iio_mem_nhds hsmall)
    have hright : ∀ᶠ s in 𝓝[>] t, f s < eps :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht) hnear
    filter_upwards [hright] with s hs
    rw [slope_def_field]
    simpa only [max_eq_right hs.le, max_eq_right hsmall.le, sub_self, zero_div] using hr

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.antitoneOn_max_of_upper_right_slope_nonpos_on_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.antitoneOn_max_of_upper_right_slope_nonpos_on_pos target :: scope.openDecls } }

theorem antitoneOn_of_upper_right_slope_nonpos_on_pos
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b))
    (hnonneg : ∀ t ∈ _root_.Set.Icc a b, 0 ≤ f t)
    (hbound : ∀ t ∈ _root_.Set.Ico a b, 0 < f t → ∀ r : ℝ, 0 < r →
      ∀ᶠ s in 𝓝[>] t, slope f t s < r) :
    AntitoneOn f (_root_.Set.Icc a b) := by
  intro x hx y hy hxy
  by_contra hnot
  have hlt : f x < f y := lt_of_not_ge hnot
  have hypos : 0 < f y := (hnonneg x hx).trans_lt hlt
  have hanti := antitoneOn_max_of_upper_right_slope_nonpos_on_pos
    hf (half_pos hypos) hbound
  have hh : _root_.Max.max (f y) (f y / 2) ≤ _root_.Max.max (f x) (f y / 2) := hanti hx hy hxy
  have hmax : _root_.Max.max (f x) (f y / 2) < f y :=
    max_lt_iff.mpr ⟨hlt, half_lt_self hypos⟩
  exact (not_lt_of_ge ((le_max_left (f y) (f y / 2)).trans hh)) hmax

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.antitoneOn_of_upper_right_slope_nonpos_on_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.antitoneOn_of_upper_right_slope_nonpos_on_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.antitoneOn_of_upper_right_slope_nonpos_on_pos ``Submission.DifferentialGeometry.Geometry.Topology.antitoneOn_of_upper_right_slope_nonpos_on_pos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsRiemannianManifold I M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem tangent_cast_model_eq {p q : M} (h : p = q)
    (v : TangentSpace I p) : (h ▸ v : TangentSpace I q) = (v : E) := by
  cases h
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.tangent_cast_model_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.tangent_cast_model_eq target :: scope.openDecls } }

theorem antitoneOn_dist_of_right_first_variation_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (_root_.Set.Icc a b)) (hzeta : ContinuousOn zeta (_root_.Set.Icc a b))
    (X : (t : ℝ) → ℝ →L[ℝ] TangentSpace I (xi t))
    (Y : (t : ℝ) → ℝ →L[ℝ] TangentSpace I (zeta t))
    (hX : ∀ t ∈ _root_.Set.Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (_root_.Set.Ici t) t (X t))
    (hY : ∀ t ∈ _root_.Set.Ico a b, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (_root_.Set.Ici t) t (Y t))
    (hangle : ∀ t ∈ _root_.Set.Ico a b, xi t ≠ zeta t →
      ∀ u : TangentSpace I (xi t), g.inner (xi t) u u = 1 →
      ∀ hend : intrinsicGeodesic g hEnorm (xi t) u (_root_.Dist.dist (xi t) (zeta t)) = zeta t,
        -g.inner (xi t) (X t 1) u + g.inner (zeta t) (Y t 1)
          (hend ▸ curveVelocity (I := I) (intrinsicGeodesic g hEnorm (xi t) u)
            (_root_.Dist.dist (xi t) (zeta t))) ≤ 0) :
    AntitoneOn (fun t => _root_.Dist.dist (xi t) (zeta t)) (_root_.Set.Icc a b) := by
  apply antitoneOn_of_upper_right_slope_nonpos_on_pos
    (fun t ht => (hxi t ht).dist (hzeta t ht))
    (fun _ _ => dist_nonneg)
  intro t ht hpos r hr
  have hne : xi t ≠ zeta t := dist_pos.mp hpos
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm (xi t) (zeta t) hpos
  have hmin : _root_.Dist.dist (xi t)
      (intrinsicGeodesic g hEnorm (xi t) u (_root_.Dist.dist (xi t) (zeta t))) =
        dist (xi t) (zeta t) := by rw [hend]
  have hcoeff := hangle t ht hne u hu hend
  rw [tangent_cast_model_eq] at hcoeff
  have hcoeff' :
      -g.inner (xi t) (X t 1) u +
        g.inner (intrinsicGeodesic g hEnorm (xi t) u (_root_.Dist.dist (xi t) (zeta t))) (Y t 1)
          (curveVelocity (I := I) (intrinsicGeodesic g hEnorm (xi t) u)
            (_root_.Dist.dist (xi t) (zeta t))) ≤ 0 := by
    rw [hend]
    exact hcoeff
  exact upper_right_first_variation_of_minimizing_geodesic g hEnorm (xi t) u
    (_root_.Dist.dist (xi t) (zeta t)) hpos hu hmin xi zeta t rfl hend.symm
    (X t) (Y t) (hX t ht) (hY t ht) r (hcoeff'.trans_lt hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_of_right_first_variation_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.antitoneOn_dist_of_right_first_variation_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_of_right_first_variation_nonpos ``Submission.DifferentialGeometry.Geometry.Topology.antitoneOn_dist_of_right_first_variation_nonpos

end DifferentialGeometry.Geometry.Topology
