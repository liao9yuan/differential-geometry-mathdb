import Submission.DifferentialGeometry.Analysis.InnerProductSpace.SphereDerivative
import Submission.DifferentialGeometry.Analysis.Calculus.BallBoundary
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import Submission.DifferentialGeometry.Topology.Manifold.RelativeCollarIsotopy
import Submission.DifferentialGeometry.Topology.Homeomorph.LevelIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.RealInnerProductSpace _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open _root_.Diffeomorph in
theorem injective_convex_combination_fderiv_of_eventuallyEq_sphere
    {F : E → E} {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ _root_.Metric.sphere c r)
    (hF : DifferentiableAt ℝ F x) (hfixed : F =ᶠ[𝓝[_root_.Metric.sphere c r] x] id)
    (hpos : 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x) := by
  have hn : ‖x - c‖ = r := by simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hx
  let l : E →ₗ[ℝ] ℝ := (r ^ 2)⁻¹ • (innerSL ℝ (x - c)).toLinearMap
  have hl (v : E) : l v = (r ^ 2)⁻¹ * ⟪x - c, v⟫ := rfl
  have hln : l (x - c) = 1 := by
    rw [hl, real_inner_self_eq_norm_sq, hn, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  apply (fderiv ℝ F x).toLinearMap.injective_convex_combination_of_eqOn_ker_id l hln
  · intro v hv
    have hv' : ⟪x - c, v⟫ = 0 := (mul_eq_zero.mp hv).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hr.ne'))
    change (fderiv ℝ F x) v = v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using
      fderiv_apply_eq_of_eventuallyEq_sphere hr hx hF differentiableAt_id hfixed hv'
  · exact mul_pos (inv_pos.mpr (sq_pos_of_pos hr)) hpos
  · exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.injective_convex_combination_fderiv_of_eventuallyEq_sphere then
    throwError "Refusing to shadow existing declaration Diffeomorph.injective_convex_combination_fderiv_of_eventuallyEq_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.injective_convex_combination_fderiv_of_eventuallyEq_sphere ``Submission.Diffeomorph.injective_convex_combination_fderiv_of_eventuallyEq_sphere

open _root_.Diffeomorph in
theorem injective_convex_combination_fderiv_of_eqOn_sphere
    {F : E → E} {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ _root_.Metric.sphere c r)
    (hF : DifferentiableAt ℝ F x) (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r))
    (hpos : 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    Function.Injective ((1 - t) • ContinuousLinearMap.id ℝ E + t • fderiv ℝ F x) := by
  apply injective_convex_combination_fderiv_of_eventuallyEq_sphere hr hx hF ?_ hpos ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hfixed hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.injective_convex_combination_fderiv_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration Diffeomorph.injective_convex_combination_fderiv_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.injective_convex_combination_fderiv_of_eqOn_sphere ``Submission.Diffeomorph.injective_convex_combination_fderiv_of_eqOn_sphere

open _root_.Diffeomorph in
theorem exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {c : E} {r : ℝ} (hr : 0 < r)
    (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r ∩ W))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ _root_.Metric.sphere c r ∩ W)
    (hpos : ∀ x ∈ K, 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, _root_.Set.EqOn (Φ t) id (_root_.Metric.sphere c r) ∧ _root_.Set.EqOn (Φ t).symm id (_root_.Metric.sphere c r)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ t '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ _root_.Set.EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hSV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_of_injective_convex_combination hW hF
      hfixed hK hKS
      (fun x hx t ht => injective_convex_combination_fderiv_of_eventuallyEq_sphere hr (hKS hx).1
        ((hF.contDiffAt (hW.mem_nhds (hKS hx).2)).differentiableAt (by simp))
        (by
          filter_upwards [self_mem_nhdsWithin,
            eventually_nhdsWithin_of_eventually_nhds (hW.mem_nhds (hKS hx).2)] with y hy hyW
          exact hfixed ⟨hy, hyW⟩)
        (hpos x hx) ht) hO hKO
  refine ⟨V, hV, hSV, hVW, Φ, hΦ, hΦi, hΦ0, htrack, hfix, ?_, hsupport⟩
  intro t ht
  change (Φ t).toHomeomorph '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r
  have hlevel (u : ℝ) (hu : u ∈ _root_.Set.Icc (0 : ℝ) 1) :
      (Φ u).toHomeomorph '' {x : E | _root_.Dist.dist x c = r} = {x : E | _root_.Dist.dist x c = r} := by
    change Φ u '' _root_.Metric.sphere c r = _root_.Metric.sphere c r
    rw [(hfix u).1.image_eq, _root_.Set.image_id]
  exact Homeomorph.image_sublevel_eq_of_image_level_eq (fun u => (Φ u).toHomeomorph)
    (continuous_id.dist continuous_const) (fun x => (hΦ.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
    (by rw [hΦ0]; rfl) hlevel t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere ``Submission.Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere

open _root_.Diffeomorph in
theorem exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere
    [FiniteDimensional ℝ E] {F : E → E} {W : Set E}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    {c : E} {r : ℝ} (hr : 0 < r) (hSW : _root_.Metric.sphere c r ⊆ W)
    (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r))
    (hpos : ∀ x ∈ _root_.Metric.sphere c r, 0 < ⟪x - c, fderiv ℝ F x (x - c)⟫)
    {O : Set E} (hO : IsOpen O) (hSO : _root_.Metric.sphere c r ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ _root_.Metric.sphere c r ⊆ V ∧ V ⊆ W ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ p ∈ V, Φ t p = (1 - t) • p + t • F p) ∧
        (∀ t, _root_.Set.EqOn (Φ t) id (_root_.Metric.sphere c r) ∧ _root_.Set.EqOn (Φ t).symm id (_root_.Metric.sphere c r)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ t '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ _root_.Set.EqOn (Φ t).symm id Lᶜ := by
  exact exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere hW hF hr
    (hfixed.mono _root_.Set.inter_subset_left) (isCompact_sphere c r) (fun x hx => ⟨hx, hSW hx⟩)
    hpos hO hSO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere ``Submission.Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere

end Diffeomorph

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open _root_.PartialDiffeomorph in
theorem inner_fderiv_pos_of_mapsTo_compl_ball
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ _root_.Metric.sphere c r)
    (hxF : x ∈ F.source) (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r))
    (hmap : _root_.Set.MapsTo F ((_root_.Metric.ball c r)ᶜ ∩ F.source) (_root_.Metric.ball c r)ᶜ) :
    0 < ⟪x - c, fderiv ℝ F x (x - c)⟫ := by
  have hn : ‖x - c‖ = r := by simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hx
  have hd := ((F.contMDiffOn.contDiffOn.contDiffAt
    (F.open_source.mem_nhds hxF)).differentiableAt (by simp)).hasFDerivAt
  have hmin : IsLocalMinOn (fun y => ‖F y - c‖ ^ 2) (_root_.Metric.ball c r)ᶜ x := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (F.open_source.mem_nhds hxF)] with y hy hyF
    have hnorm : r ≤ ‖F y - c‖ := by
      simpa only [_root_.Set.mem_compl_iff, _root_.Metric.mem_ball, dist_eq_norm, not_lt] using hmap ⟨hy, hyF⟩
    change ‖F x - c‖ ^ 2 ≤ ‖F y - c‖ ^ 2
    rw [hfixed hx, id_eq, hn]
    exact (sq_le_sq₀ hr.le (norm_nonneg _)).mpr hnorm
  have hcone : x - c ∈ posTangentConeAt (_root_.Metric.ball c r)ᶜ x := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (x - c) ∈ (_root_.Metric.ball c r)ᶜ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      rw [_root_.Set.mem_compl_iff, _root_.Metric.mem_ball, dist_eq_norm, not_lt]
      have heq : x + t • (x - c) - c = (1 + t) • (x - c) := by
        rw [add_smul, one_smul]
        abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn]
      nlinarith
    exact he.frequently
  have hnonneg : 0 ≤ ⟪x - c, fderiv ℝ F x (x - c)⟫ := by
    have h := hmin.hasFDerivWithinAt_nonneg (hd.sub_const c).norm_sq.hasFDerivWithinAt hcone
    simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, hfixed hx, id_eq] at h
    linarith
  apply lt_of_le_of_ne hnonneg
  intro heq
  have htangent : fderiv ℝ F x (fderiv ℝ F x (x - c)) = fderiv ℝ F x (x - c) := by
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using
      fderiv_apply_eq_of_eqOn_sphere hr hx hd.differentiableAt differentiableAt_id
        hfixed heq.symm
  have hA := DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph F hxF
  have hrad : fderiv ℝ F x (x - c) = x - c := hA.injective htangent
  have hzero := heq.symm
  rw [hrad, real_inner_self_eq_norm_sq, hn] at hzero
  exact (sq_pos_of_pos hr).ne' hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_compl_ball then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_compl_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_compl_ball ``Submission.PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_compl_ball

open _root_.PartialDiffeomorph in
theorem inner_fderiv_pos_of_mapsTo_closedBall
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c x : E} {r : ℝ} (hr : 0 < r) (hx : x ∈ _root_.Metric.sphere c r)
    (hxF : x ∈ F.source) (hfixed : F x = x)
    (hmap : _root_.Set.MapsTo F (_root_.Metric.closedBall c r ∩ F.source) (_root_.Metric.closedBall c r)) :
    0 < ⟪x - c, fderiv ℝ F x (x - c)⟫ := by
  have hn : ‖x - c‖ = r := by simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hx
  have hd := ((F.contMDiffOn.contDiffOn.contDiffAt
    (F.open_source.mem_nhds hxF)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨a, ha, heq⟩ := hd.exists_pos_inner_eq_mul_inner_of_eventually_mem_closedBall
    (DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph F hxF).surjective
    hr hr hn (by rw [hfixed]; exact hn) (by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (F.open_source.mem_nhds hxF)] with y hy hyF
      exact hmap ⟨hy, hyF⟩)
  have h := heq (x - c)
  rw [hfixed, real_inner_self_eq_norm_sq, hn] at h
  rw [h]
  exact mul_pos ha (sq_pos_of_pos hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_closedBall then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_closedBall ``Submission.PartialDiffeomorph.inner_fderiv_pos_of_mapsTo_closedBall

open _root_.PartialDiffeomorph in
theorem exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
    [FiniteDimensional ℝ E]
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c : E} {r : ℝ} (hr : 0 < r)
    (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r ∩ F.source))
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ _root_.Metric.sphere c r ∩ F.source)
    (hmap : _root_.Set.MapsTo F (_root_.Metric.closedBall c r ∩ F.source) (_root_.Metric.closedBall c r))
    {O : Set E} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ F.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        _root_.Set.EqOn (Φ 1) F V ∧
        (∀ t, _root_.Set.EqOn (Φ t) id (_root_.Metric.sphere c r) ∧ _root_.Set.EqOn (Φ t).symm id (_root_.Metric.sphere c r)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ t '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ _root_.Set.EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hball, hsupport⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere
      F.open_source F.contMDiffOn.contDiffOn hr hfixed hK hKS
      (fun x hx => F.inner_fderiv_pos_of_mapsTo_closedBall hr (hKS hx).1
        (hKS hx).2 (hfixed (hKS hx)) hmap) hO hKO
  refine ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, ?_, hfix, hball, hsupport⟩
  intro x hx
  simpa only [sub_self, zero_smul, one_smul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere ``Submission.PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere

open _root_.PartialDiffeomorph in
theorem exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood
    [FiniteDimensional ℝ E]
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c : E} {r : ℝ} (hr : 0 < r) (hSF : _root_.Metric.sphere c r ⊆ F.source)
    (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r))
    (hmap : _root_.Set.MapsTo F (_root_.Metric.closedBall c r ∩ F.source) (_root_.Metric.closedBall c r))
    {O : Set E} (hO : IsOpen O) (hSO : _root_.Metric.sphere c r ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ _root_.Metric.sphere c r ⊆ V ∧ V ⊆ F.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        _root_.Set.EqOn (Φ 1) F V ∧
        (∀ t, _root_.Set.EqOn (Φ t) id (_root_.Metric.sphere c r) ∧ _root_.Set.EqOn (Φ t).symm id (_root_.Metric.sphere c r)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ t '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ _root_.Set.EqOn (Φ t).symm id Lᶜ := by
  exact F.exists_contDiff_compact_isotopy_eqOn_neighborhood_of_eqOn_sphere hr
    (hfixed.mono _root_.Set.inter_subset_left) (isCompact_sphere c r) (fun x hx => ⟨hx, hSF hx⟩)
    hmap hO hSO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood ``Submission.PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood

open _root_.PartialDiffeomorph in
theorem exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball
    [FiniteDimensional ℝ E]
    (F : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {c : E} {r : ℝ} (hr : 0 < r) (hSF : _root_.Metric.sphere c r ⊆ F.source)
    (hfixed : _root_.Set.EqOn F id (_root_.Metric.sphere c r))
    (hmap : _root_.Set.MapsTo F ((_root_.Metric.ball c r)ᶜ ∩ F.source) (_root_.Metric.ball c r)ᶜ)
    {O : Set E} (hO : IsOpen O) (hSO : _root_.Metric.sphere c r ⊆ O) :
    ∃ V : Set E, IsOpen V ∧ _root_.Metric.sphere c r ⊆ V ∧ V ⊆ F.source ∧
      ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
        Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        _root_.Set.EqOn (Φ 1) F V ∧
        (∀ t, _root_.Set.EqOn (Φ t) id (_root_.Metric.sphere c r) ∧ _root_.Set.EqOn (Φ t).symm id (_root_.Metric.sphere c r)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ t '' _root_.Metric.closedBall c r = _root_.Metric.closedBall c r) ∧
        ∃ L : Set E, IsCompact L ∧ L ⊆ O ∧ ∀ t : ℝ,
          EqOn (Φ t) id Lᶜ ∧ _root_.Set.EqOn (Φ t).symm id Lᶜ := by
  obtain ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, htrack, hfix, hball, hsupport⟩ :=
    Diffeomorph.exists_contDiff_compact_isotopy_eqOn_of_eqOn_sphere
      F.open_source F.contMDiffOn.contDiffOn hr hSF hfixed
      (fun x hx => F.inner_fderiv_pos_of_mapsTo_compl_ball hr hx (hSF hx) hfixed hmap) hO hSO
  refine ⟨V, hV, hSV, hVF, Φ, hΦ, hΦi, hΦ0, ?_, hfix, hball, hsupport⟩
  intro x hx
  simpa only [sub_self, zero_smul, one_smul, zero_add] using htrack 1 ⟨zero_le_one, le_rfl⟩ x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball ``Submission.PartialDiffeomorph.exists_contDiff_compact_isotopy_eqOn_sphere_neighborhood_of_mapsTo_compl_ball

end PartialDiffeomorph
