import Submission.DifferentialGeometry.Analysis.Calculus.SmoothMax
import Submission.DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import Submission.DifferentialGeometry.Topology.Diffeomorph.Convex
import Submission.DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology.Handle

noncomputable def quadraticCapsuleFunction (n : ℕ) (ε r h : ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 +
    Real.smoothMax ε (-(r ^ 2))
      (Real.smoothMax ε (-2 * ((EuclideanSpace.equivProdLast n z).2 + h))
        (2 * ((EuclideanSpace.equivProdLast n z).2 - h)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction

theorem convexOn_quadraticCapsuleFunction (n : ℕ) {ε : ℝ} (hε : 0 < ε) (r h : ℝ) :
    ConvexOn ℝ _root_.Set.univ (quadraticCapsuleFunction n ε r h) := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  let L := (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp A.toLinearMap
  have hx : ConvexOn ℝ _root_.Set.univ (fun z => ‖(A z).1‖) := by
    convert! (convexOn_norm (E := EuclideanSpace ℝ (Fin n)) convex_univ).comp_linearMap
      ((LinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp A.toLinearMap) using 1
  apply (hx.pow (fun _ _ => norm_nonneg _) 2).add
  apply Real.smoothMax.comp_convexOn hε (convexOn_const _ convex_univ)
  apply Real.smoothMax.comp_convexOn hε
  · convert! (((-2 : ℝ) • L).convexOn convex_univ).add_const (-2 * h) using 1
    funext z
    dsimp [L, A]
    ring
  · convert! (((2 : ℝ) • L).convexOn convex_univ).add_const (-2 * h) using 1
    funext z
    dsimp [L, A]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.convexOn_quadraticCapsuleFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.convexOn_quadraticCapsuleFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.convexOn_quadraticCapsuleFunction ``Submission.DifferentialGeometry.Topology.Handle.convexOn_quadraticCapsuleFunction

theorem contDiff_quadraticCapsuleFunction (n : ℕ) (ε r h : ℝ) :
    ContDiff ℝ ∞ (quadraticCapsuleFunction n ε r h) := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  apply ((contDiff_norm_sq ℝ).comp (contDiff_fst.comp A.contDiff)).add
  exact (Real.smoothMax.contDiff ε).comp (contDiff_const.prodMk
    ((Real.smoothMax.contDiff ε).comp
      ((contDiff_const.mul ((contDiff_snd.comp A.contDiff).add contDiff_const)).prodMk
        (contDiff_const.mul ((contDiff_snd.comp A.contDiff).sub contDiff_const)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsuleFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsuleFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsuleFunction ``Submission.DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsuleFunction

theorem quadraticCapsuleFunction_nonpos_bounds (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : quadraticCapsuleFunction n ε r h z ≤ 0) :
    ‖(EuclideanSpace.equivProdLast n z).1‖ ≤ |r| ∧
      (EuclideanSpace.equivProdLast n z).2 ∈ _root_.Set.Icc (-h) h := by
  let t := (EuclideanSpace.equivProdLast n z).2
  let v := Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))
  have h₀ := (le_max_left (-(r ^ 2)) v).trans (Real.smoothMax.max_le hε _ _)
  have h₁ := (le_max_right (-(r ^ 2)) v).trans (Real.smoothMax.max_le hε _ _)
  have h₂ := (le_max_left (-2 * (t + h)) (2 * (t - h))).trans (Real.smoothMax.max_le hε _ _)
  have h₃ := (le_max_right (-2 * (t + h)) (2 * (t - h))).trans (Real.smoothMax.max_le hε _ _)
  change ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 + Real.smoothMax ε (-(r ^ 2)) v ≤ 0 at hz
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [norm_nonneg (EuclideanSpace.equivProdLast n z).1, sq_abs r, abs_nonneg r]
  · change -h ≤ t
    change -2 * (t + h) ≤ v at h₂
    nlinarith [sq_nonneg ‖(EuclideanSpace.equivProdLast n z).1‖]
  · change t ≤ h
    change 2 * (t - h) ≤ v at h₃
    nlinarith [sq_nonneg ‖(EuclideanSpace.equivProdLast n z).1‖]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_bounds ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_bounds

theorem isCompact_sublevel_quadraticCapsuleFunction (n : ℕ) {ε r h : ℝ} (hε : 0 < ε) :
    IsCompact {z | quadraticCapsuleFunction n ε r h z ≤ 0} := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  have hcompact := (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) |r|).prod
    (_root_.CompactIccSpace.isCompact_Icc (a := -h) (b := h))
  apply (hcompact.image A.symm.continuous).of_isClosed_subset
    (isClosed_le (contDiff_quadraticCapsuleFunction n ε r h).continuous continuous_const)
  intro z hz
  obtain ⟨hx, ht⟩ := quadraticCapsuleFunction_nonpos_bounds n hε hz
  exact ⟨A z, ⟨mem_closedBall_zero_iff.mpr hx, ht⟩, A.symm_apply_apply z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.isCompact_sublevel_quadraticCapsuleFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.isCompact_sublevel_quadraticCapsuleFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.isCompact_sublevel_quadraticCapsuleFunction ``Submission.DifferentialGeometry.Topology.Handle.isCompact_sublevel_quadraticCapsuleFunction

theorem quadraticCapsuleFunction_eq_lower (n : ℕ) {ε r h : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (ht : (EuclideanSpace.equivProdLast n z).2 ≤ -ε / 4)
    (hcap : 2 * ((EuclideanSpace.equivProdLast n z).2 + h) ≤ r ^ 2 - ε) :
    quadraticCapsuleFunction n ε r h z =
      ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 -
        2 * ((EuclideanSpace.equivProdLast n z).2 + h) := by
  let t := (EuclideanSpace.equivProdLast n z).2
  have hsep : ε ≤ |(-2 * (t + h)) - 2 * (t - h)| :=
    (show ε ≤ (-2 * (t + h)) - 2 * (t - h) by
      change t ≤ -ε / 4 at ht
      linarith).trans (le_abs_self _)
  have hmax : _root_.Max.max (-2 * (t + h)) (2 * (t - h)) = -2 * (t + h) :=
    max_eq_left (by change t ≤ -ε / 4 at ht; linarith)
  have hsep' : ε ≤ |-(r ^ 2) - (-2 * (t + h))| :=
    (show ε ≤ -(-(r ^ 2) - (-2 * (t + h))) by
      change 2 * (t + h) ≤ r ^ 2 - ε at hcap
      linarith).trans (neg_le_abs _)
  change ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 +
    Real.smoothMax ε (-(r ^ 2)) (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))) = _
  rw [Real.smoothMax.eq_max_of_le hε hsep, hmax,
    Real.smoothMax.eq_max_of_le hε hsep',
    max_eq_right (by
      change 2 * (t + h) ≤ r ^ 2 - ε at hcap
      linarith : -(r ^ 2) ≤ -2 * (t + h))]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_lower ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_lower

theorem quadraticCapsuleFunction_eq_upper (n : ℕ) {ε r h : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (ht : ε / 4 ≤ (EuclideanSpace.equivProdLast n z).2)
    (hcap : 2 * (h - (EuclideanSpace.equivProdLast n z).2) ≤ r ^ 2 - ε) :
    quadraticCapsuleFunction n ε r h z =
      ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 +
        2 * ((EuclideanSpace.equivProdLast n z).2 - h) := by
  let t := (EuclideanSpace.equivProdLast n z).2
  have hsep : ε ≤ |(-2 * (t + h)) - 2 * (t - h)| :=
    (show ε ≤ -((-2 * (t + h)) - 2 * (t - h)) by
      change ε / 4 ≤ t at ht
      linarith).trans (neg_le_abs _)
  have hmax : _root_.Max.max (-2 * (t + h)) (2 * (t - h)) = 2 * (t - h) :=
    max_eq_right (by change ε / 4 ≤ t at ht; linarith)
  have hsep' : ε ≤ |-(r ^ 2) - 2 * (t - h)| :=
    (show ε ≤ -(-(r ^ 2) - 2 * (t - h)) by
      change 2 * (h - t) ≤ r ^ 2 - ε at hcap
      linarith).trans (neg_le_abs _)
  change ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 +
    Real.smoothMax ε (-(r ^ 2)) (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))) = _
  rw [Real.smoothMax.eq_max_of_le hε hsep, hmax,
    Real.smoothMax.eq_max_of_le hε hsep',
    max_eq_right (by
      change 2 * (h - t) ≤ r ^ 2 - ε at hcap
      linarith : -(r ^ 2) ≤ 2 * (t - h))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_upper ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_upper

theorem quadraticCapsuleFunction_eq_cylinder (n : ℕ) {ε r h : ℝ} (hε : 0 < ε)
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (ht : |(EuclideanSpace.equivProdLast n z).2| ≤ h - r ^ 2 / 2 - ε) :
    quadraticCapsuleFunction n ε r h z =
      ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 - r ^ 2 := by
  let t := (EuclideanSpace.equivProdLast n z).2
  let v := Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))
  have htv : v ≤ -(r ^ 2) - ε := by
    apply (Real.smoothMax.le_max_add hε _ _).trans
    have hl : -2 * (t + h) ≤ -(r ^ 2) - 2 * ε := by
      have habs := neg_le_abs t
      change |t| ≤ h - r ^ 2 / 2 - ε at ht
      linarith
    have hu : 2 * (t - h) ≤ -(r ^ 2) - 2 * ε := by
      have habs := le_abs_self t
      change |t| ≤ h - r ^ 2 / 2 - ε at ht
      linarith
    linarith [max_le hl hu]
  have hsep : ε ≤ |-(r ^ 2) - v| := (show ε ≤ -(r ^ 2) - v by linarith).trans (le_abs_self _)
  change ‖(EuclideanSpace.equivProdLast n z).1‖ ^ 2 + Real.smoothMax ε (-(r ^ 2)) v = _
  rw [Real.smoothMax.eq_max_of_le hε hsep, max_eq_left (by linarith : v ≤ -(r ^ 2))]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_cylinder ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_cylinder

theorem exists_quadraticCapsuleFunction_eq_on_cap_collars (n : ℕ)
    {ε r h ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hr : ρ ^ 2 + ε < r ^ 2) (hh : ρ ^ 2 + ε / 2 < 2 * h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      ‖x‖ ≤ ρ + δ → |s| ≤ δ →
        quadraticCapsuleFunction n ε r h
          ((EuclideanSpace.equivProdLast n).symm (x, -h + ‖x‖ ^ 2 / 2 + s)) = -2 * s ∧
        quadraticCapsuleFunction n ε r h
          ((EuclideanSpace.equivProdLast n).symm (x, h - ‖x‖ ^ 2 / 2 + s)) = 2 * s := by
  let R := _root_.Min.min (r ^ 2 - ε) (2 * h - ε / 2)
  have hR : ρ ^ 2 < R := lt_min (by linarith) (by linarith)
  let δ := _root_.Min.min 1 ((R - ρ ^ 2) / (2 * (2 * ρ + 3)))
  have hden : 0 < 2 * (2 * ρ + 3) := by linarith
  have hδ : 0 < δ := lt_min one_pos (div_pos (sub_pos.mpr hR) hden)
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδbound : δ * (2 * (2 * ρ + 3)) ≤ R - ρ ^ 2 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : (ρ + δ) ^ 2 + 2 * δ < R := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδone)]
  have hsmallr : (ρ + δ) ^ 2 + 2 * δ < r ^ 2 - ε :=
    hsmall.trans_le (min_le_left _ _)
  have hsmallh : (ρ + δ) ^ 2 + 2 * δ < 2 * h - ε / 2 :=
    hsmall.trans_le (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro x s hx hs
  have hx2 : ‖x‖ ^ 2 ≤ (ρ + δ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x) (by linarith)).mpr hx
  obtain ⟨hsl, hsu⟩ := abs_le.mp hs
  constructor
  · rw [quadraticCapsuleFunction_eq_lower n hε]
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      ring
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      nlinarith
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      nlinarith
  · rw [quadraticCapsuleFunction_eq_upper n hε]
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      ring
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      nlinarith
    · simp only [ContinuousLinearEquiv.apply_symm_apply]
      nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_quadraticCapsuleFunction_eq_on_cap_collars then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_quadraticCapsuleFunction_eq_on_cap_collars"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_quadraticCapsuleFunction_eq_on_cap_collars ``Submission.DifferentialGeometry.Topology.Handle.exists_quadraticCapsuleFunction_eq_on_cap_collars

private theorem quadraticCapsuleFunction_zero_lt_zero (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) :
    quadraticCapsuleFunction n ε r h 0 < 0 := by
  have hinner := Real.smoothMax.le_max_add hε (-2 * h) (-2 * h)
  simp only [max_self] at hinner
  have houter := Real.smoothMax.le_max_add hε (-(r ^ 2))
    (Real.smoothMax ε (-2 * h) (-2 * h))
  have hnegative : _root_.Max.max (-(r ^ 2)) (Real.smoothMax ε (-2 * h) (-2 * h)) < -ε :=
    max_lt (by linarith) (by linarith)
  simp only [neg_mul] at houter hnegative
  simp only [quadraticCapsuleFunction, map_zero, Prod.fst_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Prod.snd_zero, zero_add, zero_sub, mul_neg, neg_mul]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_zero_lt_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_zero_lt_zero target :: scope.openDecls } }

theorem exists_diffeomorph_quadraticCapsule (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) :
    ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin (n + 1))),
      D 0 = 0 ∧
      D '' _root_.Metric.closedBall 0 1 = {z | quadraticCapsuleFunction n ε r h z ≤ 0} ∧
      D '' _root_.Metric.ball 0 1 = {z | quadraticCapsuleFunction n ε r h z < 0} ∧
      D '' _root_.Metric.sphere 0 1 = {z | quadraticCapsuleFunction n ε r h z = 0} := by
  have hneg := quadraticCapsuleFunction_zero_lt_zero n hε hr hh
  obtain ⟨D, hD0, _, hclosed, hopen, hsphere⟩ :=
    Diffeomorph.exists_diffeomorph_convex_sublevel (convexOn_quadraticCapsuleFunction n hε r h)
      (contDiff_quadraticCapsuleFunction n ε r h)
      (isCompact_sublevel_quadraticCapsuleFunction n hε).isBounded hneg
  exact ⟨D, hD0, hclosed, hopen, hsphere⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule ``Submission.DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule

noncomputable def quadraticCapsuleRadius (ε r h t : ℝ) : ℝ :=
  Real.sqrt (-Real.smoothMax ε (-(r ^ 2))
    (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius

private theorem quadraticCapsuleFunction_axis_lt_zero (n : ℕ) {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Ioo (-h) h) :
    quadraticCapsuleFunction n ε r h
      ((EuclideanSpace.equivProdLast n).symm (0, t)) < 0 := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  let L : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    A.symm.toLinearMap.comp (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  let f : ℝ → ℝ := quadraticCapsuleFunction n ε r h ∘ L
  have hf : ConvexOn ℝ _root_.Set.univ f :=
    (convexOn_quadraticCapsuleFunction n hε r h).comp_linearMap L
  have hzero : f 0 < 0 := by
    simpa only [f, Function.comp_apply, map_zero] using
      quadraticCapsuleFunction_zero_lt_zero n hε hr hh
  have hleft : f (-h) = 0 := by
    change quadraticCapsuleFunction n ε r h (A.symm (0, -h)) = 0
    rw [quadraticCapsuleFunction_eq_lower n hε]
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply, norm_zero,
        zero_pow (by decide : 2 ≠ 0), neg_add_cancel, _root_.MulZeroClass.mul_zero, sub_zero]
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply]
      linarith
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply]
      linarith
  have hright : f h = 0 := by
    change quadraticCapsuleFunction n ε r h (A.symm (0, h)) = 0
    rw [quadraticCapsuleFunction_eq_upper n hε]
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply, norm_zero,
        zero_pow (by decide : 2 ≠ 0), sub_self, _root_.MulZeroClass.mul_zero, add_zero]
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply]
      linarith
    · simp only [A, ContinuousLinearEquiv.apply_symm_apply]
      linarith
  have hchord (q s : ℝ) (hq : f q = 0) (hs : s ∈ _root_.Set.Ico (0 : ℝ) 1) : f (s * q) < 0 := by
    have hc := hf.2 (_root_.Set.mem_univ 0) (_root_.Set.mem_univ q) (sub_nonneg.mpr hs.2.le) hs.1
      (by ring : (1 - s) + s = 1)
    simp only [smul_eq_mul, _root_.MulZeroClass.mul_zero, zero_add, hq, add_zero] at hc
    exact hc.trans_lt (mul_neg_of_pos_of_neg (sub_pos.mpr hs.2) hzero)
  change f t < 0
  have hhpos : 0 < h := hε.trans hh
  rcases le_total 0 t with hpos | hneg
  · have hs : t / h ∈ _root_.Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg hpos hhpos.le, (div_lt_one hhpos).mpr ht.2⟩
    simpa only [div_mul_cancel₀ _ hhpos.ne'] using hchord h (t / h) hright hs
  · have hs : (-t) / h ∈ _root_.Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg (neg_nonneg.mpr hneg) hhpos.le, (div_lt_one hhpos).mpr (by linarith [ht.1])⟩
    have heq : (-t) / h * (-h) = t := by field_simp
    simpa only [heq] using hchord (-h) ((-t) / h) hleft hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_axis_lt_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_axis_lt_zero target :: scope.openDecls } }

private theorem contDiff_quadraticCapsule_vertical (ε r h : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => Real.smoothMax ε (-(r ^ 2))
      (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h)))) :=
  (Real.smoothMax.contDiff ε).comp (contDiff_const.prodMk
    ((Real.smoothMax.contDiff ε).comp
      ((contDiff_const.mul (contDiff_id.add contDiff_const)).prodMk
        (contDiff_const.mul (contDiff_id.sub contDiff_const)))))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsule_vertical
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.contDiff_quadraticCapsule_vertical target :: scope.openDecls } }

theorem quadraticCapsuleRadius_pos {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Ioo (-h) h) :
    0 < quadraticCapsuleRadius ε r h t := by
  apply Real.sqrt_pos.mpr
  have hn := quadraticCapsuleFunction_axis_lt_zero 0 hε hr hh ht
  simpa only [quadraticCapsuleFunction, ContinuousLinearEquiv.apply_symm_apply,
    norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, neg_pos] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_pos ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_pos

theorem quadraticCapsuleRadius_sq {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Icc (-h) h) :
    quadraticCapsuleRadius ε r h t ^ 2 = -Real.smoothMax ε (-(r ^ 2))
      (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h))) := by
  apply Real.sq_sqrt
  have hsub : _root_.Set.Ioo (-h) h ⊆ {t | 0 ≤ -Real.smoothMax ε (-(r ^ 2))
      (Real.smoothMax ε (-2 * (t + h)) (2 * (t - h)))} := by
    intro t ht
    exact ((Real.sqrt_pos.mp (quadraticCapsuleRadius_pos hε hr hh ht))).le
  apply closure_minimal hsub
    (isClosed_le continuous_const (contDiff_quadraticCapsule_vertical ε r h).continuous.neg)
  rw [closure_Ioo (by linarith : -h ≠ h)]
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq

theorem contDiffOn_quadraticCapsuleRadius {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) :
    ContDiffOn ℝ ∞ (quadraticCapsuleRadius ε r h) (_root_.Set.Ioo (-h) h) :=
  (contDiff_quadraticCapsule_vertical ε r h).neg.contDiffOn.sqrt
    (fun _ ht => (Real.sqrt_pos.mp (quadraticCapsuleRadius_pos hε hr hh ht)).ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.contDiffOn_quadraticCapsuleRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.contDiffOn_quadraticCapsuleRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.contDiffOn_quadraticCapsuleRadius ``Submission.DifferentialGeometry.Topology.Handle.contDiffOn_quadraticCapsuleRadius

theorem quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq (n : ℕ) {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Icc (-h) h)
    (x : EuclideanSpace ℝ (Fin n)) :
    quadraticCapsuleFunction n ε r h ((EuclideanSpace.equivProdLast n).symm (x, t)) =
      ‖x‖ ^ 2 - quadraticCapsuleRadius ε r h t ^ 2 := by
  rw [quadraticCapsuleRadius_sq hε hr hh ht]
  simp only [quadraticCapsuleFunction, ContinuousLinearEquiv.apply_symm_apply, sub_neg_eq_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq

theorem quadraticCapsuleFunction_nonpos_iff (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h)
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    quadraticCapsuleFunction n ε r h z ≤ 0 ↔
      (EuclideanSpace.equivProdLast n z).2 ∈ _root_.Set.Icc (-h) h ∧
        ‖(EuclideanSpace.equivProdLast n z).1‖ ≤
          quadraticCapsuleRadius ε r h (EuclideanSpace.equivProdLast n z).2 := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  have heq (ht : (A z).2 ∈ _root_.Set.Icc (-h) h) :
      quadraticCapsuleFunction n ε r h z = ‖(A z).1‖ ^ 2 -
        quadraticCapsuleRadius ε r h (A z).2 ^ 2 := by
    simpa only [A, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
      quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq n hε hr hh ht (A z).1
  constructor
  · intro hz
    have ht := (quadraticCapsuleFunction_nonpos_bounds n hε hz).2
    refine ⟨ht, ?_⟩
    rw [heq ht, sub_nonpos] at hz
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hz
  · rintro ⟨ht, hx⟩
    rw [heq ht, sub_nonpos]
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_iff ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_nonpos_iff

theorem quadraticCapsuleRadius_sq_eq_lower {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Icc (-h) h)
    (htcap : t ≤ -ε / 4) (hcap : 2 * (t + h) ≤ r ^ 2 - ε) :
    quadraticCapsuleRadius ε r h t ^ 2 = 2 * (t + h) := by
  have heq := quadraticCapsuleFunction_eq_lower 0 hε
    (z := (EuclideanSpace.equivProdLast 0).symm (0, t))
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using htcap)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hcap)
  rw [quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq 0 hε hr hh ht] at heq
  simp only [ContinuousLinearEquiv.apply_symm_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_sub] at heq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_lower ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_lower

theorem quadraticCapsuleRadius_sq_eq_upper {ε r h t : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (ht : t ∈ _root_.Set.Icc (-h) h)
    (htcap : ε / 4 ≤ t) (hcap : 2 * (h - t) ≤ r ^ 2 - ε) :
    quadraticCapsuleRadius ε r h t ^ 2 = 2 * (h - t) := by
  have heq := quadraticCapsuleFunction_eq_upper 0 hε
    (z := (EuclideanSpace.equivProdLast 0).symm (0, t))
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using htcap)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hcap)
  rw [quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq 0 hε hr hh ht] at heq
  simp only [ContinuousLinearEquiv.apply_symm_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_sub, zero_add] at heq
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_upper ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleRadius_sq_eq_upper

theorem quadraticCapsuleFunction_eq_zero_iff (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h)
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    quadraticCapsuleFunction n ε r h z = 0 ↔
      (EuclideanSpace.equivProdLast n z).2 ∈ _root_.Set.Icc (-h) h ∧
        ‖(EuclideanSpace.equivProdLast n z).1‖ =
          quadraticCapsuleRadius ε r h (EuclideanSpace.equivProdLast n z).2 := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  have heq (ht : (A z).2 ∈ _root_.Set.Icc (-h) h) :
      quadraticCapsuleFunction n ε r h z = ‖(A z).1‖ ^ 2 -
        quadraticCapsuleRadius ε r h (A z).2 ^ 2 := by
    simpa only [A, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
      quadraticCapsuleFunction_eq_norm_sq_sub_radius_sq n hε hr hh ht (A z).1
  constructor
  · intro hz
    have ht := (quadraticCapsuleFunction_nonpos_bounds n hε hz.le).2
    refine ⟨ht, ?_⟩
    rw [heq ht, sub_eq_zero] at hz
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hz
  · rintro ⟨ht, hx⟩
    rw [heq ht, hx, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_zero_iff ``Submission.DifferentialGeometry.Topology.Handle.quadraticCapsuleFunction_eq_zero_iff

theorem exists_quadraticCapsule_cap_intervals {c₀ c₁ r η : ℝ}
    (hr : 0 < r) (hab : c₀ + r ^ 2 / 2 < c₁ - r ^ 2 / 2) (hη : 0 < η) :
    ∃ ε τ : ℝ, 0 < ε ∧ ε < (2 * r) ^ 2 ∧ ε < (c₁ - c₀) / 2 ∧
      0 < τ ∧ τ ≤ η ∧ τ ≤ r ^ 2 / 8 ∧
      2 * τ < (c₁ - r ^ 2 / 2) - (c₀ + r ^ 2 / 2) ∧
      (∀ t ∈ _root_.Set.Icc c₀ (c₀ + r ^ 2 / 2 + τ),
        quadraticCapsuleRadius ε (2 * r) ((c₁ - c₀) / 2) (t - (c₀ + c₁) / 2) ^ 2 =
          2 * (t - c₀)) ∧
      (∀ t ∈ _root_.Set.Icc (c₁ - r ^ 2 / 2 - τ) c₁,
        quadraticCapsuleRadius ε (2 * r) ((c₁ - c₀) / 2) (t - (c₀ + c₁) / 2) ^ 2 =
          2 * (c₁ - t)) := by
  let g := (c₁ - r ^ 2 / 2) - (c₀ + r ^ 2 / 2)
  have hg : 0 < g := sub_pos.mpr hab
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  let τ := _root_.Min.min η (_root_.Min.min (g / 8) (r ^ 2 / 8))
  let ε := _root_.Min.min (g / 2) (r ^ 2 / 2)
  have hτ : 0 < τ := lt_min hη (lt_min (by positivity) (by positivity))
  have hτη : τ ≤ η := min_le_left _ _
  have hτg : τ ≤ g / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hτr : τ ≤ r ^ 2 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεg : ε ≤ g / 2 := min_le_left _ _
  have hεr : ε ≤ r ^ 2 / 2 := min_le_right _ _
  have hεR : ε < (2 * r) ^ 2 := by nlinarith
  have hεh : ε < (c₁ - c₀) / 2 := by dsimp [g] at hg; linarith
  refine ⟨ε, τ, hε, hεR, hεh, hτ, hτη, hτr, by change 2 * τ < g; linarith, ?_, ?_⟩
  · intro t ht
    have heq := quadraticCapsuleRadius_sq_eq_lower hε hεR hεh
      (t := t - (c₀ + c₁) / 2)
      (show t - (c₀ + c₁) / 2 ∈ _root_.Set.Icc (-((c₁ - c₀) / 2)) ((c₁ - c₀) / 2) by
        constructor <;> dsimp [g] at hτg <;> linarith [ht.1, ht.2])
      (by dsimp [g] at hεg hτg; linarith [ht.2])
      (by nlinarith [ht.2])
    convert heq using 1
    ring
  · intro t ht
    have heq := quadraticCapsuleRadius_sq_eq_upper hε hεR hεh
      (t := t - (c₀ + c₁) / 2)
      (show t - (c₀ + c₁) / 2 ∈ _root_.Set.Icc (-((c₁ - c₀) / 2)) ((c₁ - c₀) / 2) by
        constructor <;> dsimp [g] at hτg <;> linarith [ht.1, ht.2])
      (by dsimp [g] at hεg hτg; linarith [ht.1])
      (by nlinarith [ht.1])
    convert heq using 1
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_quadraticCapsule_cap_intervals then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_quadraticCapsule_cap_intervals"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_quadraticCapsule_cap_intervals ``Submission.DifferentialGeometry.Topology.Handle.exists_quadraticCapsule_cap_intervals


theorem exists_diffeomorph_quadraticCapsule_eq_radius (n : ℕ) {ε r h : ℝ}
    (hε : 0 < ε) (hr : ε < r ^ 2) (hh : ε < h) (m : ℝ) :
    ∃ D : (EuclideanSpace ℝ (Fin (n + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
      D '' _root_.Metric.closedBall 0 1 = {p | p.2 ∈ _root_.Set.Icc (m - h) (m + h) ∧
        ‖p.1‖ ≤ quadraticCapsuleRadius ε r h (p.2 - m)} ∧
      D '' _root_.Metric.sphere 0 1 = {p | p.2 ∈ _root_.Set.Icc (m - h) (m + h) ∧
        ‖p.1‖ = quadraticCapsuleRadius ε r h (p.2 - m)} := by
  let A := EuclideanSpace.equivProdLast (𝕜 := ℝ) n
  let T := translateDiffeomorph ((0 : EuclideanSpace ℝ (Fin n)), m)
  obtain ⟨D, _, hclosed, _, hsphere⟩ := exists_diffeomorph_quadraticCapsule n hε hr hh
  have hT (z : EuclideanSpace ℝ (Fin n) × ℝ) : T z = (z.1, z.2 + m) := by
    change z + (0, m) = _
    exact Prod.ext (add_zero _) rfl
  have hTi (z : EuclideanSpace ℝ (Fin n) × ℝ) : T.symm z = (z.1, z.2 - m) := by
    apply T.injective
    change T (T.symm z) = T (z.1, z.2 - m)
    rw [T.apply_symm_apply, hT]
    simp only [sub_add_cancel, Prod.eta]
  refine ⟨(D.trans A.toDiffeomorph).trans T, ?_, ?_⟩
  · change (T ∘ A ∘ D) '' _root_.Metric.closedBall 0 1 = _
    rw [_root_.Set.image_comp, _root_.Set.image_comp, hclosed]
    ext p
    rw [← _root_.Set.image_comp]
    change p ∈ (A.toDiffeomorph.trans T).toEquiv '' _ ↔ _
    rw [_root_.Set.mem_image_equiv]
    change quadraticCapsuleFunction n ε r h (A.symm (T.symm p)) ≤ 0 ↔ _
    rw [quadraticCapsuleFunction_nonpos_iff n hε hr hh, ContinuousLinearEquiv.apply_symm_apply, hTi]
    simp only [_root_.Set.mem_ofPred_eq]
    constructor <;> rintro ⟨ht, hx⟩ <;> refine ⟨?_, hx⟩ <;> constructor <;> linarith [ht.1, ht.2]
  · change (T ∘ A ∘ D) '' _root_.Metric.sphere 0 1 = _
    rw [_root_.Set.image_comp, _root_.Set.image_comp, hsphere]
    ext p
    rw [← _root_.Set.image_comp]
    change p ∈ (A.toDiffeomorph.trans T).toEquiv '' _ ↔ _
    rw [_root_.Set.mem_image_equiv]
    change quadraticCapsuleFunction n ε r h (A.symm (T.symm p)) = 0 ↔ _
    rw [quadraticCapsuleFunction_eq_zero_iff n hε hr hh,
      ContinuousLinearEquiv.apply_symm_apply, hTi]
    simp only [_root_.Set.mem_ofPred_eq]
    constructor <;> rintro ⟨ht, hx⟩ <;> refine ⟨?_, hx⟩ <;> constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule_eq_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule_eq_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule_eq_radius ``Submission.DifferentialGeometry.Topology.Handle.exists_diffeomorph_quadraticCapsule_eq_radius

end DifferentialGeometry.Topology.Handle
