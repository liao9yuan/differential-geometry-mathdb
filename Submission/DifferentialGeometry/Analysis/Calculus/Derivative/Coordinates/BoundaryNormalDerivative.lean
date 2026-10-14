import Submission.DifferentialGeometry.Tensor.LinearAlgebra.BoundaryBlockDeterminant
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normal_coefficient_nonneg_at_lower
    {a b : ℝ} (hab : a < b) (F : ℝ × E → ℝ × E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (z : E)
    (hF : HasFDerivWithinAt F L (_root_.Set.Icc a b ×ˢ _root_.Set.univ) (a, z))
    (hbound : ∀ q ∈ _root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E), (F q).1 ∈ _root_.Set.Icc a b)
    (hface : (F (a, z)).1 = a) : 0 ≤ (L (1, 0)).1 := by
  have hmin : IsLocalMinOn (fun q ↦ (F q).1) (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E)) (a, z) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (F (a, z)).1 ≤ (F q).1
    rw [hface]
    exact (hbound q hq).1
  have ht : (1, (0 : E)) ∈ posTangentConeAt (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E)) (a, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, z) + t • (1, (0 : E)) ∈ _root_.Set.Icc a b ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (sub_pos.mpr hab))] with t hpos hsmall
      change 0 < t at hpos
      change t < b - a at hsmall
      refine ⟨?_, _root_.Set.mem_univ _⟩
      change a ≤ a + t * 1 ∧ a + t * 1 ≤ b
      constructor <;> linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (a, z)) from hasFDerivAt_fst).comp_hasFDerivWithinAt (a, z) hF
  exact hmin.hasFDerivWithinAt_nonneg hd ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_lower ``Submission.DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_lower

theorem normal_coefficient_nonneg_at_upper
    {a b : ℝ} (hab : a < b) (F : ℝ × E → ℝ × E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (z : E)
    (hF : HasFDerivWithinAt F L (_root_.Set.Icc a b ×ˢ _root_.Set.univ) (b, z))
    (hbound : ∀ q ∈ _root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E), (F q).1 ∈ _root_.Set.Icc a b)
    (hface : (F (b, z)).1 = b) : 0 ≤ (L (1, 0)).1 := by
  have hmax : IsLocalMaxOn (fun q ↦ (F q).1) (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E)) (b, z) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (F q).1 ≤ (F (b, z)).1
    rw [hface]
    exact (hbound q hq).2
  have ht : (-1, (0 : E)) ∈ posTangentConeAt (_root_.Set.Icc a b ×ˢ (_root_.Set.univ : Set E)) (b, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (b, z) + t • (-1, (0 : E)) ∈ _root_.Set.Icc a b ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (sub_pos.mpr hab))] with t hpos hsmall
      change 0 < t at hpos
      change t < b - a at hsmall
      refine ⟨?_, _root_.Set.mem_univ _⟩
      change a ≤ b + t * (-1) ∧ b + t * (-1) ≤ b
      constructor <;> linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (b, z)) from hasFDerivAt_fst).comp_hasFDerivWithinAt (b, z) hF
  have h := hmax.hasFDerivWithinAt_nonpos hd ht
  change (L (-1, 0)).1 ≤ 0 at h
  have heq : ((-1 : ℝ), (0 : E)) = -(1, (0 : E)) := by simp
  rw [heq, map_neg] at h
  exact neg_nonpos.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_upper ``Submission.DifferentialGeometry.Analysis.normal_coefficient_nonneg_at_upper

theorem horizontal_derivative_of_face_eq
    {a b r : ℝ} (hr : r ∈ _root_.Set.Icc a b) (F : ℝ × E → ℝ × E) (f : E → E)
    (L : (ℝ × E) →L[ℝ] (ℝ × E)) (A : E →L[ℝ] E) (z : E)
    (hF : HasFDerivWithinAt F L (_root_.Set.Icc a b ×ˢ _root_.Set.univ) (r, z))
    (hf : HasFDerivAt f A z) (hface : ∀ w, F (r, w) = (r, f w)) :
    ∀ w, L (0, w) = (0, A w) := by
  have hin : HasFDerivAt (fun w : E ↦ (r, w)) (ContinuousLinearMap.inr ℝ ℝ E) z :=
    (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z)
  have hcomp := (hF.comp z hin.hasFDerivWithinAt
    (show _root_.Set.MapsTo (fun w : E ↦ (r, w)) _root_.Set.univ (_root_.Set.Icc a b ×ˢ _root_.Set.univ) from fun _ _ ↦ ⟨hr, _root_.Set.mem_univ _⟩)).hasFDerivAt_of_univ
  have heq : F ∘ (fun w : E ↦ (r, w)) = (fun w ↦ (r, f w)) := funext hface
  rw [heq] at hcomp
  have hder := hcomp.unique ((hasFDerivAt_const r z).prodMk hf)
  intro w
  exact congrArg (fun B : E →L[ℝ] (ℝ × E) ↦ B w) hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.horizontal_derivative_of_face_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.horizontal_derivative_of_face_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.horizontal_derivative_of_face_eq ``Submission.DifferentialGeometry.Analysis.horizontal_derivative_of_face_eq

theorem normal_coefficient_nonneg_of_eventually_le
    {F : ℝ × E → ℝ × E} {L : (ℝ × E) →L[ℝ] (ℝ × E)} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hface : (F (a, z)).1 = a)
    (hbound : ∀ᶠ q in 𝓝 (a, z), q.1 ≤ a → (F q).1 ≤ a) :
    0 ≤ (L (1, 0)).1 := by
  have hmax : IsLocalMaxOn (fun q => (F q).1) (_root_.Set.Iic a ×ˢ (_root_.Set.univ : Set E)) (a, z) := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hbound]
      with q hq hqbound
    change (F q).1 ≤ (F (a, z)).1
    rw [hface]
    exact hqbound hq.1
  have ht : (-1, (0 : E)) ∈ posTangentConeAt (_root_.Set.Iic a ×ˢ (_root_.Set.univ : Set E)) (a, z) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, z) + t • (-1, (0 : E)) ∈ _root_.Set.Iic a ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine ⟨?_, _root_.Set.mem_univ _⟩
      change a + t * (-1) ≤ a
      change 0 < t at ht
      linarith
    exact he.frequently
  have hd := (show HasFDerivAt (Prod.fst : ℝ × E → ℝ)
    (ContinuousLinearMap.fst ℝ ℝ E) (F (a, z)) from hasFDerivAt_fst).comp (a, z) hF
  have h := hmax.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt ht
  change (L (-1, 0)).1 ≤ 0 at h
  have heq : ((-1 : ℝ), (0 : E)) = -(1, (0 : E)) := by simp
  rw [heq, map_neg] at h
  exact neg_nonpos.mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normal_coefficient_nonneg_of_eventually_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normal_coefficient_nonneg_of_eventually_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normal_coefficient_nonneg_of_eventually_le ``Submission.DifferentialGeometry.Analysis.normal_coefficient_nonneg_of_eventually_le

theorem horizontal_derivative_of_eventuallyEq_face
    {F : ℝ × E → ℝ × E} {f : E → E}
    {L : (ℝ × E) →L[ℝ] (ℝ × E)} {A : E →L[ℝ] E} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hf : HasFDerivAt f A z)
    (hface : (fun w => F (a, w)) =ᶠ[𝓝 z] fun w => (a, f w)) :
    ∀ w, L (0, w) = (0, A w) := by
  have hin : HasFDerivAt (fun w : E => (a, w)) (ContinuousLinearMap.inr ℝ ℝ E) z :=
    (hasFDerivAt_const a z).prodMk (hasFDerivAt_id z)
  have hder := ((hF.comp z hin).congr_of_eventuallyEq hface.symm).unique
    ((hasFDerivAt_const a z).prodMk hf)
  intro w
  exact congrArg (fun B : E →L[ℝ] (ℝ × E) => B w) hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.horizontal_derivative_of_eventuallyEq_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.horizontal_derivative_of_eventuallyEq_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.horizontal_derivative_of_eventuallyEq_face ``Submission.DifferentialGeometry.Analysis.horizontal_derivative_of_eventuallyEq_face

theorem det_pos_iff_horizontal_of_eventually_le [FiniteDimensional ℝ E]
    {F : ℝ × E → ℝ × E} {f : E → E}
    {L : (ℝ × E) →L[ℝ] (ℝ × E)} {A : E →L[ℝ] E} {a : ℝ} {z : E}
    (hF : HasFDerivAt F L (a, z)) (hf : HasFDerivAt f A z)
    (hface : (fun w => F (a, w)) =ᶠ[𝓝 z] fun w => (a, f w))
    (hL : Function.Surjective L)
    (hbound : ∀ᶠ q in 𝓝 (a, z), q.1 ≤ a → (F q).1 ≤ a) :
    0 < L.det ↔ 0 < A.det := by
  exact det_pos_iff_horizontal_of_surjective L.toLinearMap A.toLinearMap
    (horizontal_derivative_of_eventuallyEq_face hF hf hface) hL
    (normal_coefficient_nonneg_of_eventually_le hF (congrArg Prod.fst hface.eq_of_nhds) hbound)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_pos_iff_horizontal_of_eventually_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_pos_iff_horizontal_of_eventually_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_pos_iff_horizontal_of_eventually_le ``Submission.DifferentialGeometry.Analysis.det_pos_iff_horizontal_of_eventually_le

theorem normal_derivative_pos_of_eventually_nonneg
    {f : ℝ × E → ℝ} {L : (ℝ × E) →L[ℝ] ℝ} {a : ℝ} {x : E}
    (hf : HasFDerivAt f L (a, x)) (hL : L ≠ 0)
    (hface : (fun y => f (a, y)) =ᶠ[𝓝 x] fun _ => 0)
    (hside : ∀ᶠ p in 𝓝 (a, x), a ≤ p.1 → 0 ≤ f p) :
    0 < L (1, 0) := by
  have hmin : IsLocalMinOn f (_root_.Set.Ici a ×ˢ (_root_.Set.univ : Set E)) (a, x) := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hside]
      with p hp hs
    rw [hface.eq_of_nhds]
    exact hs hp.1
  have ht : (1, (0 : E)) ∈ posTangentConeAt (_root_.Set.Ici a ×ˢ (_root_.Set.univ : Set E)) (a, x) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (a, x) + t • (1, (0 : E)) ∈ _root_.Set.Ici a ×ˢ univ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨by change a ≤ a + t * 1; change 0 < t at ht; linarith, _root_.Set.mem_univ _⟩
    exact he.frequently
  have hnonneg : 0 ≤ L (1, 0) := hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt ht
  have hin : HasFDerivAt (fun y : E => (a, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have hder := ((hf.comp x hin).congr_of_eventuallyEq hface.symm).unique
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x)
  have hzero (v : E) : L (0, v) = 0 :=
    congrArg (fun A : E →L[ℝ] ℝ => A v) hder
  apply lt_of_le_of_ne hnonneg
  intro h
  apply hL
  apply ContinuousLinearMap.ext
  intro p
  rw [show p = p.1 • (1, (0 : E)) + (0, p.2) from by ext <;> simp, map_add,
    map_smul, hzero, ← h]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normal_derivative_pos_of_eventually_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normal_derivative_pos_of_eventually_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normal_derivative_pos_of_eventually_nonneg ``Submission.DifferentialGeometry.Analysis.normal_derivative_pos_of_eventually_nonneg

open _root_.Metric in
theorem fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F}
    {a : ℝ} {x : E} {r : ℝ} {d : F}
    (hg : HasFDerivAt g L (a, x)) (hL : Function.Surjective L) (hr : 0 < r)
    (hface : ∀ᶠ y in 𝓝 x, g (a, y) ∈ _root_.Metric.sphere d r)
    (hside : ∀ᶠ p in 𝓝 (a, x), a ≤ p.1 → g p ∈ _root_.Metric.closedBall d r) :
    fderiv ℝ (fun p => ‖g p - d‖ ^ 2) (a, x) (1, 0) < 0 := by
  have hnorm : ‖g (a, x) - d‖ = r := by
    simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hface.self_of_nhds
  have hne : 2 • (innerSL ℝ (g (a, x) - d)).comp L ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := hL (g (a, x) - d)
    have hh := congrArg (fun A : (ℝ × E) →L[ℝ] ℝ => A v) hzero
    simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, zero_apply, hv, real_inner_self_eq_norm_sq, hnorm] at hh
    nlinarith
  have hd := (hg.sub_const d).norm_sq
  have hpos : 0 < (-(2 • (innerSL ℝ (g (a, x) - d)).comp L)) (1, 0) := by
    apply normal_derivative_pos_of_eventually_nonneg (hd.const_sub (r ^ 2))
      (neg_ne_zero.mpr hne)
    · filter_upwards [hface] with y hy
      have hy' : ‖g (a, y) - d‖ = r := by
        simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hy
      simp only [hy', sub_self]
    · filter_upwards [hside] with p hp ha
      exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr
        (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using hp ha))
  rw [hd.fderiv]
  exact neg_pos.mp hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall ``Submission.DifferentialGeometry.Analysis.fderiv_norm_sq_apply_neg_of_eventually_mem_closedBall

end DifferentialGeometry.Analysis
