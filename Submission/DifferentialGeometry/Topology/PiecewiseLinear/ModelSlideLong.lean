/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ModelSlide

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def scaleMap (d : ℝ) : ℝ →ᵃ[ℝ] ℝ := (d • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.scaleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.scaleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.scaleMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.scaleMap

theorem scaleMap_apply (d t : ℝ) : scaleMap d t = d * t := by
  change d • t = d * t
  rw [smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.scaleMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.scaleMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.scaleMap_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.scaleMap_apply

noncomputable def slideWidthScaled (d : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  d * (1 - |p.2.1| - |p.2.2|)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideWidthScaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideWidthScaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideWidthScaled ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideWidthScaled

noncomputable def slideTaperRad (R : ℝ) (p : ℝ × ℝ × ℝ) : ℝ := (R - |p.1|) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideTaperRad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideTaperRad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideTaperRad ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideTaperRad

noncomputable def slideAmountLong (d R : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  _root_.Max.max 0 (_root_.Min.min (slideWidthScaled d p) (slideTaperRad R p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong

noncomputable def slideMapLong (d R : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 - slideAmountLong d R p, p.2.1, p.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong

def slideBandA (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.2 = 0 ∧ |p.2.1| ≤ 1 ∧ p.1 ∈ _root_.Set.Icc (0 : ℝ) c}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideBandA then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideBandA"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideBandA ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideBandA

def slideBandQ (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.1 = 0 ∧ |p.2.2| ≤ 1 ∧ p.1 ∈ _root_.Set.Icc a b}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideBandQ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideBandQ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideBandQ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideBandQ

def slideSupportLong (R : ℝ) : Set (ℝ × ℝ × ℝ) := {p | |p.2.1| + |p.2.2| ≤ 1 ∧ |p.1| ≤ R}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong

theorem slideAmountLong_nonneg (d R : ℝ) (p : ℝ × ℝ × ℝ) : 0 ≤ slideAmountLong d R p :=
  le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_nonneg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_nonneg

theorem slideAmountLong_eq_zero_of_width {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 ≤ d)
    (h : 1 ≤ |p.2.1| + |p.2.2|) : slideAmountLong d R p = 0 := by
  have hw : slideWidthScaled d p ≤ 0 := by
    have h1 : 1 - |p.2.1| - |p.2.2| ≤ 0 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd
    simpa [slideWidthScaled] using h2
  simp only [slideAmountLong, max_eq_left (le_trans (min_le_left _ _) hw)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_width ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_width

theorem slideAmountLong_eq_zero_of_taper {d R : ℝ} {p : ℝ × ℝ × ℝ} (h : R ≤ |p.1|) :
    slideAmountLong d R p = 0 := by
  have ht : slideTaperRad R p ≤ 0 := by
    simp only [slideTaperRad]
    linarith
  simp only [slideAmountLong, max_eq_left (le_trans (min_le_right _ _) ht)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_taper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_taper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_taper ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_eq_zero_of_taper

theorem slideMapLong_eq_self_of_width {d R : ℝ} {p : ℝ × ℝ × ℝ} (hd : 0 ≤ d)
    (h : 1 ≤ |p.2.1| + |p.2.2|) : slideMapLong d R p = p := by
  simp only [slideMapLong, slideAmountLong_eq_zero_of_width hd h, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_width ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_width

theorem slideMapLong_eq_self_of_taper {d R : ℝ} {p : ℝ × ℝ × ℝ} (h : R ≤ |p.1|) :
    slideMapLong d R p = p := by
  simp only [slideMapLong, slideAmountLong_eq_zero_of_taper h, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_taper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_taper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_taper ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_eq_self_of_taper

theorem slideAmountLong_le_add {d R : ℝ} {p q : ℝ × ℝ × ℝ} (hyz : p.2 = q.2) (hpq : p.1 ≤ q.1) :
    slideAmountLong d R q ≤ slideAmountLong d R p + (q.1 - p.1) / 2 := by
  have hc : 0 ≤ (q.1 - p.1) / 2 := by linarith
  have hw : slideWidthScaled d q = slideWidthScaled d p := by
    simp only [slideWidthScaled, hyz]
  have hab : |p.1| - |q.1| ≤ q.1 - p.1 := by
    have h := abs_sub_abs_le_abs_sub p.1 q.1
    rwa [abs_of_nonpos (by linarith : p.1 - q.1 ≤ 0), neg_sub] at h
  have hT : slideTaperRad R q ≤ slideTaperRad R p + (q.1 - p.1) / 2 := by
    simp only [slideTaperRad]
    linarith
  have hmin : _root_.Min.min (slideWidthScaled d q) (slideTaperRad R q) ≤
      min (slideWidthScaled d p) (slideTaperRad R p) + (q.1 - p.1) / 2 := by
    rcases le_total (slideWidthScaled d p) (slideTaperRad R p) with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) (by rw [hw]; linarith)
    · rw [min_eq_right h]
      exact le_trans (min_le_right _ _) (by linarith)
  have hmax : _root_.Min.min (slideWidthScaled d p) (slideTaperRad R p) ≤ slideAmountLong d R p :=
    le_max_right _ _
  refine max_le (by linarith [slideAmountLong_nonneg d R p]) ?_
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_le_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_le_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_le_add ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideAmountLong_le_add

theorem injective_slideMapLong {d R : ℝ} : Function.Injective (slideMapLong d R) := by
  intro p q hpq
  have h2 : p.2 = q.2 := by
    have h := congrArg Prod.snd hpq
    exact h
  have h1 : p.1 - slideAmountLong d R p = q.1 - slideAmountLong d R q := congrArg Prod.fst hpq
  have hx : p.1 = q.1 := by
    rcases le_total p.1 q.1 with h | h
    · have hle := slideAmountLong_le_add (d := d) (R := R) h2 h
      linarith
    · have hle := slideAmountLong_le_add (d := d) (R := R) h2.symm h
      linarith
  exact Prod.ext hx h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injective_slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injective_slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injective_slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injective_slideMapLong

theorem isPiecewiseAffineOn_slideMapLong {d R : ℝ} :
    IsPiecewiseAffineOn (slideMapLong d R) univ := by
  have hid : IsPiecewiseAffineOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ :=
    (IsLocallyPolyhedral.of_isOpen isOpen_univ).isPiecewiseAffineOn_id
  have hx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    hid.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hy : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    hid.affine_comp ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hz : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    hid.affine_comp ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hconst : ∀ c : ℝ, IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => c) univ := by
    intro c
    exact hid.affine_comp (AffineMap.const ℝ (ℝ × ℝ × ℝ) c)
  have hwidth : IsPiecewiseAffineOn (slideWidthScaled d) univ := by
    have h := (((hconst 1).add (hy.abs.affine_comp (-AffineMap.id ℝ ℝ))).add
      (hz.abs.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp (scaleMap d)
    refine h.congr fun p _ => ?_
    change slideWidthScaled d p = scaleMap d (1 + -|p.2.1| + -|p.2.2|)
    rw [scaleMap_apply, slideWidthScaled]
    ring
  have htaper : IsPiecewiseAffineOn (slideTaperRad R) univ := by
    have h := ((hconst R).add (hx.abs.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp halfMap
    refine h.congr fun p _ => ?_
    change slideTaperRad R p = halfMap (R + -|p.1|)
    rw [halfMap_apply, slideTaperRad]
    ring
  have hamount : IsPiecewiseAffineOn (slideAmountLong d R) univ :=
    ((hconst 0).max (hwidth.min htaper)).congr fun _ _ => rfl
  have hfirst : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1 - slideAmountLong d R p) univ := by
    have h := hx.add (hamount.affine_comp (-AffineMap.id ℝ ℝ))
    refine h.congr fun p _ => ?_
    change p.1 + -slideAmountLong d R p = p.1 - slideAmountLong d R p
    ring
  exact hfirst.prod_mk (hy.prod_mk hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_slideMapLong

theorem continuous_slideMapLong {d R : ℝ} : Continuous (slideMapLong d R) := by
  rw [← continuousOn_univ]
  exact isPiecewiseAffineOn_slideMapLong.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuous_slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuous_slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuous_slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuous_slideMapLong

theorem surjective_slideMapLong {d R : ℝ} (hR : 0 ≤ R) :
    Function.Surjective (slideMapLong d R) := by
  intro w
  have hcont : Continuous fun x : ℝ => (slideMapLong d R (x, w.2.1, w.2.2)).1 :=
    continuous_fst.comp (continuous_slideMapLong.comp (by fun_prop))
  rcases le_or_gt |w.1| R with hle | hgt
  · have h3 : (slideMapLong d R ((R : ℝ), w.2.1, w.2.2)).1 = R := by
      rw [slideMapLong_eq_self_of_taper (p := ((R : ℝ), w.2.1, w.2.2))
        (by simp [abs_of_nonneg hR])]
    have hm3 : (slideMapLong d R ((-R : ℝ), w.2.1, w.2.2)).1 = -R := by
      rw [slideMapLong_eq_self_of_taper (p := ((-R : ℝ), w.2.1, w.2.2))
        (by simp [abs_of_nonneg hR])]
    have hmem : w.1 ∈ _root_.Set.Icc ((slideMapLong d R ((-R : ℝ), w.2.1, w.2.2)).1)
        ((slideMapLong d R ((R : ℝ), w.2.1, w.2.2)).1) := by
      rw [h3, hm3]
      exact abs_le.mp hle
    obtain ⟨x, -, hgx⟩ :=
      intermediate_value_Icc (by linarith : (-R : ℝ) ≤ R) hcont.continuousOn hmem
    exact ⟨(x, w.2.1, w.2.2), Prod.ext hgx rfl⟩
  · refine ⟨(w.1, w.2.1, w.2.2), ?_⟩
    rw [slideMapLong_eq_self_of_taper (p := (w.1, w.2.1, w.2.2)) (by simpa using hgt.le)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.surjective_slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.surjective_slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.surjective_slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjective_slideMapLong

theorem bijective_slideMapLong {d R : ℝ} (hR : 0 ≤ R) : Function.Bijective (slideMapLong d R) :=
  ⟨injective_slideMapLong, surjective_slideMapLong hR⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bijective_slideMapLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bijective_slideMapLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bijective_slideMapLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bijective_slideMapLong

theorem slideMapLong_snd (d R : ℝ) (p : ℝ × ℝ × ℝ) : (slideMapLong d R p).2 = p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideMapLong_snd

theorem mapsTo_slideMapLong_prod {d R : ℝ} (T : Set (ℝ × ℝ)) :
    MapsTo (slideMapLong d R) {p : ℝ × ℝ × ℝ | p.2 ∈ T} {p : ℝ × ℝ × ℝ | p.2 ∈ T} :=
  fun _ hp => hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_prod ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_prod

theorem bijOn_slideMapLong_prod {d R : ℝ} (hR : 0 ≤ R) (T : Set (ℝ × ℝ)) :
    BijOn (slideMapLong d R) {p : ℝ × ℝ × ℝ | p.2 ∈ T} {p : ℝ × ℝ × ℝ | p.2 ∈ T} := by
  refine ⟨mapsTo_slideMapLong_prod T, injective_slideMapLong.injOn, ?_⟩
  intro w hw
  obtain ⟨p, hp⟩ := surjective_slideMapLong (d := d) hR w
  refine ⟨p, ?_, hp⟩
  have h2 : p.2 = w.2 := by
    rw [← slideMapLong_snd d R p, hp]
  change p.2 ∈ T
  rw [h2]
  exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_slideMapLong_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bijOn_slideMapLong_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_slideMapLong_prod ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bijOn_slideMapLong_prod

theorem isClosed_slideSupportLong (R : ℝ) : IsClosed (slideSupportLong R) := by
  have h1 : Continuous fun p : ℝ × ℝ × ℝ => |p.2.1| + |p.2.2| :=
    (continuous_abs.comp (continuous_fst.comp continuous_snd)).add
      (continuous_abs.comp (continuous_snd.comp continuous_snd))
  have h2 : Continuous fun p : ℝ × ℝ × ℝ => |p.1| := continuous_abs.comp continuous_fst
  exact (isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_slideSupportLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClosed_slideSupportLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_slideSupportLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClosed_slideSupportLong

theorem slideSupportLong_subset_closedBall (R : ℝ) :
    slideSupportLong R ⊆ Metric.closedBall 0 (_root_.Max.max R 1) := by
  rintro p ⟨h1, h2⟩
  have hy : |p.2.1| ≤ 1 := by
    have := abs_nonneg p.2.2
    linarith
  have hz : |p.2.2| ≤ 1 := by
    have := abs_nonneg p.2.1
    linarith
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff]
  exact ⟨le_trans h2 (le_max_left _ _), le_trans hy (le_max_right _ _),
    le_trans hz (le_max_right _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong_subset_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong_subset_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong_subset_closedBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slideSupportLong_subset_closedBall

theorem isCompact_slideSupportLong (R : ℝ) : IsCompact (slideSupportLong R) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_slideSupportLong R)
    ((Metric.isBounded_closedBall).subset (slideSupportLong_subset_closedBall R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slideSupportLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slideSupportLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slideSupportLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCompact_slideSupportLong

theorem eqOn_slideMapLong_id_compl {d R : ℝ} (hd : 0 ≤ d) :
    EqOn (slideMapLong d R) id (slideSupportLong R)ᶜ := by
  intro p hp
  simp only [slideSupportLong, _root_.Set.mem_compl_iff, _root_.Set.mem_ofPred_eq, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact slideMapLong_eq_self_of_width hd h.le
  · exact slideMapLong_eq_self_of_taper h.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_slideMapLong_id_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eqOn_slideMapLong_id_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eqOn_slideMapLong_id_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eqOn_slideMapLong_id_compl

theorem mapsTo_slideMapLong_slideSupportLong {d R : ℝ} :
    MapsTo (slideMapLong d R) (slideSupportLong R) (slideSupportLong R) := by
  rintro p ⟨h1, h2⟩
  have hnn := slideAmountLong_nonneg d R p
  have hmax : slideAmountLong d R p ≤ _root_.Max.max 0 (slideTaperRad R p) :=
    max_le_max (le_refl 0) (min_le_right _ _)
  have habs := neg_abs_le p.1
  rw [abs_le] at h2
  refine ⟨h1, ?_⟩
  have hfst : (slideMapLong d R p).1 = p.1 - slideAmountLong d R p := rfl
  rw [hfst, abs_le]
  refine ⟨?_, by linarith [h2.2]⟩
  have hle : slideAmountLong d R p ≤ R + p.1 := by
    refine le_trans hmax (max_le (by linarith [h2.1]) ?_)
    simp only [slideTaperRad]
    linarith [h2.1]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_slideSupportLong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_slideSupportLong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_slideSupportLong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_slideSupportLong

theorem mapsTo_slideMapLong_of_subset {d R : ℝ} (hd : 0 ≤ d) {T : Set (ℝ × ℝ × ℝ)}
    (hT : slideSupportLong R ⊆ T) : _root_.Set.MapsTo (slideMapLong d R) T T := by
  intro p hp
  by_cases hC : p ∈ slideSupportLong R
  · exact hT (mapsTo_slideMapLong_slideSupportLong hC)
  · rw [eqOn_slideMapLong_id_compl hd hC]
    exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_of_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_slideMapLong_of_subset

theorem disjoint_slideMapLong_image_slideBandA {d R a b c : ℝ} (hd : 0 ≤ d)
    (hR : c + 2 * d ≤ R) (hca : c - d < a) :
    Disjoint (slideMapLong d R '' slideBandA c) (slideBandQ a b) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, ⟨hz, -, hx0, hx1⟩, rfl⟩ ⟨hy, -, hw1, -⟩
  have hpy : p.2.1 = 0 := hy
  have hwidth : slideWidthScaled d p = d := by
    simp only [slideWidthScaled, hpy, hz, abs_zero]
    ring
  have htaper : d ≤ slideTaperRad R p := by
    simp only [slideTaperRad, abs_of_nonneg hx0]
    linarith
  have hamount : slideAmountLong d R p = d := by
    simp only [slideAmountLong, hwidth, min_eq_left htaper, max_eq_right hd]
  have hfirst : (slideMapLong d R p).1 = p.1 - d := by
    simp only [slideMapLong, hamount]
  rw [hfirst] at hw1
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_slideMapLong_image_slideBandA then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_slideMapLong_image_slideBandA"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_slideMapLong_image_slideBandA ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_slideMapLong_image_slideBandA

end DifferentialGeometry.Topology.PiecewiseLinear
