import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.ODE.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def VectorFieldTangentTo (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ t x, x ∈ C → f t x ∈ posTangentConeAt C x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo ``Submission.DifferentialGeometry.Analysis.ODE.VectorFieldTangentTo

def IsForwardInvariantForODE (f : ℝ → E → E) (C : Set E) : Prop :=
  ∀ a b, a ≤ b → ∀ γ : ℝ → E,
    IsIntegralCurveOn γ f (_root_.Set.Icc a b) → γ a ∈ C → _root_.Set.MapsTo γ (_root_.Set.Icc a b) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE

def IsForwardInvariantForODEOn (f : ℝ → E → E) (C : Set E) (J : Set ℝ) : Prop :=
  ∀ a b, a ≤ b → _root_.Set.Icc a b ⊆ J → ∀ γ : ℝ → E,
    IsIntegralCurveOn γ f (_root_.Set.Icc a b) → γ a ∈ C → _root_.Set.MapsTo γ (_root_.Set.Icc a b) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn

@[simp] theorem isForwardInvariantForODEOn_univ {f : ℝ → E → E} {C : Set E} :
    IsForwardInvariantForODEOn f C _root_.Set.univ ↔ IsForwardInvariantForODE f C := by
  constructor
  · exact fun h a b hab γ hγ hinit => h a b hab (_root_.Set.subset_univ _) γ hγ hinit
  · exact fun h a b hab _ γ hγ hinit => h a b hab γ hγ hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_univ ``Submission.DifferentialGeometry.Analysis.ODE.isForwardInvariantForODEOn_univ

theorem IsForwardInvariantForODEOn.mono {f : ℝ → E → E} {C : Set E} {J K : Set ℝ}
    (h : IsForwardInvariantForODEOn f C J) (hKJ : K ⊆ J) :
    IsForwardInvariantForODEOn f C K :=
  fun a b hab hsub γ hγ hinit => h a b hab (hsub.trans hKJ) γ hγ hinit

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.mono ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn.mono


theorem HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right
    {γ : ℝ → E} {t : ℝ} {v : E} {C : Set E}
    (hγ : HasDerivAt γ v t) (hC : ∀ᶠ h in 𝓝[>] (0 : ℝ), γ (t + h) ∈ C) :
    v ∈ posTangentConeAt C (γ t) := by
  let c : ℝ → ℝ≥0 := fun h ↦ ⟨max h⁻¹ 0, le_max_right _ _⟩
  let d : ℝ → E := fun h ↦ γ (t + h) - γ t
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) c d ?_ ?_ ?_
  · have htadd : _root_.Filter.Tendsto (fun h : ℝ ↦ t + h) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
      simpa using
        (tendsto_const_nhds.add _root_.Filter.tendsto_id).mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    simpa [d, Function.comp_def] using
      (hγ.continuousAt.tendsto.comp htadd).sub_const (γ t)
  · filter_upwards [hC] with h hh
    simpa [d] using hh
  · apply Tendsto.congr' _ hγ.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    rw [NNReal.smul_def]
    simp [c, d, max_eq_left (inv_nonneg.mpr hpos.le)]
    congr 1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.HasDerivAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right ``Submission.DifferentialGeometry.Analysis.ODE.HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right
    {f : ℝ → E → E} {γ : ℝ → E} {t : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hC : _root_.Set.MapsTo γ (_root_.Set.Ici t) C) :
    f t (γ t) ∈ posTangentConeAt C (γ t) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ t)
  filter_upwards [self_mem_nhdsWithin] with h hh
  apply hC
  change t ≤ t + h
  exact le_add_of_nonneg_right hh.le

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurve
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_right

theorem IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc
    {f : ℝ → E → E} {γ : ℝ → E} {a b : ℝ} {C : Set E}
    (hγ : IsIntegralCurve γ f) (hab : a < b) (hC : _root_.Set.MapsTo γ (_root_.Set.Icc a b) C) :
    f a (γ a) ∈ posTangentConeAt C (γ a) := by
  apply HasDerivAt.mem_posTangentConeAt_of_eventually_mem_right (hγ a)
  have hb : _root_.Set.Iio (b - a) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (sub_pos.mpr hab)
  have hb' : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ _root_.Set.Iio (b - a) :=
    Filter.Eventually.filter_mono inf_le_left hb
  filter_upwards [self_mem_nhdsWithin, hb'] with h hpos hlt
  apply hC
  constructor
  · exact le_add_of_nonneg_right hpos.le
  · have hlt' : h < b - a := hlt
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurve.mem_posTangentConeAt_of_mapsTo_Icc

theorem HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right
    {γ : ℝ → E} {t : ℝ} {v : E} {C : Set E}
    (hγ : HasDerivWithinAt γ v (_root_.Set.Ici t) t)
    (hC : ∀ᶠ s in 𝓝[>] t, γ s ∈ C) :
    v ∈ posTangentConeAt C (γ t) := by
  let c : ℝ → ℝ≥0 := fun s ↦ ⟨max (s - t)⁻¹ 0, le_max_right _ _⟩
  let d : ℝ → E := fun s ↦ γ s - γ t
  refine mem_tangentConeAt_of_seq (𝓝[>] t) c d ?_ ?_ ?_
  · simpa only [sub_self] using
      (hγ.continuousWithinAt.tendsto.mono_left
        (nhdsWithin_mono t _root_.Set.Ioi_subset_Ici_self)).sub_const (γ t)
  · filter_upwards [hC] with s hs
    simpa [d] using hs
  · have hslope : _root_.Filter.Tendsto (slope γ t) (𝓝[>] t) (𝓝 v) := by
      have heq : _root_.Set.Ici t \ {t} = _root_.Set.Ioi t := by
        ext s
        simp only [Set.mem_sdiff, _root_.Set.mem_Ici, _root_.Set.mem_singleton_iff, _root_.Set.mem_Ioi]
        constructor
        · exact fun h => lt_of_le_of_ne h.1 (Ne.symm h.2)
        · exact fun h => ⟨h.le, ne_of_gt h⟩
      simpa only [heq] using (hasDerivWithinAt_iff_tendsto_slope.mp hγ)
    apply Tendsto.congr' _ hslope
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : 0 < s - t := sub_pos.mpr hs
    rw [NNReal.smul_def]
    simp [c, d, slope, max_eq_left (inv_nonneg.mpr hst.le)]
    rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.HasDerivWithinAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right ``Submission.DifferentialGeometry.Analysis.ODE.HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right

theorem IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc
    {f : ℝ → E → E} {γ : ℝ → E} {a b : ℝ} {C : Set E}
    (hγ : IsIntegralCurveOn γ f (_root_.Set.Icc a b)) (hab : a < b)
    (hC : _root_.Set.MapsTo γ (_root_.Set.Icc a b) C) :
    f a (γ a) ∈ posTangentConeAt C (γ a) := by
  apply HasDerivWithinAt.mem_posTangentConeAt_of_eventually_mem_right
    ((hγ a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (show a ∈ _root_.Set.Ico a b from ⟨le_rfl, hab⟩)))
  have hb : ∀ᶠ s in 𝓝[>] a, s < b :=
    Filter.Eventually.filter_mono inf_le_left
      (isOpen_Iio.mem_nhds (show a ∈ _root_.Set.Iio b from hab))
  filter_upwards [self_mem_nhdsWithin, hb] with s hsa hsb
  exact hC ⟨hsa.le, hsb.le⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc ``Submission.DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt
    {f : ℝ → E → E} {C : Set E} (hC : IsForwardInvariantForODE f C)
    (hex : ∀ t x, x ∈ C → ∃ γ : ℝ → E, IsIntegralCurveAt γ f t ∧ γ t = x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨γ, hγ, hγt⟩ := hex t x hx
  obtain ⟨ε, hε, hγBall⟩ := isIntegralCurveAt_iff_exists_pos.mp hγ
  have hinterval : _root_.Set.Icc t (t + ε / 2) ⊆ Metric.ball t ε := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith [hs.2]
  have hγIcc := hγBall.mono hinterval
  have hmap : _root_.Set.MapsTo γ (_root_.Set.Icc t (t + ε / 2)) C :=
    hC t (t + ε / 2) (by linarith) γ hγIcc (hγt.symm ▸ hx)
  simpa [hγt] using
    IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc hγIcc (by linarith) hmap

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurveAt


theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve
    {f : ℝ → E → E} {C : Set E} (hC : IsForwardInvariantForODE f C)
    (hex : ∀ t x, ∃ γ : ℝ → E, IsIntegralCurve γ f ∧ γ t = x) :
    VectorFieldTangentTo f C := by
  apply hC.vectorFieldTangentTo_of_exists_isIntegralCurveAt
  intro t x _
  obtain ⟨γ, hγ, hγt⟩ := hex t x
  exact ⟨γ, hγ.isIntegralCurveAt t, hγt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.vectorFieldTangentTo_of_exists_isIntegralCurve

theorem IsForwardInvariantForODE.inter
    {f : ℝ → E → E} {C D : Set E}
    (hC : IsForwardInvariantForODE f C) (hD : IsForwardInvariantForODE f D) :
    IsForwardInvariantForODE f (C ∩ D) := by
  intro a b hab γ hγ hγab
  exact (hC a b hab γ hγ hγab.1).inter (hD a b hab γ hγ hγab.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.inter ``Submission.DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE.inter

theorem isForwardInvariantForODE_univ (f : ℝ → E → E) :
    IsForwardInvariantForODE f univ := by
  intro a b hab γ hγ ha
  exact _root_.Set.mapsTo_univ γ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_univ ``Submission.DifferentialGeometry.Analysis.ODE.isForwardInvariantForODE_univ

theorem Convex.vectorFieldTangentTo_of_sub_mem
    {f : ℝ → E → E} {C : Set E} (hC : Convex ℝ C)
    (hf : ∀ t x, x ∈ C → ∃ y ∈ C, f t x = y - x) :
    VectorFieldTangentTo f C := by
  intro t x hx
  obtain ⟨y, hy, hfy⟩ := hf t x hx
  rw [hfy]
  exact sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx hy)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.Convex
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.Convex.vectorFieldTangentTo_of_sub_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.Convex.vectorFieldTangentTo_of_sub_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.Convex.vectorFieldTangentTo_of_sub_mem ``Submission.DifferentialGeometry.Analysis.ODE.Convex.vectorFieldTangentTo_of_sub_mem

theorem ConvexCone.vectorFieldTangentTo_of_mapsTo
    (C : ConvexCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, _root_.Set.MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.ConvexCone
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.ConvexCone.vectorFieldTangentTo_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.ConvexCone.vectorFieldTangentTo_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.ConvexCone.vectorFieldTangentTo_of_mapsTo ``Submission.DifferentialGeometry.Analysis.ODE.ConvexCone.vectorFieldTangentTo_of_mapsTo

theorem ProperCone.vectorFieldTangentTo_of_mapsTo
    (C : ProperCone ℝ E) {f : ℝ → E → E}
    (hf : ∀ t, _root_.Set.MapsTo (f t) C C) :
    VectorFieldTangentTo f C := by
  apply Convex.vectorFieldTangentTo_of_sub_mem C.convex
  intro t x hx
  refine ⟨x + f t x, C.add_mem hx (hf t hx), ?_⟩
  abel

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.ODE.ProperCone
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.ProperCone.vectorFieldTangentTo_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.ProperCone.vectorFieldTangentTo_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.ProperCone.vectorFieldTangentTo_of_mapsTo ``Submission.DifferentialGeometry.Analysis.ODE.ProperCone.vectorFieldTangentTo_of_mapsTo

end DifferentialGeometry.Analysis.ODE
