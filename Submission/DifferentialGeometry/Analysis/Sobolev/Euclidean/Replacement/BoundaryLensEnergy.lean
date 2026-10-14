import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Composition
import Submission.DifferentialGeometry.Analysis.Complex.BoundaryLens.Geometry
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.LoopCone
import Mathlib.Analysis.Calculus.MeanValue
import Submission.DifferentialGeometry.Analysis.Sobolev.Interval.ArcEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

theorem exists_boundaryLens_homeomorph_energy_bound {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = boundaryLensCenter ρ +
        ρ • gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ) z) ∧
      LipschitzWith (Real.toNNReal (12 * ρ)) e ∧
      LipschitzWith (Real.toNNReal (12 / ρ)) e.symm ∧
      e '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      e '' _root_.Metric.sphere (0 : ℂ) 1 = frontier (boundaryLens ρ) ∧
      ∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        (f : ℂ → F) (D : ℝ≥0), LipschitzWith D f →
        ((∫ z in boundaryLens ρ, ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
          (12 : ℝ) ^ 4 * ∫ z in _root_.Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ∧
        ((∫ z in boundaryLens ρ, (‖fderiv ℝ (f ∘ e.symm) z 1‖ ^ 2 +
          ‖fderiv ℝ (f ∘ e.symm) z Complex.I‖ ^ 2) / 2) ≤
          2 * (12 : ℝ) ^ 4 * ∫ z in _root_.Metric.closedBall (0 : ℂ) 1,
            (‖fderiv ℝ f z 1‖ ^ 2 + ‖fderiv ℝ f z Complex.I‖ ^ 2) / 2) := by
  obtain ⟨e, heq, he, hei, hset, hboundary⟩ :=
    exists_boundaryLens_bilipschitz_homeomorph hρ hρ1
  refine ⟨e, heq, he, hei, hset, hboundary, ?_⟩
  intro F _ _ _ f D hf
  have hs : e.symm ⁻¹' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ := by
    rw [← hset]
    ext z
    constructor
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [_root_.Set.mem_preimage, e.symm_apply_apply] using hx
  have hconst : ((Real.toNNReal (12 / ρ) : ℝ≥0) : ℝ) ^ 2 *
      ((Real.toNNReal (12 * ρ) : ℝ≥0) : ℝ) ^ 2 = (12 : ℝ) ^ 4 := by
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    field_simp
  constructor
  · have h := e.symm.integral_norm_fderiv_comp_sq_le (μ := _root_.MeasureTheory.MeasureSpace.volume) hei he hf
      measurableSet_closedBall (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top
    simpa only [hs, Complex.finrank_real_complex, hconst] using h
  · have h := e.symm.integral_plane_dirichlet_energy_comp_le hei he hf
      measurableSet_closedBall (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top
    rw [hs] at h
    have hc : 2 * ((Real.toNNReal (12 / ρ) : ℝ≥0) : ℝ) ^ 2 *
        ((Real.toNNReal (12 * ρ) : ℝ≥0) : ℝ) ^ 2 = 2 * (12 : ℝ) ^ 4 := by
      rw [mul_assoc, hconst]
    simpa only [hc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_boundaryLens_homeomorph_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_boundaryLens_homeomorph_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_boundaryLens_homeomorph_energy_bound ``Submission.DifferentialGeometry.Analysis.exists_boundaryLens_homeomorph_energy_bound

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.ENNReal _root_.Topology



namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_retracted_periodicLoopCone_boundaryLens_filling
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K U : Set F} (p : F) (hp : p ∈ K) {ε : ℝ}
    (hεU : _root_.Metric.closedBall p ε ⊆ U) {a : ℝ → F} {La : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith La a)
    (haK : ∀ t, a t ∈ K) (haε : ∀ t, ‖a t - p‖ ≤ ε)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : _root_.Set.MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    ∃ e : ℂ ≃ₜ ℂ,
      (∀ z, e z = boundaryLensCenter ρ +
        ρ • gaugeRescale (_root_.Metric.ball (0 : ℂ) 1) (normalizedBoundaryLens ρ) z) ∧
      LipschitzWith (Real.toNNReal (12 * ρ)) e ∧
      LipschitzWith (Real.toNNReal (12 / ρ)) e.symm ∧
      e '' _root_.Metric.closedBall (0 : ℂ) 1 = boundaryLens ρ ∧
      e '' _root_.Metric.sphere (0 : ℂ) 1 = frontier (boundaryLens ρ) ∧
      let q : ℂ → F := T ∘ periodicLoopCone p ha ∘ e.symm
      LipschitzWith (LT * (2 * La + Real.toNNReal ε) * Real.toNNReal (12 / ρ)) q ∧
      _root_.Set.MapsTo q (boundaryLens ρ) K ∧ q (e 0) = p ∧
      (∀ t, q (e (circleMap 0 1 (2 * Real.pi * t - Real.pi))) = a t) ∧
      (∫ z in boundaryLens ρ, (‖fderiv ℝ q z 1‖ ^ 2 +
        ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤
        2 * (12 : ℝ) ^ 4 * (LT : ℝ) ^ 2 *
          ((Real.pi / 2) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a t - p‖ ^ 2) +
            (1 / (8 * Real.pi)) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2)) := by
  have hε : 0 ≤ ε := (norm_nonneg (a 0 - p)).trans (haε 0)
  have hcircle (z : Circle) : periodicCircleMap ha z ∈ K ∧
      ‖periodicCircleMap ha z - p‖ ≤ ε := by
    let ξ : loopCircle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z +
      ((1 / 2 : ℝ) : loopCircle)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective ξ
    change ha.lift ξ ∈ K ∧ ‖ha.lift ξ - p‖ ≤ ε
    rw [← ht, Function.Periodic.lift_coe]
    exact ⟨haK t, haε t⟩
  have hcone : LipschitzWith (2 * La + Real.toNNReal ε) (periodicLoopCone p ha) :=
    radialCone_lipschitz (periodicCircleMap_lipschitz ha hLip)
      (fun z => (hcircle z).2.trans (Real.le_coe_toNNReal ε))
  have hconeU : _root_.Set.MapsTo (periodicLoopCone p ha) (_root_.Metric.closedBall (0 : ℂ) 1) U := by
    intro z hz
    apply hεU
    rw [_root_.Metric.mem_closedBall, dist_eq_norm]
    change ‖(p + ‖z‖ • (periodicCircleMap ha (radialDirection z) - p)) - p‖ ≤ ε
    rw [add_sub_cancel_left, norm_smul, norm_norm]
    have hz1 : ‖z‖ ≤ 1 := by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz
    exact (mul_le_mul_of_nonneg_left (hcircle _).2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hz1 hε)
  have hTLip : LipschitzWith LT T :=
    lipschitzWith_of_nnnorm_fderiv_le hT hLT
  obtain ⟨e, heq, he, hei, himage, hboundary, henergy⟩ :=
    exists_boundaryLens_homeomorph_energy_bound hρ hρ1
  let q : ℂ → F := T ∘ periodicLoopCone p ha ∘ e.symm
  refine ⟨e, heq, he, hei, himage, hboundary, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hTLip.comp hcone).comp hei
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (himage.symm ▸ hz)
    exact hmap (by simpa only [Function.comp_apply, e.symm_apply_apply] using hconeU hy)
  · change T (periodicLoopCone p ha (e.symm (e 0))) = p
    rw [e.symm_apply_apply]
    exact (congrArg T (radialCone_zero p (periodicCircleMap ha))).trans (hfix p hp)
  · intro t
    change T (periodicLoopCone p ha (e.symm (e _))) = a t
    rw [e.symm_apply_apply, periodicLoopCone_boundary]
    exact hfix _ (haK t)
  · have htrans := (henergy F (T ∘ periodicLoopCone p ha) _ (hTLip.comp hcone)).2
    have hpost := hT.integral_plane_dirichlet_energy_comp_le hLT hcone
      (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top
    have hbase := integral_energy_periodicLoopCone_le p ha hLip
    have h := htrans.trans ((mul_le_mul_of_nonneg_left
      (hpost.trans (mul_le_mul_of_nonneg_left hbase (sq_nonneg (LT : ℝ))))) (by positivity))
    change (∫ z in boundaryLens ρ, (‖fderiv ℝ q z 1‖ ^ 2 +
      ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤ _
    simpa only [q, Function.comp_assoc, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_retracted_periodicLoopCone_boundaryLens_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_retracted_periodicLoopCone_boundaryLens_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_retracted_periodicLoopCone_boundaryLens_filling ``Submission.DifferentialGeometry.Analysis.exists_retracted_periodicLoopCone_boundaryLens_filling

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem retracted_periodicLoopCone_homeomorph_filling
    (e : ℂ ≃ₜ ℂ) {A B : ℝ≥0} (he : LipschitzWith A e) (hei : LipschitzWith B e.symm)
    {K U : Set F} (p : F) (hp : p ∈ K) {ε : ℝ}
    (hεU : _root_.Metric.closedBall p ε ⊆ U) {a : ℝ → F} {La : ℝ≥0}
    (ha : Function.Periodic a 1) (hLip : LipschitzWith La a)
    (haK : ∀ t, a t ∈ K) (haε : ∀ t, ‖a t - p‖ ≤ ε)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : _root_.Set.MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    let q : ℂ → F := T ∘ periodicLoopCone p ha ∘ e.symm
    LipschitzWith (LT * (2 * La + Real.toNNReal ε) * B) q ∧
      _root_.Set.MapsTo q (e '' _root_.Metric.closedBall (0 : ℂ) 1) K ∧ q (e 0) = p ∧
      (∀ t, q (e (circleMap 0 1 (2 * Real.pi * t - Real.pi))) = a t) ∧
      (∫ z in e '' _root_.Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤
        2 * (A : ℝ) ^ 2 * (B : ℝ) ^ 2 * (LT : ℝ) ^ 2 *
          ((Real.pi / 2) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a t - p‖ ^ 2) +
            (1 / (8 * Real.pi)) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2)) := by
  have hε : 0 ≤ ε := (norm_nonneg (a 0 - p)).trans (haε 0)
  have hcircle (z : Circle) : ‖periodicCircleMap ha z - p‖ ≤ ε := by
    let ξ : loopCircle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z +
      ((1 / 2 : ℝ) : loopCircle)
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective ξ
    change ‖ha.lift ξ - p‖ ≤ ε
    rw [← ht, Function.Periodic.lift_coe]
    exact haε t
  have hcone : LipschitzWith (2 * La + Real.toNNReal ε) (periodicLoopCone p ha) :=
    radialCone_lipschitz (periodicCircleMap_lipschitz ha hLip)
      (fun z => (hcircle z).trans (Real.le_coe_toNNReal ε))
  have hconeU : _root_.Set.MapsTo (periodicLoopCone p ha) (_root_.Metric.closedBall (0 : ℂ) 1) U := by
    intro z hz
    apply hεU
    rw [_root_.Metric.mem_closedBall, dist_eq_norm]
    change ‖(p + ‖z‖ • (periodicCircleMap ha (radialDirection z) - p)) - p‖ ≤ ε
    rw [add_sub_cancel_left, norm_smul, norm_norm]
    have hz1 : ‖z‖ ≤ 1 := by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz
    exact (mul_le_mul_of_nonneg_left (hcircle _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hz1 hε)
  have hTLip : LipschitzWith LT T := lipschitzWith_of_nnnorm_fderiv_le hT hLT
  let q : ℂ → F := T ∘ periodicLoopCone p ha ∘ e.symm
  refine ⟨(hTLip.comp hcone).comp hei, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact hmap (by simpa only [Function.comp_apply, e.symm_apply_apply] using hconeU hy)
  · change T (periodicLoopCone p ha (e.symm (e 0))) = p
    rw [e.symm_apply_apply]
    exact (congrArg T (radialCone_zero p (periodicCircleMap ha))).trans (hfix p hp)
  · intro t
    change T (periodicLoopCone p ha (e.symm (e _))) = a t
    rw [e.symm_apply_apply, periodicLoopCone_boundary]
    exact hfix _ (haK t)
  · have hpre : e.symm ⁻¹' _root_.Metric.closedBall (0 : ℂ) 1 = e '' _root_.Metric.closedBall (0 : ℂ) 1 := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
      · rintro ⟨x, hx, rfl⟩
        simpa only [_root_.Set.mem_preimage, e.symm_apply_apply] using hx
    have htrans := e.symm.integral_plane_dirichlet_energy_comp_le hei he (hTLip.comp hcone)
      measurableSet_closedBall (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top
    rw [hpre] at htrans
    have hpost := hT.integral_plane_dirichlet_energy_comp_le hLT hcone
      (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top
    have hbase := integral_energy_periodicLoopCone_le p ha hLip
    have h := htrans.trans (mul_le_mul_of_nonneg_left
      (hpost.trans (mul_le_mul_of_nonneg_left hbase (sq_nonneg (LT : ℝ)))) (by positivity))
    change (∫ z in e '' _root_.Metric.closedBall (0 : ℂ) 1,
      (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤ _
    simpa only [q, Function.comp_assoc, mul_assoc, mul_left_comm, mul_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.retracted_periodicLoopCone_homeomorph_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.retracted_periodicLoopCone_homeomorph_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.retracted_periodicLoopCone_homeomorph_filling ``Submission.DifferentialGeometry.Analysis.retracted_periodicLoopCone_homeomorph_filling

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem retracted_joinedLoop_affine_arc_homeomorph_filling
    (e : ℂ ≃ₜ ℂ) {A B : ℝ≥0} (he : LipschitzWith A e) (hei : LipschitzWith B e.symm)
    {K U : Set F} (a Γ : ℝ → F) {Ka KΓ J : ℝ≥0}
    (ha : LipschitzWith Ka a) (hΓ : LipschitzWith KΓ Γ) (hperiod : Function.Periodic Γ 1)
    (hInv : AntilipschitzWith J (hperiod.lift : loopCircle → F))
    {p₀ p₁ : ℝ} (hp : p₀ ≤ p₁) (hshort : p₁ - p₀ ≤ 2 / 3)
    (ha₀ : a 0 = Γ p₁) (ha₁ : a 1 = Γ p₀)
    (haK : _root_.Set.MapsTo a (_root_.Set.Icc (0 : ℝ) 1) K) (hΓK : _root_.Set.range Γ ⊆ K)
    {η : ℝ} (hηU : _root_.Metric.closedBall (a 0) η ⊆ U)
    (hsmall : (1 + 2 * (KΓ : ℝ) * (J : ℝ)) *
      Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2) ≤ η)
    (T : F → F) (hT : Differentiable ℝ T) {LT : ℝ≥0}
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : _root_.Set.MapsTo T U K)
    (hfix : ∀ y ∈ K, T y = y) :
    let b : ℝ → F := fun t => Γ ((1 - t) * p₀ + t * p₁)
    let q : ℂ → F := T ∘ periodicLoopCone (a 0) (joinedLoop_periodic a b) ∘ e.symm
    LipschitzWith
      (LT * (2 * _root_.Max.max (2 * Ka) (2 * (KΓ * Real.nnabs (p₁ - p₀))) + Real.toNNReal η) * B) q ∧
      _root_.Set.MapsTo q (e '' _root_.Metric.closedBall (0 : ℂ) 1) K ∧ q (e 0) = a 0 ∧
      (∀ t, q (e (circleMap 0 1 (2 * Real.pi * t - Real.pi))) = joinedLoop a b t) ∧
      (∫ z in e '' _root_.Metric.closedBall (0 : ℂ) 1,
        (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) ≤
        2 * (A : ℝ) ^ 2 * (B : ℝ) ^ 2 * (LT : ℝ) ^ 2 *
          ((Real.pi / 2) * (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 +
            (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi)) *
          (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2) := by
  let b : ℝ → F := fun t => Γ ((1 - t) * p₀ + t * p₁)
  let Ea : ℝ := ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2
  obtain ⟨hb₀, hb₁, hb, _, _, hder, hnorm, hgap⟩ :=
    joinedLoop_affine_arc_energy_and_norm_bound a Γ ha hΓ hperiod hInv hp hshort ha₀ ha₁
  have hjlip : LipschitzWith (_root_.Max.max (2 * Ka) (2 * (KΓ * Real.nnabs (p₁ - p₀))))
      (joinedLoop a b) := joinedLoop_lipschitz ha hb hb₀.symm hb₁
  have hjK : ∀ t, joinedLoop a b t ∈ K :=
    fun t => mapsTo_joinedLoop_affine_arc haK hΓK (_root_.Set.mem_univ t)
  have hjη : ∀ t, ‖joinedLoop a b t - a 0‖ ≤ η :=
    fun t => (hnorm t).trans hsmall
  obtain ⟨hLipq, hKq, hcenter, hboundary, henergy⟩ :=
    retracted_periodicLoopCone_homeomorph_filling e he hei (a 0) (haK (by norm_num)) hηU
      (joinedLoop_periodic a b) hjlip hjK hjη T hT hLT hmap hfix
  refine ⟨hLipq, hKq, hcenter, hboundary, ?_⟩
  have hbracket :
      (Real.pi / 2) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖joinedLoop a b t - a 0‖ ^ 2) +
        (1 / (8 * Real.pi)) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (joinedLoop a b) t‖ ^ 2) ≤
      ((Real.pi / 2) * (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 +
        (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) / (8 * Real.pi)) * Ea := by
    have h1 := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ Real.pi / 2)
    have h2 := mul_le_mul_of_nonneg_left hder (by positivity : 0 ≤ 1 / (8 * Real.pi))
    calc
      _ ≤ (Real.pi / 2) * ((1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 * Ea) +
          (1 / (8 * Real.pi)) * ((2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) * Ea) :=
        add_le_add h1 h2
      _ = _ := by ring
  exact henergy.trans ((mul_le_mul_of_nonneg_left hbracket (by positivity)).trans_eq
    (mul_assoc _ _ _).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.retracted_joinedLoop_affine_arc_homeomorph_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.retracted_joinedLoop_affine_arc_homeomorph_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.retracted_joinedLoop_affine_arc_homeomorph_filling ``Submission.DifferentialGeometry.Analysis.retracted_joinedLoop_affine_arc_homeomorph_filling

end DifferentialGeometry.Analysis

end
