import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Metric _root_.Set
open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

open _root_.MeasureTheory in
theorem lintegral_polar_prod (f : E → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
        f (z.2.1 • z.1.1)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ x in ({0}ᶜ : Set E), f x ∂μ := by
      exact congrArg (fun ν : _root_.MeasureTheory.Measure E => ∫⁻ x, f x ∂ν)
        (_root_.MeasureTheory.restrict_compl_singleton (μ := μ) 0).symm
    _ = ∫⁻ x : ({0}ᶜ : Set E), f x ∂(μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
      rw [_root_.MeasureTheory.lintegral_subtype_comap isOpen_compl_singleton.measurableSet]
    _ = ∫⁻ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
          f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [Φ, Homeomorph.symm_apply_apply] using
        (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          Φ.measurableEmbedding
          (fun z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) =>
            f ((Φ.symm z : ({0}ᶜ : Set E)) : E)))
    _ = ∫⁻ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
          f (z.2.1 • z.1.1)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.lintegral_polar_prod then
    throwError "Refusing to shadow existing declaration MeasureTheory.lintegral_polar_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.lintegral_polar_prod ``Submission.MeasureTheory.lintegral_polar_prod

open _root_.MeasureTheory in
theorem lintegral_polar (f : E → ℝ≥0∞) (hf : AEMeasurable f μ) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ), f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  let Φ := homeomorphUnitSphereProd E
  let G : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun z => f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
  have hfsub : AEMeasurable
      (fun x : ({0}ᶜ : Set E) => f x)
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
    exact (aemeasurable_restrict_iff_comap_subtype
      isOpen_compl_singleton.measurableSet).mp hf.restrict
  have hG : AEMeasurable G
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.map_eq]
    apply Φ.measurableEmbedding.aemeasurable_map_iff.mpr
    have hfun : G ∘ Φ = fun x : ({0}ᶜ : Set E) => f x := by
      funext x
      simp only [G, Function.comp_apply]
      rw [Φ.symm_apply_apply]
    rw [hfun]
    exact hfsub
  rw [lintegral_polar_prod μ f]
  simpa only [G, Φ, homeomorphUnitSphereProd_symm_apply_coe] using
    (_root_.MeasureTheory.lintegral_prod G hG)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.lintegral_polar then
    throwError "Refusing to shadow existing declaration MeasureTheory.lintegral_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.lintegral_polar ``Submission.MeasureTheory.lintegral_polar

section Signed

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open _root_.MeasureTheory in
theorem integrable_ioiPow_iff (d : ℕ) (F : ℝ → G) :
    _root_.MeasureTheory.Integrable (fun r : _root_.Set.Ioi (0 : ℝ) => F r.1) (Measure.volumeIoiPow d) ↔
      IntegrableOn (fun r : ℝ => r ^ d • F r) (_root_.Set.Ioi (0 : ℝ)) := by
  rw [_root_.MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioi, Function.comp_def,
    Measure.volumeIoiPow, _root_.MeasureTheory.integrable_withDensity_iff_integrable_smul',
    _root_.MeasureTheory.integrable_congr]
  · refine .of_forall ?_
    rintro ⟨r, hr : 0 < r⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · measurability
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_ioiPow_iff then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_ioiPow_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_ioiPow_iff ``Submission.MeasureTheory.integrable_ioiPow_iff

open _root_.MeasureTheory in
theorem integral_ioiPow (d : ℕ) (F : ℝ → G) :
    (∫ r : _root_.Set.Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in _root_.Set.Ioi (0 : ℝ), r ^ d • F r := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_subtype_coe.pow_const d).ennreal_ofReal)
      (by filter_upwards with r; exact ENNReal.ofReal_lt_top)]
  calc
    (∫ r : _root_.Set.Ioi (0 : ℝ),
        (ENNReal.ofReal (r.1 ^ d)).toReal • F r.1
          ∂Measure.comap Subtype.val _root_.MeasureTheory.MeasureSpace.volume) =
        ∫ r : _root_.Set.Ioi (0 : ℝ), r.1 ^ d • F r.1
          ∂Measure.comap Subtype.val volume := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with r
      rw [ENNReal.toReal_ofReal (pow_nonneg r.2.le d)]
    _ = ∫ r in _root_.Set.Ioi (0 : ℝ), r ^ d • F r :=
      _root_.MeasureTheory.integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ d • F r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_ioiPow then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_ioiPow"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_ioiPow ``Submission.MeasureTheory.integral_ioiPow

open _root_.MeasureTheory in
theorem integral_ioiPow_set (d : ℕ) (S : Set ℝ) (hS : MeasurableSet S)
    (hS0 : S ⊆ _root_.Set.Ioi (0 : ℝ)) (F : ℝ → G) :
    (∫ r : _root_.Set.Ioi (0 : ℝ), S.indicator F r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in S, r ^ d • F r := by
  rw [integral_ioiPow d (S.indicator F)]
  calc
    (∫ r in _root_.Set.Ioi (0 : ℝ), r ^ d • S.indicator F r) =
        ∫ r in S, r ^ d • S.indicator F r := by
      apply _root_.MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hS0
      intro r hr
      rw [_root_.Set.indicator_of_notMem hr.2, smul_zero]
    _ = ∫ r in S, r ^ d • F r := by
      apply _root_.MeasureTheory.setIntegral_congr_fun hS
      intro r hr
      change r ^ d • S.indicator F r = r ^ d • F r
      rw [_root_.Set.indicator_of_mem hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_ioiPow_set then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_ioiPow_set"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_ioiPow_set ``Submission.MeasureTheory.integral_ioiPow_set

open _root_.MeasureTheory in
theorem integral_polar_prod (f : E → G) :
    ∫ x, f x ∂μ =
      ∫ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
        f (z.2.1 • z.1.1)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  calc
    ∫ x, f x ∂μ = ∫ x in ({0}ᶜ : Set E), f x ∂μ := by
      exact congrArg (fun ν : _root_.MeasureTheory.Measure E => ∫ x, f x ∂ν)
        (_root_.MeasureTheory.restrict_compl_singleton (μ := μ) 0).symm
    _ = ∫ x : ({0}ᶜ : Set E),
          f x ∂(μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
      rw [_root_.MeasureTheory.integral_subtype_comap isOpen_compl_singleton.measurableSet]
    _ = ∫ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
          f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [Φ, Homeomorph.symm_apply_apply] using
        (μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          Φ.measurableEmbedding
          (fun z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) =>
            f ((Φ.symm z : ({0}ᶜ : Set E)) : E)))
    _ = ∫ z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ),
          f (z.2.1 • z.1.1)
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_polar_prod then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_polar_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_polar_prod ``Submission.MeasureTheory.integral_polar_prod

omit [NormedSpace ℝ G] in
open _root_.MeasureTheory in
theorem integrable_polar_prod (f : E → G) (hf : _root_.MeasureTheory.Integrable f μ) :
    _root_.MeasureTheory.Integrable
      (fun z : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) => f (z.2.1 • z.1.1))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let Φ := homeomorphUnitSphereProd E
  let F : _root_.Metric.sphere (0 : E) 1 × _root_.Set.Ioi (0 : ℝ) → G :=
    fun z => f ((Φ.symm z : ({0}ᶜ : Set E)) : E)
  have hfres : _root_.MeasureTheory.Integrable f (μ.restrict ({0}ᶜ : Set E)) := by
    simpa only [_root_.MeasureTheory.restrict_compl_singleton] using hf
  have hfsub : _root_.MeasureTheory.Integrable
      (fun x : ({0}ᶜ : Set E) => f x)
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) := by
    change _root_.MeasureTheory.Integrable
      (f ∘ ((↑) : ({0}ᶜ : Set E) → E))
      (μ.comap ((↑) : ({0}ᶜ : Set E) → E))
    rw [← (MeasurableEmbedding.subtype_coe
      isOpen_compl_singleton.measurableSet).integrable_map_iff,
      map_comap_subtype_coe isOpen_compl_singleton.measurableSet]
    exact hfres
  have hF : _root_.MeasureTheory.Integrable F
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    apply (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      Φ.measurableEmbedding).mp
    apply hfsub.congr
    filter_upwards with x
    simp only [F, Φ, Function.comp_apply, Homeomorph.symm_apply_apply]
  simpa only [F, Φ, homeomorphUnitSphereProd_symm_apply_coe] using hF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_polar_prod then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_polar_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_polar_prod ``Submission.MeasureTheory.integrable_polar_prod

open _root_.MeasureTheory in
theorem integral_polar (f : E → G) (hf : _root_.MeasureTheory.Integrable f μ) :
    ∫ x, f x ∂μ =
      ∫ u : _root_.Metric.sphere (0 : E) 1,
        ∫ r : _root_.Set.Ioi (0 : ℝ), f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [integral_polar_prod μ f]
  exact MeasureTheory.integral_prod _ (integrable_polar_prod μ f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_polar then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_polar ``Submission.MeasureTheory.integral_polar

open _root_.MeasureTheory in
theorem setIntegral_polar (s : Set E) (hs : MeasurableSet s)
    (f : E → G) (hf : _root_.MeasureTheory.IntegrableOn f s μ) :
    (∫ x in s, f x ∂μ) =
      ∫ u : _root_.Metric.sphere (0 : E) 1,
        ∫ r : _root_.Set.Ioi (0 : ℝ), s.indicator f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [← _root_.MeasureTheory.integral_indicator hs]
  exact integral_polar μ (s.indicator f) (hf.integrable_indicator hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setIntegral_polar then
    throwError "Refusing to shadow existing declaration MeasureTheory.setIntegral_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setIntegral_polar ``Submission.MeasureTheory.setIntegral_polar

end Signed

open _root_.MeasureTheory in
theorem setLIntegral_polar (s : Set E) (hs : MeasurableSet s)
    (f : E → ℝ≥0∞) (hf : AEMeasurable f (μ.restrict s)) :
    (∫⁻ x in s, f x ∂μ) =
      ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ), s.indicator f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [← _root_.MeasureTheory.lintegral_indicator hs]
  exact lintegral_polar μ (s.indicator f) ((aemeasurable_indicator_iff hs).mpr hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setLIntegral_polar then
    throwError "Refusing to shadow existing declaration MeasureTheory.setLIntegral_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setLIntegral_polar ``Submission.MeasureTheory.setLIntegral_polar

open _root_.MeasureTheory in
theorem setLIntegral_inter_ball_polar (s : Set E) (hs : MeasurableSet s)
    (R : ℝ) (f : E → ℝ≥0∞)
    (hf : AEMeasurable f (μ.restrict (s ∩ _root_.Metric.ball (0 : E) R))) :
    (∫⁻ x in s ∩ _root_.Metric.ball (0 : E) R, f x ∂μ) =
      ∫⁻ u : _root_.Metric.sphere (0 : E) 1,
        ∫⁻ r : _root_.Set.Ioi (0 : ℝ) in {r : _root_.Set.Ioi (0 : ℝ) | r.1 < R},
          s.indicator f (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂μ.toSphere := by
  rw [setLIntegral_polar μ (s ∩ _root_.Metric.ball (0 : E) R) (hs.inter measurableSet_ball) f hf]
  apply _root_.MeasureTheory.lintegral_congr
  intro u
  rw [← _root_.MeasureTheory.lintegral_indicator (measurableSet_lt measurable_subtype_coe measurable_const)]
  apply _root_.MeasureTheory.lintegral_congr
  intro r
  have hu : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hball : r.1 • u.1 ∈ _root_.Metric.ball (0 : E) R ↔ r.1 < R := by
    rw [_root_.Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg r.2.le, hu, mul_one]
  by_cases hsx : r.1 • u.1 ∈ s <;> by_cases hr : r.1 < R <;>
    simp [hsx, hball, hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setLIntegral_inter_ball_polar then
    throwError "Refusing to shadow existing declaration MeasureTheory.setLIntegral_inter_ball_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setLIntegral_inter_ball_polar ``Submission.MeasureTheory.setLIntegral_inter_ball_polar

end MeasureTheory

end
