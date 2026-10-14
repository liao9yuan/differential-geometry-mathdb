import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.Frozen
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Localization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real _root_.Set _root_.Filter
open scoped _root_.NNReal _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open _root_.Submission.DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def parabolicLaplacian (u : Real → V → F) : ParabolicPoint V → F :=
  fun p ↦ lapEval (hessianCurryEquiv V F (parabolicSpatialJet 2 u p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [CompleteSpace F] in
theorem parabolicLaplacian_add
    (u v : Real → V → F) (p : ParabolicPoint V)
    (hu : ContDiffAt Real 2 (u p.time) p.space)
    (hv : ContDiffAt Real 2 (v p.time) p.space) :
    parabolicLaplacian (fun t x ↦ u t x + v t x) p =
      parabolicLaplacian u p + parabolicLaplacian v p := by
  unfold parabolicLaplacian
  rw [parabolicSpatialJet_add 2 u v p hu hv, map_add, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian_add ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.parabolicLaplacian_add

omit [CompleteSpace F] in
theorem heatD3Convolution_int_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun y : V => heatD3 t h v w y • u (x - y)) := by
  refine ((heatD3Maj_int (V := V) ht).const_mul
    (‖h‖ * ‖v‖ * ‖w‖ * ‖u‖)).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable <| by
      unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
      fun_prop)
  · filter_upwards with y
    rw [norm_smul]
    calc
      ‖heatD3 t h v w y‖ * ‖u (x - y)‖ ≤
          (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t y) * ‖u‖ := by
        exact mul_le_mul (heatD3_bound ht h v w y)
          (u.norm_coe_le_norm (x - y)) (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
              (norm_nonneg w))
            (heatD3Maj_nonneg ht y))
      _ = (‖h‖ * ‖v‖ * ‖w‖ * ‖u‖) * heatD3Maj t y := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_int_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_int_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_int_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_int_of_bounded

omit [CompleteSpace F] in
theorem heatD3Convolution_norm_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD3Convolution t h v w u x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  unfold heatD3Convolution
  calc
    ‖∫ y : V, heatD3 t h v w y • u (x - y)‖ ≤
        ∫ y : V, ‖heatD3 t h v w y‖ * ‖u‖ := by
      exact _root_.MeasureTheory.norm_integral_le_of_norm_le
        ((heatD3_int (V := V) ht h v w).norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left
            (u.norm_coe_le_norm (x - y)) (norm_nonneg _))
    _ = (∫ y : V, ‖heatD3 t h v w y‖) * ‖u‖ := by
      rw [_root_.MeasureTheory.integral_mul_const]
    _ ≤ (‖h‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖u‖ := by
      gcongr
      exact integral_norm_D3 ht h v w
    _ = ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_norm_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_norm_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_norm_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_norm_of_bounded

omit [CompleteSpace F] in
theorem heatD3_path_integrable_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    _root_.MeasureTheory.Integrable
      (fun z : Real × V ↦
        (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2))
      ((volume.restrict (_root_.Set.Ioc 0 1)).prod _root_.MeasureTheory.MeasureSpace.volume) := by
  let μ : _root_.MeasureTheory.Measure Real := volume.restrict (_root_.Set.Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  let A : Real := ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖
  let C : Real := A * (t⁻¹ * (heatScale t)⁻¹ * heatC3 V)
  have hGmeas : _root_.MeasureTheory.AEStronglyMeasurable G (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) := by
    apply Continuous.aestronglyMeasurable
    unfold G heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hslice_int : ∀ s : Real, _root_.MeasureTheory.Integrable (fun y : V ↦ G (s, y)) := by
    intro s
    have hs := (heatD3Convolution_int_of_bounded ht h v w u (x - s • h)).neg
      |>.comp_add_right (s • (-h))
    refine hs.congr (Eventually.of_forall fun y ↦ ?_)
    have hfarg : x - s • h - (y + s • (-h)) = x - y := by
      rw [smul_neg]
      abel
    simp only [G, hfarg, Pi.neg_apply, neg_smul]
  have hslice_bound : ∀ s : Real, (∫ y : V, ‖G (s, y)‖) ≤ C := by
    intro s
    have hmajor : _root_.MeasureTheory.Integrable
        (fun y : V ↦ A * heatD3Maj t (y + s • (-h))) :=
      ((heatD3Maj_int (V := V) ht).comp_add_right (s • (-h))).const_mul A
    have hpoint : ∀ y : V,
        ‖G (s, y)‖ ≤ A * heatD3Maj t (y + s • (-h)) := by
      intro y
      rw [norm_smul]
      calc
        ‖-heatD3 t h v w (y + s • (-h))‖ * ‖u (x - y)‖ ≤
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t (y + s • (-h))) * ‖u‖ := by
          rw [norm_neg]
          exact mul_le_mul (heatD3_bound ht h v w _)
            (u.norm_coe_le_norm (x - y)) (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
                (norm_nonneg w))
              (heatD3Maj_nonneg ht _))
        _ = A * heatD3Maj t (y + s • (-h)) := by
          unfold A
          ring
    calc
      (∫ y : V, ‖G (s, y)‖) ≤
          ∫ y : V, A * heatD3Maj t (y + s • (-h)) :=
        _root_.MeasureTheory.integral_mono (hslice_int s).norm hmajor hpoint
      _ = A * ∫ y : V, heatD3Maj t (y + s • (-h)) := by
        rw [_root_.MeasureTheory.integral_const_mul]
      _ = A * ∫ y : V, heatD3Maj t y := by
        rw [MeasureTheory.integral_add_right_eq_self]
      _ = C := by
        rw [integral_heatD3Maj ht]
  have hCnonneg : 0 ≤ C := by
    unfold C A
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
          (norm_nonneg w))
        (norm_nonneg u))
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr ht.le)
          (inv_nonneg.mpr (heatScale_pos ht).le))
        (heatC3_nonneg (V := V)))
  have houter : _root_.MeasureTheory.Integrable (fun s : Real ↦ ∫ y : V, ‖G (s, y)‖) μ := by
    have hconst : _root_.MeasureTheory.Integrable (fun _ : Real ↦ C) μ := by
      change _root_.MeasureTheory.IntegrableOn (fun _ : Real ↦ C) (_root_.Set.Ioc 0 1) _root_.MeasureTheory.MeasureSpace.volume
      exact _root_.MeasureTheory.integrableOn_const (C := C) measure_Ioc_lt_top.ne
    refine hconst.mono hGmeas.norm.integral_prod_right' ?_
    filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_nonneg (_root_.MeasureTheory.integral_nonneg fun y ↦ norm_nonneg (G (s, y))),
      Real.norm_eq_abs, abs_of_nonneg hCnonneg]
    exact hslice_bound s
  exact (_root_.MeasureTheory.integrable_prod_iff hGmeas).2
    ⟨Eventually.of_forall hslice_int, houter⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3_path_integrable_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3_path_integrable_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3_path_integrable_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3_path_integrable_of_bounded

omit [CompleteSpace F] in
theorem heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x =
      ∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • u (x - z) := by
  have hzero := supKernel_int (heatD2_int ht v w) u x
  have hone0 := supKernel_int (heatD2_int ht v w) u (x - h)
  change _root_.MeasureTheory.Integrable (fun z : V ↦ heatD2 t v w z • u (x - z)) at hzero
  change _root_.MeasureTheory.Integrable (fun z : V ↦ heatD2 t v w z • u (x - h - z)) at hone0
  have hone : _root_.MeasureTheory.Integrable
      (fun z : V ↦ heatD2 t v w (z - h) • u (x - z)) := by
    have htranslated := hone0.comp_add_right (-h)
    refine htranslated.congr (Filter.Eventually.of_forall fun z ↦ ?_)
    have hk : z + -h = z - h := by abel
    have hfarg : x - h - (z - h) = x - z := by abel
    simp only [hk, hfarg]
  rw [heatD2Convolution_translate_kernel]
  unfold heatD2Convolution
  rw [← _root_.MeasureTheory.integral_sub hone hzero]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [sub_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded

theorem heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x =
      ∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h) := by
  let μ : _root_.MeasureTheory.Measure Real := volume.restrict (_root_.Set.Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  have hGint : _root_.MeasureTheory.Integrable G (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) := by
    simpa only [G, μ] using heatD3_path_integrable_of_bounded ht h v w u x
  rw [heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded ht]
  calc
    (∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • u (x - z)) =
        ∫ z : V, (∫ s : Real in 0..1,
          -heatD3 t h v w (z + s • (-h))) • u (x - z) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [heatD2_space_sub_eq_integral_heatD3]
    _ = ∫ z : V, ∫ s : Real in 0..1,
        (-heatD3 t h v w (z + s • (-h))) • u (x - z) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with z
      exact (intervalIntegral.integral_smul_const
        (fun s : Real ↦ -heatD3 t h v w (z + s • (-h))) (u (x - z))).symm
    _ = ∫ z : V, (∫ s : Real, G (s, z) ∂μ) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ s : Real, (∫ z : V, G (s, z)) ∂μ := by
      have huncurry : _root_.MeasureTheory.Integrable
          (Function.uncurry (fun s : Real ↦ fun z : V ↦ G (s, z)))
          (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) := by
        change _root_.MeasureTheory.Integrable G (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V))
        exact hGint
      have hswap :
          (∫ s : Real, (∫ z : V, G (s, z)) ∂μ) =
            ∫ z : V, (∫ s : Real, G (s, z) ∂μ) :=
        _root_.MeasureTheory.integral_integral_swap huncurry
      exact hswap.symm
    _ = ∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with s
      simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w u x s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded

omit [CompleteSpace F] in
theorem heatD3Convolution_path_intervalIntegrable_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    IntervalIntegrable
      (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h)) _root_.MeasureTheory.MeasureSpace.volume 0 1 := by
  let μ : _root_.MeasureTheory.Measure Real := volume.restrict (_root_.Set.Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  have hGint : _root_.MeasureTheory.Integrable G (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure V)) := by
    simpa only [G, μ] using heatD3_path_integrable_of_bounded ht h v w u x
  have hneg : _root_.MeasureTheory.Integrable
      (fun s : Real ↦ -heatD3Convolution t h v w u (x - s • h)) μ := by
    refine hGint.integral_prod_left.congr (Eventually.of_forall fun s ↦ ?_)
    simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w u x s
  have hconv : _root_.MeasureTheory.Integrable
      (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h)) μ := by
    refine hneg.neg.congr (Eventually.of_forall fun s ↦ ?_)
    simp
  rw [intervalIntegrable_iff,
    _root_.Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)]
  change _root_.MeasureTheory.Integrable
    (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h))
    (volume.restrict (_root_.Set.Ioc 0 1)) at hconv
  exact hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_path_intervalIntegrable_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_path_intervalIntegrable_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_path_intervalIntegrable_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD3Convolution_path_intervalIntegrable_of_bounded

theorem heatD2Convolution_space_sub_norm_le_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  let M : Real :=
    ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V
  have hpath := heatD3Convolution_path_intervalIntegrable_of_bounded ht h v w u x
  have hconst : IntervalIntegrable (fun _ : Real ↦ M) _root_.MeasureTheory.MeasureSpace.volume 0 1 :=
    (continuous_const : Continuous (fun _ : Real ↦ M)).intervalIntegrable
      (μ := _root_.MeasureTheory.MeasureSpace.volume) 0 1
  rw [heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded ht]
  calc
    ‖∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h)‖ ≤
        ∫ s : Real in 0..1, ‖-heatD3Convolution t h v w u (x - s • h)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _s : Real in 0..1, M := by
      refine intervalIntegral.integral_mono (by norm_num) hpath.neg.norm hconst ?_
      intro s
      dsimp only
      rw [norm_neg]
      simpa only [M] using heatD3Convolution_norm_of_bounded ht h v w u (x - s • h)
    _ = M := by simp
    _ = ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_norm_le_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_norm_le_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_norm_le_of_bounded ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_space_sub_norm_le_of_bounded

def heatD2SupHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  _root_.Max.max
    (2 * Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖))
    (Real.toNNReal (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2SupHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2SupHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2SupHolderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2SupHolderConst

theorem heatD2Convolution_holder_of_norm_le_one
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v w : V)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (u : BoundedContinuousFunction V F) :
    HolderWith (heatD2SupHolderConst (V := V) t u) alpha
      (fun x ↦ heatD2Convolution t v w u x) := by
  let B₀ : NNReal := Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)
  let B₁ : NNReal :=
    Real.toNNReal (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V)
  have hnorm : ∀ x : V, ‖heatD2Convolution t v w u x‖ ≤ B₀ := by
    intro x
    have hraw := heatD2Sup_norm ht v w u x
    have hunit :
        (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ ≤
          t⁻¹ * heatC2 V * ‖u‖ := by
      have hvw : ‖v‖ * ‖w‖ ≤ 1 := by
        exact (mul_le_mul hv hw (norm_nonneg w) (by positivity)).trans_eq (one_mul 1)
      have hcoef : 0 ≤ t⁻¹ * heatC2 V * ‖u‖ := by
        exact mul_nonneg
          (mul_nonneg (inv_nonneg.mpr ht.le) (heatC2_nonneg (V := V)))
          (norm_nonneg u)
      calc
        (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ =
            (‖v‖ * ‖w‖) * (t⁻¹ * heatC2 V * ‖u‖) := by ring
        _ ≤ 1 * (t⁻¹ * heatC2 V * ‖u‖) :=
          mul_le_mul_of_nonneg_right hvw hcoef
        _ = t⁻¹ * heatC2 V * ‖u‖ := one_mul _
    have hraw' : ‖heatD2Convolution t v w u x‖ ≤
        t⁻¹ * heatC2 V * ‖u‖ := by
      simpa only [heatD2Convolution, heatD2Sup, supKernel] using hraw.trans hunit
    exact hraw'.trans (Real.le_coe_toNNReal _)
  have hzero : HolderWith (2 * B₀) 0
      (fun x ↦ heatD2Convolution t v w u x) :=
    holderWith_zero_of_norm_le hnorm
  have hlip : LipschitzWith B₁
      (fun x ↦ heatD2Convolution t v w u x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hraw := heatD2Convolution_space_sub_norm_le_of_bounded ht (y - x) v w u y
    have hxy : y - (y - x) = x := by abel
    rw [hxy] at hraw
    have hunit :
        ‖y - x‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V ≤
          (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖x - y‖ := by
      rw [norm_sub_rev]
      have hvw : ‖v‖ * ‖w‖ ≤ 1 := by
        exact (mul_le_mul hv hw (norm_nonneg w) (by positivity)).trans_eq (one_mul 1)
      have hcoef : 0 ≤
          ‖x - y‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (norm_nonneg _) (norm_nonneg u))
              (inv_nonneg.mpr ht.le))
            (inv_nonneg.mpr (heatScale_pos ht).le))
          (heatC3_nonneg (V := V))
      calc
        ‖x - y‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V =
            (‖v‖ * ‖w‖) *
              (‖x - y‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) := by
          ring
        _ ≤ 1 * (‖x - y‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V) :=
          mul_le_mul_of_nonneg_right hvw hcoef
        _ = (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖x - y‖ := by
          ring
    exact hraw.trans (hunit.trans (by
      unfold B₁
      gcongr
      exact Real.le_coe_toNNReal _))
  have hone : HolderWith B₁ 1
      (fun x ↦ heatD2Convolution t v w u x) := hlip.holderWith
  have hinterp := hzero.of_le_of_le hone bot_le halpha
  simpa only [heatD2SupHolderConst, B₀, B₁] using hinterp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_holder_of_norm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_holder_of_norm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_holder_of_norm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Convolution_holder_of_norm_le_one

def heatSupSpatialJetConst (t : Real)
    (u : BoundedContinuousFunction V F) : Nat → NNReal
  | 0 => ⟨‖u‖, norm_nonneg u⟩
  | 1 => Real.toNNReal ((heatScale t)⁻¹ * heatC1 V * ‖u‖)
  | _ => Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSpatialJetConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSpatialJetConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSpatialJetConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSpatialJetConst

def heatSupHessianHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ∑ _β : Fin 2 → Fin (Module.finrank Real V),
    heatD2SupHolderConst (V := V) t u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianHolderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianHolderConst

def heatSupHessianMapHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ∑ _i : Fin (Module.finrank Real V),
    ∑ _j : Fin (Module.finrank Real V),
      heatD2SupHolderConst (V := V) t u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianMapHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianMapHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianMapHolderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessianMapHolderConst

def heatSupSchauderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  (∑ j ∈ Finset.range 3, heatSupSpatialJetConst (V := V) t u j) +
    heatSupHessianHolderConst (V := V) t u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSchauderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSchauderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSchauderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupSchauderConst

omit [CompleteSpace F] in
theorem heatSup_spatialJet_norm_le
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F)
    {j : Nat} (hj : j ≤ 2) (x : V) :
    ‖iteratedFDeriv Real j (fun z : V ↦ heatSup t u z) x‖ ≤
      heatSupSpatialJetConst (V := V) t u j := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  obtain rfl | rfl | rfl := hcases
  · rw [norm_iteratedFDeriv_zero]
    change ‖heatSup t u x‖ ≤ ‖u‖
    exact heatSup_contract ht u x
  · rw [norm_iteratedFDeriv_one, (heatSup_hasFDerivAt ht u x).fderiv]
    change ‖heatSupGradient t u x‖ ≤
      Real.toNNReal ((heatScale t)⁻¹ * heatC1 V * ‖u‖)
    have hnonneg : 0 ≤ (heatScale t)⁻¹ * heatC1 V * ‖u‖ :=
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)
          (heatC1_nonneg (V := V)))
        (norm_nonneg u)
    rw [Real.coe_toNNReal _ hnonneg]
    refine ContinuousLinearMap.opNorm_le_bound (𝕜 := Real) (𝕜₂ := Real)
      (heatSupGradient t u x) ?_ ?_
    · exact hnonneg
    · intro v
      rw [heatSupGradient_apply ht]
      have hraw := heatD1Sup_norm ht v u x
      exact hraw.trans_eq (by ring)
  · refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
    · change 0 ≤ Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)
      positivity
    · intro m
      rw [heatSup_iteratedFDeriv_two_apply ht, heatSupHessian_apply ht]
      have hraw := heatD2Sup_norm ht (m 1) (m 0) u x
      have hraw' : ‖heatD2Convolution t (m 1) (m 0) u x‖ ≤
          (‖m 1‖ * ‖m 0‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
        simpa only [heatD2Convolution, heatD2Sup, supKernel] using hraw
      have hnonneg : 0 ≤ t⁻¹ * heatC2 V * ‖u‖ :=
        mul_nonneg
          (mul_nonneg (inv_nonneg.mpr ht.le) (heatC2_nonneg (V := V)))
          (norm_nonneg u)
      calc
        ‖heatD2Convolution t (m 1) (m 0) u x‖ ≤
            (‖m 1‖ * ‖m 0‖ * t⁻¹ * heatC2 V) * ‖u‖ := hraw'
        _ = (t⁻¹ * heatC2 V * ‖u‖) * ∏ i, ‖m i‖ := by
          rw [Fin.prod_univ_two]
          ring
        _ = (heatSupSpatialJetConst (V := V) t u 2 : Real) *
            ∏ i, ‖m i‖ := by
          change (t⁻¹ * heatC2 V * ‖u‖) * ∏ i, ‖m i‖ =
            (Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖) : Real) * ∏ i, ‖m i‖
          rw [Real.coe_toNNReal _ hnonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_spatialJet_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_spatialJet_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_spatialJet_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_spatialJet_norm_le

theorem heatSup_iteratedFDeriv_two_holder
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    HolderWith (heatSupHessianHolderConst (V := V) t u) alpha
      (iteratedFDeriv Real 2 (fun z : V ↦ heatSup t u z)) := by
  apply holderWith_continuousMultilinearMap_of_stdOrthonormalBasis
    (C := fun _ ↦ heatD2SupHolderConst (V := V) t u)
  intro β
  have h := heatD2Convolution_holder_of_norm_le_one halpha ht
    ((stdOrthonormalBasis Real V) (β 1))
    ((stdOrthonormalBasis Real V) (β 0))
    (by simp) (by simp) u
  simpa only [heatSupHessianHolderConst,
    heatSup_iteratedFDeriv_two_apply ht, heatSupHessian_apply ht] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_iteratedFDeriv_two_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_iteratedFDeriv_two_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_iteratedFDeriv_two_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_iteratedFDeriv_two_holder

theorem heatSupHessian_holder
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    HolderWith (heatSupHessianMapHolderConst (V := V) t u) alpha
      (heatSupHessian t u) := by
  unfold heatSupHessianMapHolderConst
  apply holderWith_continuousLinearMap_two_of_stdOrthonormalBasis
    (A := heatSupHessian t u)
    (C := fun _ _ ↦ heatD2SupHolderConst (V := V) t u)
  intro i j
  have h := heatD2Convolution_holder_of_norm_le_one halpha ht
    ((stdOrthonormalBasis Real V) j)
    ((stdOrthonormalBasis Real V) i)
    (by simp) (by simp) u
  simpa only [heatSupHessian_apply ht] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessian_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessian_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessian_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupHessian_holder

theorem heatSup_contDiff_two
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    ContDiff Real 2 (fun x : V ↦ heatSup t u x) := by
  have hhess : Continuous (heatSupHessian t u) :=
    (heatSupHessian_holder (alpha := 1) le_rfl ht u).continuous (by norm_num)
  have hgrad : ContDiff Real 1 (heatSupGradient t u) :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨heatSupHessian t u, hhess, heatSupGradient_hasFDerivAt ht u⟩
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨heatSupGradient t u, hgrad, heatSup_hasFDerivAt ht u⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contDiff_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contDiff_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contDiff_two ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contDiff_two

theorem heatSup_schauder_estimate
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    eContDiffHolderGaugeOn 2 alpha Set.univ
      (fun x : V ↦ heatSup t u x) ≤
      heatSupSchauderConst (V := V) t u := by
  have h := eContDiffHolderGaugeOn_le
    (heatSupSpatialJetConst (V := V) t u)
    (heatSupHessianHolderConst (V := V) t u)
    (fun j hj x _ ↦ heatSup_spatialJet_norm_le ht u hj x)
    ((heatSup_iteratedFDeriv_two_holder halpha ht u).holderOnWith
      Set.univ).holderWith
  simpa only [heatSupSchauderConst, ENNReal.coe_add,
    ENNReal.ofNNReal_finsetSum] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_schauder_estimate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_schauder_estimate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_schauder_estimate ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_schauder_estimate

omit [CompleteSpace F] in
theorem heatScaled_integrable (t : Real)
    (u : BoundedContinuousFunction V F) (x : V) :
    _root_.MeasureTheory.Integrable (fun z : V ↦
      baseHeat z • u (x - heatScale t • z)) := by
  refine ((baseHeat_int (V := V)).norm.mul_const ‖u‖).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseHeat heatScale
    fun_prop
  · filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseHeat_nonneg z)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _)
        (baseHeat_nonneg z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_integrable

omit [CompleteSpace F] in
theorem heatScaled_space_sub_norm_le_of_holder
    {alpha K : NNReal} (t : Real)
    (u : BoundedContinuousFunction V F) (hu : HolderWith K alpha u)
    (x y : V) :
    ‖heatScaled t u x - heatScaled t u y‖ ≤
      (K : Real) * _root_.Dist.dist x y ^ (alpha : Real) := by
  have heq : heatScaled t u x - heatScaled t u y =
      ∫ z : V, baseHeat z •
        (u (x - heatScale t • z) - u (y - heatScale t • z)) := by
    unfold heatScaled
    rw [← _root_.MeasureTheory.integral_sub (heatScaled_integrable t u x)
      (heatScaled_integrable t u y)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [smul_sub]
  rw [heq]
  have hmajor : _root_.MeasureTheory.Integrable
      (fun z : V ↦ ((K : Real) * _root_.Dist.dist x y ^ (alpha : Real)) * baseHeat z) :=
    (baseHeat_int (V := V)).const_mul
      ((K : Real) * _root_.Dist.dist x y ^ (alpha : Real))
  calc
    ‖∫ z : V, baseHeat z •
        (u (x - heatScale t • z) - u (y - heatScale t • z))‖ ≤
        ∫ z : V,
          ((K : Real) * _root_.Dist.dist x y ^ (alpha : Real)) * baseHeat z := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards with z
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (baseHeat_nonneg z)]
      have hdist : _root_.Dist.dist (x - heatScale t • z)
          (y - heatScale t • z) = _root_.Dist.dist x y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      calc
        baseHeat z *
            ‖u (x - heatScale t • z) - u (y - heatScale t • z)‖ ≤
            baseHeat z *
              ((K : Real) * _root_.Dist.dist x y ^ (alpha : Real)) := by
          rw [← dist_eq_norm, ← hdist]
          exact mul_le_mul_of_nonneg_left
            (hu.dist_le _ _) (baseHeat_nonneg z)
        _ = ((K : Real) * _root_.Dist.dist x y ^ (alpha : Real)) * baseHeat z := by
          ring
    _ = (K : Real) * _root_.Dist.dist x y ^ (alpha : Real) := by
      rw [_root_.MeasureTheory.integral_const_mul, integral_baseHeat, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_space_sub_norm_le_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_space_sub_norm_le_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_space_sub_norm_le_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_space_sub_norm_le_of_holder

omit [CompleteSpace F] in
theorem heatScaled_time_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F) (hu : HolderWith K alpha u)
    (t s : Real) (x : V) :
    ‖heatScaled t u x - heatScaled s u x‖ ≤
      (K : Real) * |heatScale t - heatScale s| ^ (alpha : Real) *
        heatC0Holder (V := V) alpha := by
  have heq : heatScaled t u x - heatScaled s u x =
      ∫ z : V, baseHeat z •
        (u (x - heatScale t • z) - u (x - heatScale s • z)) := by
    unfold heatScaled
    rw [← _root_.MeasureTheory.integral_sub (heatScaled_integrable t u x)
      (heatScaled_integrable s u x)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [smul_sub]
  rw [heq]
  let A : Real := (K : Real) *
    |heatScale t - heatScale s| ^ (alpha : Real)
  have hA : 0 ≤ A := mul_nonneg K.coe_nonneg
    (Real.rpow_nonneg (abs_nonneg _) _)
  have hmajor : _root_.MeasureTheory.Integrable
      (fun z : V ↦ A * baseHeatHolder alpha z) :=
    (baseHeatHolder_int (V := V) halpha).const_mul A
  calc
    ‖∫ z : V, baseHeat z •
        (u (x - heatScale t • z) - u (x - heatScale s • z))‖ ≤
        ∫ z : V, A * baseHeatHolder alpha z := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards with z
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (baseHeat_nonneg z)]
      have hdist : _root_.Dist.dist (x - heatScale t • z)
          (x - heatScale s • z) =
          |heatScale t - heatScale s| * ‖z‖ := by
        rw [dist_eq_norm]
        have heq' :
            (x - heatScale t • z) - (x - heatScale s • z) =
              (heatScale s - heatScale t) • z := by
          module
        rw [heq', norm_smul, Real.norm_eq_abs, abs_sub_comm]
      calc
        baseHeat z *
            ‖u (x - heatScale t • z) - u (x - heatScale s • z)‖ ≤
            baseHeat z * ((K : Real) *
              (|heatScale t - heatScale s| * ‖z‖) ^
                (alpha : Real)) := by
          rw [← dist_eq_norm, ← hdist]
          exact mul_le_mul_of_nonneg_left
            (hu.dist_le _ _) (baseHeat_nonneg z)
        _ = A * baseHeatHolder alpha z := by
          rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
          unfold A baseHeatHolder
          ring
    _ = A * heatC0Holder (V := V) alpha := by
      rw [_root_.MeasureTheory.integral_const_mul]
      rfl
    _ = (K : Real) * |heatScale t - heatScale s| ^ (alpha : Real) *
        heatC0Holder (V := V) alpha := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_time_sub_norm_le_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_time_sub_norm_le_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_time_sub_norm_le_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_time_sub_norm_le_of_holder

theorem abs_heatScale_sub_heatScale_le
    {t s : Real} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |heatScale t - heatScale s| ≤ Real.sqrt |t - s| := by
  wlog hst : s ≤ t generalizing t s
  · rw [abs_sub_comm (heatScale t), abs_sub_comm t]
    exact this hs ht (le_of_not_ge hst)
  have hsqrt : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
  have hleft : 0 ≤ Real.sqrt t - Real.sqrt s := sub_nonneg.mpr hsqrt
  have hright : 0 ≤ Real.sqrt (t - s) := Real.sqrt_nonneg _
  have hmul : (Real.sqrt s) ^ 2 ≤ Real.sqrt s * Real.sqrt t := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg s)
  have hsquare : (Real.sqrt t - Real.sqrt s) ^ 2 ≤
      (Real.sqrt (t - s)) ^ 2 := by
    calc
      (Real.sqrt t - Real.sqrt s) ^ 2 =
          (Real.sqrt t) ^ 2 + (Real.sqrt s) ^ 2 -
            2 * (Real.sqrt s * Real.sqrt t) := by ring
      _ =
          t + s - 2 * (Real.sqrt s * Real.sqrt t) := by
        rw [Real.sq_sqrt ht, Real.sq_sqrt hs]
      _ ≤ t - s := by
        rw [Real.sq_sqrt hs] at hmul
        nlinarith
      _ = (Real.sqrt (t - s)) ^ 2 := by
        rw [Real.sq_sqrt (sub_nonneg.mpr hst)]
  unfold heatScale
  rw [abs_of_nonneg (sub_nonneg.mpr hsqrt),
    abs_of_nonneg (sub_nonneg.mpr hst)]
  exact (sq_le_sq₀ hleft hright).mp hsquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.abs_heatScale_sub_heatScale_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.abs_heatScale_sub_heatScale_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.abs_heatScale_sub_heatScale_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.abs_heatScale_sub_heatScale_le

def heatScaledParabolicHolderConst
    (alpha K : NNReal) : NNReal :=
  K * (1 + Real.toNNReal (heatC0Holder (V := V) alpha))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaledParabolicHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaledParabolicHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaledParabolicHolderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaledParabolicHolderConst

omit [CompleteSpace F] in
theorem heatScaled_parabolic_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F) (hu : HolderWith K alpha u)
    {t s : Real} (ht : 0 ≤ t) (hs : 0 ≤ s) (x y : V) :
    ‖heatScaled t u x - heatScaled s u y‖ ≤
      (heatScaledParabolicHolderConst (V := V) alpha K : Real) *
        dist (parabolicPoint t x) (parabolicPoint s y) ^ (alpha : Real) := by
  let D : Real := _root_.Dist.dist (parabolicPoint t x) (parabolicPoint s y)
  have hspace : _root_.Dist.dist x y ≤ D := by
    unfold D
    rw [dist_parabolicPoint]
    exact le_max_right _ _
  have htime : |heatScale t - heatScale s| ≤ D := by
    refine (abs_heatScale_sub_heatScale_le ht hs).trans ?_
    unfold D
    rw [dist_parabolicPoint, Real.sqrt_eq_rpow]
    exact le_max_left _ _
  have hspacePow : _root_.Dist.dist x y ^ (alpha : Real) ≤ D ^ (alpha : Real) :=
    Real.rpow_le_rpow dist_nonneg hspace alpha.coe_nonneg
  have htimePow : |heatScale t - heatScale s| ^ (alpha : Real) ≤
      D ^ (alpha : Real) :=
    Real.rpow_le_rpow (abs_nonneg _) htime alpha.coe_nonneg
  have hC0 : 0 ≤ heatC0Holder (V := V) alpha :=
    heatC0Holder_nonneg alpha
  calc
    ‖heatScaled t u x - heatScaled s u y‖ ≤
        ‖heatScaled t u x - heatScaled t u y‖ +
          ‖heatScaled t u y - heatScaled s u y‖ := by
      have hsplit : heatScaled t u x - heatScaled s u y =
          (heatScaled t u x - heatScaled t u y) +
            (heatScaled t u y - heatScaled s u y) := by abel
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ (K : Real) * _root_.Dist.dist x y ^ (alpha : Real) +
        (K : Real) * |heatScale t - heatScale s| ^ (alpha : Real) *
          heatC0Holder (V := V) alpha :=
      add_le_add
        (heatScaled_space_sub_norm_le_of_holder t u hu x y)
        (heatScaled_time_sub_norm_le_of_holder halpha u hu t s y)
    _ ≤ (K : Real) * D ^ (alpha : Real) +
        (K : Real) * D ^ (alpha : Real) *
          heatC0Holder (V := V) alpha := by
      gcongr
    _ = (heatScaledParabolicHolderConst (V := V) alpha K : Real) *
        D ^ (alpha : Real) := by
      unfold heatScaledParabolicHolderConst
      push_cast
      rw [Real.coe_toNNReal _ hC0]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_sub_norm_le_of_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_sub_norm_le_of_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_sub_norm_le_of_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_sub_norm_le_of_holder

omit [CompleteSpace F] in
theorem heatScaled_parabolic_holder
    {alpha K : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F) (hu : HolderWith K alpha u) :
    HolderWith (heatScaledParabolicHolderConst (V := V) alpha K) alpha
      ((parabolicCylinder (_root_.Set.Ici (0 : Real)) Set.univ).domRestrict
        (fun p ↦ heatScaled p.time u p.space)) := by
  intro p q
  rw [edist_dist, edist_dist]
  have hreal := heatScaled_parabolic_sub_norm_le_of_holder halpha u hu
    p.2.1 q.2.1 p.1.space q.1.space
  rw [← dist_eq_norm] at hreal
  refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity :
      0 ≤ (heatScaledParabolicHolderConst (V := V) alpha K : Real)),
    ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg,
    Subtype.dist_eq, parabolicPoint_time_space,
    parabolicPoint_time_space]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatScaled_parabolic_holder

omit [CompleteSpace F] in
theorem heatSup_parabolic_holder
    {alpha K : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F) (hu : HolderWith K alpha u) :
    HolderWith (heatScaledParabolicHolderConst (V := V) alpha K) alpha
      ((parabolicCylinder (_root_.Set.Ioi (0 : Real)) Set.univ).domRestrict
        (fun p ↦ heatSup p.time u p.space)) := by
  have hscaled := heatScaled_parabolic_holder (V := V) halpha u hu
  rw [HolderWith.restrict_iff] at hscaled ⊢
  intro p hp q hq
  have hp_pos : 0 < p.time := by simpa only [_root_.Set.mem_Ioi] using hp.1
  have hq_pos : 0 < q.time := by simpa only [_root_.Set.mem_Ioi] using hq.1
  have hp0 : p.time ∈ _root_.Set.Ici (0 : Real) := by
    simpa only [_root_.Set.mem_Ici] using hp_pos.le
  have hq0 : q.time ∈ _root_.Set.Ici (0 : Real) := by
    simpa only [_root_.Set.mem_Ici] using hq_pos.le
  have h := hscaled p ⟨hp0, hp.2⟩ q ⟨hq0, hq.2⟩
  change _root_.EDist.edist (heatSup p.time u p.space) (heatSup q.time u q.space) ≤ _
  rw [heatSup_scaled hp_pos u p.space,
    heatSup_scaled hq_pos u q.space]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_holder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_holder ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_holder

omit [CompleteSpace F] in
theorem heatSup_fderiv_eq
    {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    fderiv Real (fun y : V ↦ heatSup t u y) x = heatSup t du x := by
  have hscaled := heatScaled_space t u du hu x
  have hfun : (fun y : V ↦ heatSup t u y) =
      fun y : V ↦ heatScaled t u y := by
    funext y
    exact heatSup_scaled ht u y
  rw [hfun, hscaled.fderiv, ← heatSup_scaled ht du x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_fderiv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_fderiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_fderiv_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_fderiv_eq

omit [CompleteSpace F] in
theorem heatSup_hessianCurryEquiv_iteratedFDeriv_two
    {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x) (x : V) :
    hessianCurryEquiv V F
        (iteratedFDeriv Real 2 (fun y : V ↦ heatSup t u y) x) =
      heatSup t d2u x := by
  have hfd : fderiv Real (fun y : V ↦ heatSup t u y) =
      fun y : V ↦ heatSup t du y := by
    funext y
    exact heatSup_fderiv_eq ht u du hu y
  ext v w
  simp only [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
    continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_two_apply]
  rw [hfd, heatSup_fderiv_eq ht du d2u hdu x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_hessianCurryEquiv_iteratedFDeriv_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_hessianCurryEquiv_iteratedFDeriv_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_hessianCurryEquiv_iteratedFDeriv_two ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_hessianCurryEquiv_iteratedFDeriv_two

theorem heatSup_parabolicLaplacian_eq
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (p : ParabolicPoint V) (ht : 0 < p.time) :
    parabolicLaplacian (fun t x ↦ heatSup t u x) p =
      heatSup p.time (coreLap d2u) p.space := by
  unfold parabolicLaplacian parabolicSpatialJet
  rw [heatSup_hessianCurryEquiv_iteratedFDeriv_two ht u du d2u hu hdu]
  unfold heatSup supKernel
  rw [← (lapEval (V := V) (F := F)).integral_comp_comm
    (supKernel_int (heatKernel_int ht) d2u p.space)]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [map_smul, coreLap, BoundedContinuousFunction.coe_mk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicLaplacian_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicLaplacian_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicLaplacian_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicLaplacian_eq

omit [CompleteSpace F] in
theorem heatSup_parabolicTimeDerivative_eq
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (p : ParabolicPoint V) (ht : 0 < p.time) :
    parabolicTimeDerivative (fun t x ↦ heatSup t u x) p =
      heatSup p.time (coreLap d2u) p.space := by
  unfold parabolicTimeDerivative
  rw [(heatSup_time ht u du d2u hu hdu p.space).hasFDerivAt.fderiv]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq

theorem heatSup_parabolicTimeDerivative_eq_laplacian
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (p : ParabolicPoint V) (ht : 0 < p.time) :
    parabolicTimeDerivative (fun t x ↦ heatSup t u x) p =
      parabolicLaplacian (fun t x ↦ heatSup t u x) p := by
  rw [heatSup_parabolicTimeDerivative_eq u du d2u hu hdu p ht,
    heatSup_parabolicLaplacian_eq u du d2u hu hdu p ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq_laplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolicTimeDerivative_eq_laplacian

theorem heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (p : ParabolicPoint V) (ht : 0 < p.time)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ _root_.Set.Icc (0 : Real) p.time, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ _root_.Set.Icc (0 : Real) p.time, HolderWith K alpha (f s))
    (hmeas0 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSup (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time)))
    (hmeas1 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSupGradient (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time)))
    (hmeas2 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSupHessian (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time))) :
    parabolicLaplacian (fun t x ↦ heatDuhamel t f x) p =
      heatLapDuhamel p.time (fun s ↦ f s) p.space := by
  unfold parabolicLaplacian parabolicSpatialJet
  rw [heatDuhamel_hessianCurryEquiv_iteratedFDeriv_two
    halpha0 halpha1 ht f hbound hf hmeas0 hmeas1 hmeas2]
  rw [lapEval_apply]
  unfold heatLapDuhamel
  apply Finset.sum_congr rfl
  intro i _hi
  exact heatDuhamelHessian_apply halpha0 halpha1 ht f hbound hf hmeas1 hmeas2
    p.space ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel

theorem heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S : Real} (p : ParabolicPoint V) (hp : p.time ∈ _root_.Set.Ioo (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ _root_.Set.Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (_root_.Set.Icc (0 : Real) S) Set.univ).domRestrict
        (fun q ↦ f q.time q.space))) :
    parabolicTimeDerivative (fun t x ↦ heatDuhamel t f x) p =
      f p.time p.space + parabolicLaplacian (fun t x ↦ heatDuhamel t f x) p := by
  have htIoc : p.time ∈ _root_.Set.Ioc (0 : Real) S := ⟨hp.1, hp.2.le⟩
  have hf : ∀ r ∈ _root_.Set.Icc (0 : Real) S, HolderWith K alpha (f r) :=
    fun r hr ↦ holderWith_slice_of_parabolicCylinder
      (f := fun s x ↦ f s x) hsource hr
  have hsource' : HolderWith K alpha
      ((parabolicCylinder (_root_.Set.Ioc (0 : Real) S) Set.univ).domRestrict
        (fun q ↦ f q.time q.space)) := by
    rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun q hq ↦ ⟨⟨hq.1.1.le, hq.1.2⟩, hq.2⟩
  have hbound' : ∀ r ∈ _root_.Set.Icc (0 : Real) p.time, ‖f r‖ ≤ B := by
    intro r hr
    exact hbound r ⟨hr.1, hr.2.trans hp.2.le⟩
  have hf' : ∀ r ∈ _root_.Set.Icc (0 : Real) p.time,
      HolderWith K alpha (f r) := by
    intro r hr
    exact hf r ⟨hr.1, hr.2.trans hp.2.le⟩
  have hmeas0 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSup (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time)) :=
    fun z ↦ heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 htIoc f hsource z
  have hmeas1 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSupGradient (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time)) :=
    fun z ↦ heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
      halpha0 htIoc f hsource z
  have hmeas2All : ∀ q ∈ _root_.Set.Ioc (0 : Real) S, ∀ z : V,
      _root_.MeasureTheory.AEStronglyMeasurable
        (fun s : Real ↦ heatSupHessian (q - s) (f s) z)
        (volume.restrict (_root_.Set.uIoc (0 : Real) q)) :=
    fun q hq z ↦
      heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 hq f hsource z
  have hmeas2 : ∀ z : V, _root_.MeasureTheory.AEStronglyMeasurable
      (fun s : Real ↦ heatSupHessian (p.time - s) (f s) z)
      (volume.restrict (_root_.Set.uIoc (0 : Real) p.time)) :=
    hmeas2All p.time htIoc
  have htime := heatDuhamel_time halpha0 halpha1 hp f hf hsource'
    hmeas2All p.space
  have htimeEq : parabolicTimeDerivative (fun t x ↦ heatDuhamel t f x) p =
      f p.time p.space + heatLapDuhamel p.time (fun s ↦ f s) p.space := by
    unfold parabolicTimeDerivative
    rw [htime.hasFDerivAt.fderiv]
    simp only [heatDuhamelTimeDerivativeField, heatDuhamelTimeDerivative,
      parabolicPoint_time, parabolicPoint_space,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [htimeEq, heatDuhamel_parabolicLaplacian_eq_heatLapDuhamel
    halpha0 halpha1.le p hp.1 f hbound' hf' hmeas0 hmeas1 hmeas2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian

def heatSupParabolicSchauderConst
    (alpha B0 B1 B2 K2 : NNReal) : NNReal :=
  B0 + B1 + B2 + Module.finrank Real V * B2 +
    heatScaledParabolicHolderConst (V := V) alpha K2 +
      heatScaledParabolicHolderConst (V := V) alpha
        (Module.finrank Real V * K2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupParabolicSchauderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupParabolicSchauderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupParabolicSchauderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSupParabolicSchauderConst

omit [CompleteSpace F] in
theorem heatSup_parabolic_schauder_estimate
    {alpha B0 B1 B2 K2 : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (hB0 : ‖u‖ ≤ B0) (hB1 : ‖du‖ ≤ B1) (hB2 : ‖d2u‖ ≤ B2)
    (hK2 : HolderWith K2 alpha d2u) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (_root_.Set.Ioi (0 : Real)) Set.univ)
      (fun t x ↦ heatSup t u x) ≤
        heatSupParabolicSchauderConst (V := V) alpha B0 B1 B2 K2 := by
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (_root_.Set.Ioi (0 : Real)) Set.univ
  let w : Real → V → F := fun t x ↦ heatSup t u x
  let Cspatial : Nat → NNReal
    | 0 => B0
    | 1 => B1
    | _ => B2
  have hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j w p‖ ≤ Cspatial j := by
    intro j hj p hp
    have ht : 0 < p.time := hp.1
    interval_cases j
    · unfold parabolicSpatialJet w
      rw [norm_iteratedFDeriv_zero]
      exact (heatSup_contract ht u p.space).trans hB0
    · unfold parabolicSpatialJet w
      rw [norm_iteratedFDeriv_one, heatSup_fderiv_eq ht u du hu p.space]
      exact (heatSup_contract ht du p.space).trans hB1
    · unfold parabolicSpatialJet w
      rw [← (hessianCurryEquiv V F).norm_map,
        heatSup_hessianCurryEquiv_iteratedFDeriv_two ht u du d2u hu hdu]
      exact (heatSup_contract ht d2u p.space).trans hB2
  have htime : ∀ p ∈ Q,
      ‖parabolicTimeDerivative w p‖ ≤
        ((Module.finrank Real V : NNReal) * B2 : NNReal) := by
    intro p hp
    have ht : 0 < p.time := hp.1
    rw [heatSup_parabolicTimeDerivative_eq u du d2u hu hdu p ht]
    calc
      ‖heatSup p.time (coreLap d2u) p.space‖ ≤ ‖coreLap d2u‖ :=
        heatSup_contract ht (coreLap d2u) p.space
      _ ≤ Module.finrank Real V * ‖d2u‖ := coreLap_norm_le d2u
      _ ≤ Module.finrank Real V * B2 :=
        mul_le_mul_of_nonneg_left hB2 (Nat.cast_nonneg _)
      _ = ((Module.finrank Real V : NNReal) * B2 : NNReal) := by
        simp only [NNReal.coe_mul, NNReal.coe_natCast]
  have hspatialHolder : HolderWith
      (heatScaledParabolicHolderConst (V := V) alpha K2) alpha
      (Q.domRestrict (parabolicSpatialJet 2 w)) := by
    have hraw := heatSup_parabolic_holder (V := V) halpha d2u hK2
    have hcomp := (hessianCurryEquiv V F).symm.lipschitz.holderWith.comp hraw
    have hcomp' : HolderWith
        (heatScaledParabolicHolderConst (V := V) alpha K2) alpha
        ((hessianCurryEquiv V F).symm ∘
          Q.domRestrict (fun p ↦ heatSup p.time d2u p.space)) := by
      simpa only [Q, NNReal.coe_one, NNReal.rpow_one, one_mul] using hcomp
    convert hcomp' using 1
    funext p
    apply (hessianCurryEquiv V F).injective
    simp only [Function.comp_apply, Set.domRestrict_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact heatSup_hessianCurryEquiv_iteratedFDeriv_two p.2.1
      u du d2u hu hdu p.1.space
  have htimeHolder : HolderWith
      (heatScaledParabolicHolderConst (V := V) alpha
        (Module.finrank Real V * K2)) alpha
      (Q.domRestrict (parabolicTimeDerivative w)) := by
    have hlap := coreLap_holder d2u hK2
    have hraw := heatSup_parabolic_holder (V := V) halpha (coreLap d2u) hlap
    convert hraw using 1
    funext p
    exact heatSup_parabolicTimeDerivative_eq u du d2u hu hdu p.1 p.2.1
  have hresult := eParabolicC2HolderGaugeOn_le Cspatial
    (Module.finrank Real V * B2)
    (heatScaledParabolicHolderConst (V := V) alpha K2)
    (heatScaledParabolicHolderConst (V := V) alpha
      (Module.finrank Real V * K2))
    hspatial htime hspatialHolder htimeHolder
  unfold heatSupParabolicSchauderConst
  simpa only [Q, w, Cspatial, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, ENNReal.coe_add, ENNReal.coe_mul,
    NNReal.coe_natCast] using hresult

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate

omit [CompleteSpace F] in
theorem heatSup_parabolic_schauder_estimate_nnnorm
    {alpha K2 : NNReal} (halpha : alpha ≤ 1)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[Real] F) (d2u x) x)
    (hK2 : HolderWith K2 alpha d2u) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (_root_.Set.Ioi (0 : Real)) Set.univ)
      (fun t x ↦ heatSup t u x) ≤
        heatSupParabolicSchauderConst (V := V) alpha
          ‖u‖₊ ‖du‖₊ ‖d2u‖₊ K2 := by
  apply heatSup_parabolic_schauder_estimate halpha u du d2u hu hdu
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact hK2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate_nnnorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate_nnnorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate_nnnorm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_parabolic_schauder_estimate_nnnorm

def heatSolution
    (u0 : BoundedContinuousFunction V F)
    (f : Real → BoundedContinuousFunction V F) : Real → V → F :=
  fun t x ↦ heatSup t u0 x + heatDuhamel t f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution

theorem heatSolution_parabolicTimeDerivative_eq_source_add_laplacian
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S : Real} (p : ParabolicPoint V) (hp : p.time ∈ _root_.Set.Ioo (0 : Real) S)
    (u0 : BoundedContinuousFunction V F)
    (du0 : BoundedContinuousFunction V (V →L[Real] F))
    (d2u0 : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu0 : ∀ x : V, HasFDerivAt (u0 : V → F) (du0 x) x)
    (hdu0 : ∀ x : V,
      HasFDerivAt (du0 : V → V →L[Real] F) (d2u0 x) x)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ _root_.Set.Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (_root_.Set.Icc (0 : Real) S) Set.univ).domRestrict
        (fun q ↦ f q.time q.space))) :
    parabolicTimeDerivative (heatSolution u0 f) p =
      f p.time p.space + parabolicLaplacian (heatSolution u0 f) p := by
  let uh : Real → V → F := fun t x ↦ heatSup t u0 x
  let uf : Real → V → F := fun t x ↦ heatDuhamel t f x
  have hpQ : p ∈ parabolicCylinder (_root_.Set.Ioc (0 : Real) p.time) Set.univ :=
    ⟨⟨hp.1, le_rfl⟩, Set.mem_univ p.space⟩
  have huhSpatial : ContDiffAt Real 2 (uh p.time) p.space :=
    (heatSup_contDiff_two hp.1 u0).contDiffAt
  have huhTime : DifferentiableAt Real (fun t ↦ uh t p.space) p.time :=
    (heatSup_time hp.1 u0 du0 d2u0 hu0 hdu0 p.space).differentiableAt
  have huf := (heatDuhamel_isParabolicC2HolderOn
    halpha0 halpha1 hp.1.le hp.2 f hbound hsource).1
  have hufSpatial : ContDiffAt Real 2 (uf p.time) p.space :=
    huf.1 p hpQ
  have hufTime : DifferentiableAt Real (fun t ↦ uf t p.space) p.time :=
    huf.2 p hpQ
  change parabolicTimeDerivative (fun t x ↦ uh t x + uf t x) p =
    f p.time p.space +
      parabolicLaplacian (fun t x ↦ uh t x + uf t x) p
  rw [parabolicTimeDerivative_add uh uf p huhTime hufTime,
    parabolicLaplacian_add uh uf p huhSpatial hufSpatial,
    heatSup_parabolicTimeDerivative_eq_laplacian
      u0 du0 d2u0 hu0 hdu0 p hp.1,
    heatDuhamel_parabolicTimeDerivative_eq_source_add_laplacian
      halpha0 halpha1 p hp f hbound hsource]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_eq_source_add_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_eq_source_add_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_eq_source_add_laplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_eq_source_add_laplacian

theorem heatSolution_parabolicTimeDerivative_sub_laplacian
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S : Real} (p : ParabolicPoint V) (hp : p.time ∈ _root_.Set.Ioo (0 : Real) S)
    (u0 : BoundedContinuousFunction V F)
    (du0 : BoundedContinuousFunction V (V →L[Real] F))
    (d2u0 : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu0 : ∀ x : V, HasFDerivAt (u0 : V → F) (du0 x) x)
    (hdu0 : ∀ x : V,
      HasFDerivAt (du0 : V → V →L[Real] F) (d2u0 x) x)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ _root_.Set.Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (_root_.Set.Icc (0 : Real) S) Set.univ).domRestrict
        (fun q ↦ f q.time q.space))) :
    parabolicTimeDerivative (heatSolution u0 f) p -
        parabolicLaplacian (heatSolution u0 f) p =
      f p.time p.space := by
  rw [heatSolution_parabolicTimeDerivative_eq_source_add_laplacian
    halpha0 halpha1 p hp u0 du0 d2u0 hu0 hdu0 f hbound hsource]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_sub_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_sub_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_sub_laplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolicTimeDerivative_sub_laplacian

def heatSolutionSchauderConst
    (alpha B0 B1 B2 K2 Kf Bf : NNReal) (T : Real) : NNReal :=
  heatSupParabolicSchauderConst (V := V) alpha B0 B1 B2 K2 +
    heatPotentialSchauderConst (V := V) alpha Kf Bf Kf T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolutionSchauderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolutionSchauderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolutionSchauderConst ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolutionSchauderConst

theorem heatSolution_parabolic_schauder_estimate
    {alpha B0 B1 B2 K2 Kf Bf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (u0 : BoundedContinuousFunction V F)
    (du0 : BoundedContinuousFunction V (V →L[Real] F))
    (d2u0 : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu0 : ∀ x : V, HasFDerivAt (u0 : V → F) (du0 x) x)
    (hdu0 : ∀ x : V,
      HasFDerivAt (du0 : V → V →L[Real] F) (d2u0 x) x)
    (hB0 : ‖u0‖ ≤ B0) (hB1 : ‖du0‖ ≤ B1) (hB2 : ‖d2u0‖ ≤ B2)
    (hK2 : HolderWith K2 alpha d2u0)
    (f : Real → BoundedContinuousFunction V F)
    (hBf : ∀ r ∈ _root_.Set.Icc (0 : Real) S, ‖f r‖ ≤ Bf)
    (hKf : HolderWith Kf alpha
      ((parabolicCylinder (_root_.Set.Icc (0 : Real) S) Set.univ).domRestrict
        (fun p ↦ f p.time p.space))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (_root_.Set.Ioc (0 : Real) T) Set.univ)
      (heatSolution u0 f) ≤
        heatSolutionSchauderConst (V := V)
          alpha B0 B1 B2 K2 Kf Bf T := by
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (_root_.Set.Ioc (0 : Real) T) Set.univ
  let uh : Real → V → F := fun t x ↦ heatSup t u0 x
  let uf : Real → V → F := fun t x ↦ heatDuhamel t f x
  have hQ : Q ⊆ parabolicCylinder (_root_.Set.Ioi (0 : Real)) Set.univ := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have huhGauge : eParabolicC2HolderGaugeOn alpha Q uh ≤
      heatSupParabolicSchauderConst (V := V) alpha B0 B1 B2 K2 := by
    exact (eParabolicC2HolderGaugeOn_mono hQ alpha uh).trans
      (heatSup_parabolic_schauder_estimate halpha1.le
        u0 du0 d2u0 hu0 hdu0 hB0 hB1 hB2 hK2)
  have hufGauge : eParabolicC2HolderGaugeOn alpha Q uf ≤
      heatPotentialSchauderConst (V := V) alpha Kf Bf Kf T :=
    heatDuhamel_schauder_estimate_of_parabolic_holder
      halpha0 halpha1 hT hTS f hBf hKf
  have huh : IsParabolicC2On Q uh := by
    constructor
    · intro p hp
      exact (heatSup_contDiff_two hp.1.1 u0).contDiffAt
    · intro p hp
      exact (heatSup_time hp.1.1 u0 du0 d2u0 hu0 hdu0 p.space).differentiableAt
  have huf : IsParabolicC2On Q uf :=
    (heatDuhamel_isParabolicC2HolderOn
      halpha0 halpha1 hT hTS f hBf hKf).1
  have hadd := eParabolicC2HolderGaugeOn_add_le alpha Q uh uf huh huf
  unfold heatSolutionSchauderConst
  exact hadd.trans (add_le_add huhGauge hufGauge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolic_schauder_estimate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolic_schauder_estimate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolic_schauder_estimate ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSolution_parabolic_schauder_estimate

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
