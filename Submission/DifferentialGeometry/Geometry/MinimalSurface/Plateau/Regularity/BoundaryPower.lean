import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryEnergy
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.LocalLowerSemicontinuity
import Submission.DifferentialGeometry.Analysis.Asymptotics.LimsupDecay
import Submission.DifferentialGeometry.Analysis.Integration.Integral.IsometricDerivative
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Subsets
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.DifferentialGeometry.Analysis.Integration.Integral.TruncatedBallPower
import Submission.DifferentialGeometry.Geometry.HarmonicMap.WeakGradientGlobal
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.InteriorEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

private theorem le_mul_limsup_of_le_liminf
    {a b : ℕ → ℝ} {x C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hbb : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop b)
    (hle : ∀ n, a n ≤ C * b n) (hx : x ≤ _root_.Filter.liminf a _root_.Filter.atTop) :
    x ≤ C * _root_.Filter.limsup b atTop := by
  have halow : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop a :=
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall ha)
  have hblow : _root_.Filter.IsBoundedUnder (· ≥ ·) _root_.Filter.atTop b :=
    _root_.Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall hb)
  have hcbb : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (fun n => C * b n) := by
    obtain ⟨D, hD⟩ := hbb
    refine ⟨C * D, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, C * b n ≤ C * D
    change ∀ᶠ n in _root_.Filter.atTop, b n ≤ D at hD
    exact hD.mono fun n hn => mul_le_mul_of_nonneg_left hn hC
  have habb : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop a := by
    obtain ⟨D, hD⟩ := hcbb
    refine ⟨D, ?_⟩
    change ∀ᶠ n in _root_.Filter.atTop, a n ≤ D
    change ∀ᶠ n in _root_.Filter.atTop, C * b n ≤ D at hD
    exact hD.mono fun n hn => (hle n).trans hn
  have hmul := (show Monotone (fun t : ℝ => C * t) from
    fun s t hst => mul_le_mul_of_nonneg_left hst hC).map_limsup_of_continuousAt b
      (continuous_const.mul continuous_id).continuousAt hbb hblow.isCoboundedUnder_le
  exact hx.trans ((_root_.Filter.liminf_le_limsup habb halow).trans
    ((_root_.Filter.limsup_le_limsup (Eventually.of_forall hle) halow.isCoboundedUnder_le hcbb).trans_eq
      hmul.symm))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.le_mul_limsup_of_le_liminf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.le_mul_limsup_of_le_liminf target :: scope.openDecls } }


local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_uniform_boundary_weak_gradient_power_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ _root_.Set.range Φ, _root_.Metric.closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : _root_.Set.MapsTo T U (_root_.Set.range Φ))
    (hfix : ∀ y ∈ _root_.Set.range Φ, T y = y)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (_root_.Metric.ball (0 : V) 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (_root_.Metric.ball (0 : V) 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict (_root_.Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 (volume.restrict (_root_.Metric.ball (0 : V) 1))),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z))) :
    ∃ α C R₀ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ 0 < R₀ ∧
      ∀ c ∈ _root_.Metric.sphere (0 : V) 1, ∀ s ∈ _root_.Set.Ioc (0 : ℝ) R₀,
        (∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s,
          ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hw i).weakGrad x j)‖ ^ 2) ≤ C * s ^ (2 * α) := by
  obtain ⟨δ, θ, B, hδ, _, hθ, hθ1, hB, hdec⟩ := exists_uniform_boundary_energy_dyadic_decay
    g hΦ hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
      u hu hmin ψ hψ htrace hthird htwothird
  obtain ⟨CΦ, _, hEmb⟩ := exists_integral_norm_fderiv_comp_diskExtension_sq_le_on_subsets g hΦ
  choose Ku hKu using fun n => (hu n).2
  have hnonneg (n : ℕ) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension (u n)) z := by
    unfold diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  let e := Complex.orthonormalBasisOneI.repr.symm
  let f (n : ℕ) : V → F := (Φ ∘ diskExtension (u n)) ∘ e
  let G (x : V) := ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hw i).weakGrad x j)‖ ^ 2
  let H : ℝ := 8 * (CΦ : ℝ) ^ 2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hf (n : ℕ) : LipschitzWith (CΦ * Ku n) (f n) := by
    simpa only [mul_one] using ((hEmb (u n) (Ku n) (hKu n)).1.comp e.isometry.lipschitz)
  have hG0 (x : V) : 0 ≤ G x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGi : _root_.MeasureTheory.IntegrableOn G (_root_.Metric.ball (0 : V) 1) := by
    apply _root_.MeasureTheory.integrable_finsetSum
    intro j _
    have hj : _root_.MeasureTheory.MemLp (fun x => WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        2 (volume.restrict (_root_.Metric.ball (0 : V) 1)) :=
      MemLp.of_eval_piLp fun i => (hw i).weakGrad_component_memLp j
    exact hj.norm.integrable_sq
  have htotalBound : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop (fun n => riemannianDiskEnergy g (u n)) :=
    hmin.isBoundedUnder_le
  let Q (c : V) (s : ℝ) := _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s
  let SC (c : V) (s : ℝ) := _root_.Metric.ball (0 : ℂ) 1 ∩ _root_.Metric.ball (e c) s
  let CC (c : V) (s : ℝ) := _root_.Metric.closedBall (e c) s ∩ _root_.Metric.closedBall (0 : ℂ) 1
  have hsubset (c : V) (s : ℝ) : SC c s ⊆ CC c s := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.2, _root_.Metric.ball_subset_closedBall hz.1⟩
  have hcolumnbound (n : ℕ) (c : V) (s : ℝ) :
      (∫ x in Q c s, ∑ j : Fin 2, ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) ≤
        H * ∫ z in CC c s, diskMapEnergyDensity g (diskExtension (u n)) z := by
    have hNormI := (hf n).integrableOn_norm_fderiv_sq
      (μ := _root_.MeasureTheory.MeasureSpace.volume) ((_root_.MeasureTheory.measure_mono (show Q c s ⊆ _root_.Metric.closedBall (0 : V) 1 from
        fun _ hx => _root_.Metric.ball_subset_closedBall hx.1)).trans_lt
          (_root_.ProperSpace.isCompact_closedBall _ _).measure_lt_top).ne
    have hpt (x : V) :
        (∑ j : Fin 2, ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) ≤
        2 * ‖fderiv ℝ (f n) x‖ ^ 2 := by
      have hj (j : Fin 2) :
          ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ≤ ‖fderiv ℝ (f n) x‖ := by
        simpa only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one] using
          (fderiv ℝ (f n) x).le_opNorm (EuclideanSpace.single j 1)
      rw [Fin.sum_univ_two]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hj 0) 2,
        pow_le_pow_left₀ (norm_nonneg _) (hj 1) 2]
    have hcolumnsI : _root_.MeasureTheory.IntegrableOn
        (fun x => ∑ j : Fin 2, ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2) (Q c s) := by
      apply (hNormI.const_mul 2).mono'
        ((Finset.measurable_sum Finset.univ fun j _ =>
          (measurable_fderiv_apply_const ℝ (f n) _).norm.pow_const 2).aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        exact hpt x
    have hi₁ := _root_.MeasureTheory.integral_mono_ae hcolumnsI (hNormI.const_mul 2) (Eventually.of_forall hpt)
    rw [_root_.MeasureTheory.integral_const_mul] at hi₁
    have hpre : e ⁻¹' SC c s = Q c s := by
      ext x
      simp only [SC, Q, _root_.Set.mem_preimage, _root_.Set.mem_inter_iff, _root_.Metric.mem_ball, dist_zero_right,
        e.norm_map, e.dist_map]
    have htransport : (∫ x in Q c s, ‖fderiv ℝ (f n) x‖ ^ 2) =
        ∫ z in SC c s, ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2 := by
      simp only [f, e.norm_fderiv_comp]
      have h := e.measurePreserving.setIntegral_preimage_emb e.toMeasurableEquiv.measurableEmbedding
        (fun z => ‖fderiv ℝ (Φ ∘ diskExtension (u n)) z‖ ^ 2) (SC c s)
      simpa only [hpre] using h
    obtain ⟨_, hiE, hbound⟩ := (hEmb (u n) (Ku n) (hKu n)).2 (SC c s)
      (fun _ hz => _root_.Metric.ball_subset_closedBall hz.1)
    have hmono := _root_.MeasureTheory.setIntegral_mono_set
      ((integrable_diskMapEnergyDensity g (hKu n)).mono_set _root_.Set.inter_subset_right)
      (Eventually.of_forall fun z => hnonneg n z)
      (Eventually.of_forall (hsubset c s))
    rw [htransport] at hi₁
    apply hi₁.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num)).trans ?_)
    have hmul := mul_le_mul_of_nonneg_left hmono hH
    change 2 * (4 * (CΦ : ℝ) ^ 2 * _) ≤ H * _
    calc
      _ = H * (∫ z in SC c s, diskMapEnergyDensity g (diskExtension (u n)) z) := by
        dsimp only [H]
        ring
      _ ≤ _ := hmul
  have hdyadic (c : V) (hc : c ∈ _root_.Metric.sphere (0 : V) 1) (k : ℕ) :
      (∫ x in Q c (δ / (2 : ℝ) ^ k), G x) ≤ θ ^ k * (H * B) := by
    let s := δ / (2 : ℝ) ^ k
    let a (n : ℕ) := ∫ x in Q c s, ∑ j : Fin 2,
      ‖fderiv ℝ (f n) x (EuclideanSpace.single j 1)‖ ^ 2
    let b (n : ℕ) := ∫ z in CC c s, diskMapEnergyDensity g (diskExtension (u n)) z
    have ha0 (n : ℕ) : 0 ≤ a n := _root_.MeasureTheory.integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hb0 (n : ℕ) : 0 ≤ b n := _root_.MeasureTheory.integral_nonneg fun z => hnonneg n z
    have hbBound : _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop b := by
      obtain ⟨A, hA⟩ := htotalBound
      refine ⟨A, ?_⟩
      change ∀ᶠ n in _root_.Filter.atTop, b n ≤ A
      change ∀ᶠ n in _root_.Filter.atTop, riemannianDiskEnergy g (u n) ≤ A at hA
      filter_upwards [hA] with n hn
      exact (_root_.MeasureTheory.setIntegral_mono_set (integrable_diskMapEnergyDensity g (hKu n))
        (Eventually.of_forall fun z => hnonneg n z)
        (Eventually.of_forall _root_.Set.inter_subset_right)).trans hn
    have hlsc := Sobolev.Euclidean.integral_sum_norm_sq_weak_gradient_le_liminf_on_subset
      (S := Q c s)
      (measurableSet_ball.inter measurableSet_ball) _root_.Set.inter_subset_left f w hs hw
      (fun n => CΦ * Ku n) hf hrep hweak
    have hlim := le_mul_limsup_of_le_liminf hH ha0 hb0 hbBound
      (fun n => hcolumnbound n c s) hlsc
    have hec : e c ∈ _root_.Metric.sphere (0 : ℂ) 1 := by
      simpa only [_root_.Metric.mem_sphere, dist_zero_right, e.norm_map] using hc
    exact hlim.trans ((mul_le_mul_of_nonneg_left (hdec (e c) hec k) hH).trans_eq (by ring))
  let energy (c : _root_.Metric.sphere (0 : V) 1) (s : ℝ) := ∫ x in Q c s, G x
  have hmono (c : _root_.Metric.sphere (0 : V) 1) : MonotoneOn (energy c) (_root_.Set.Ioc (0 : ℝ) δ) := by
    intro s hs t ht hst
    apply _root_.MeasureTheory.setIntegral_mono_set (hGi.mono_set _root_.Set.inter_subset_left)
      (Eventually.of_forall hG0)
    exact Eventually.of_forall (_root_.Set.inter_subset_inter_right _ (_root_.Metric.ball_subset_ball hst))
  obtain ⟨α, C, hα, hα1, hC, hpower⟩ := exists_radius_power_bound_of_dyadic_decay energy
    hδ hθ hθ1 (mul_nonneg hH hB) hmono (fun c k => hdyadic c c.property k)
  exact ⟨α, C, δ, hα, hα1, hC, hδ, fun c hc s hs => hpower ⟨c, hc⟩ s hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_boundary_weak_gradient_power_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_boundary_weak_gradient_power_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_boundary_weak_gradient_power_bound ``Submission.DifferentialGeometry.Geometry.exists_uniform_boundary_weak_gradient_power_bound

end DifferentialGeometry.Geometry

end

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_uniform_weak_gradient_power_bound_on_truncated_balls
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : _root_.Set.range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ _root_.Set.range Φ, _root_.Metric.closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : _root_.Set.MapsTo T U (_root_.Set.range Φ))
    (hfix : ∀ y ∈ _root_.Set.range Φ, T y = y)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : _root_.Filter.Tendsto (fun n => riemannianDiskEnergy g (u n)) _root_.Filter.atTop
      (𝓝 (_root_.InfSet.sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3)
    (w : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (_root_.Metric.ball (0 : V) 1))
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (_root_.Metric.ball (0 : V) 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict (_root_.Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ (fun y => Φ (diskExtension (u n)
        (Complex.orthonormalBasisOneI.repr.symm y)) i) x (EuclideanSpace.single j 1)))
    (hL2 : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (_root_.Metric.ball (0 : V) 1))) _root_.Filter.atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : V) 1),
      _root_.Filter.Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        _root_.Filter.atTop (𝓝 (w x)))
    (hweak : ∀ i (z : _root_.MeasureTheory.Lp V 2 (volume.restrict (_root_.Metric.ball (0 : V) 1))),
      _root_.Filter.Tendsto (fun n => _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) _root_.Filter.atTop
        (𝓝 (_root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z))) :
    ∃ α C R₀ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ 0 < R₀ ∧ R₀ ≤ 1 ∧
      ∀ c ∈ _root_.Metric.closedBall (0 : V) 1, ∀ s ∈ _root_.Set.Ioc (0 : ℝ) R₀,
        (∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s,
          ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hw i).weakGrad x j)‖ ^ 2) ≤ C * s ^ (2 * α) := by
  obtain ⟨αb, Cb, Rb, hαb, _, hCb, hRb, hb⟩ :=
    exists_uniform_boundary_weak_gradient_power_bound
      g (hΦ.of_le (by simp)) hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
      u hu hmin ψ hψ htrace hthird htwothird w hs hw hrep hweak
  obtain ⟨δi, θ, hδi, _, hθ, hθ1, hstep, _⟩ :=
    exists_dyadic_weak_energy_decay_on_interior_balls_of_minimizing_sequence
      g hΦ hN hr hΦN hleft u hu hmin hs w hw hrep hL2 hae hweak
  let A := pullbackMetricCoefficients g r
  let G (x : V) := ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hw i).weakGrad x j)‖ ^ 2
  let e (x : V) := ∑ j : Fin 2, A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
  have hK : IsCompact (_root_.Set.range Φ) := isCompact_range hΦ.continuous
  have hwK : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : V) 1), w x ∈ _root_.Set.range Φ :=
    hae.mono fun x hx => hK.isClosed.mem_of_tendsto hx
      (Eventually.of_forall fun n => _root_.Set.mem_range_self _)
  have hA : ContinuousOn A (_root_.Set.range Φ) :=
    (contDiffOn_pullback_metric_coefficients g hN hr).continuousOn.mono hΦN
  have hei : _root_.MeasureTheory.IntegrableOn e (_root_.Metric.ball (0 : V) 1) :=
    integrable_sum_quadratic_weakGrad hw hK A hA hwK
  have he0 (x : V) : 0 ≤ e x :=
    Finset.sum_nonneg fun j _ => metric_inner_self_nonneg g (r (w x)) _
  have hGi : _root_.MeasureTheory.IntegrableOn G (_root_.Metric.ball (0 : V) 1) := by
    apply _root_.MeasureTheory.integrable_finsetSum
    intro j _
    have hj : _root_.MeasureTheory.MemLp (fun x => WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        2 (volume.restrict (_root_.Metric.ball (0 : V) 1)) :=
      MemLp.of_eval_piLp fun i => (hw i).weakGrad_component_memLp j
    exact hj.norm.integrable_sq
  obtain ⟨A₀, hA₀⟩ := hK.bddAbove_image
    ((@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA)
  let L := _root_.Max.max A₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have heG : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : V) 1), e x ≤ L * G x := by
    filter_upwards [hwK] with x hx
    have hAx : ‖A (w x)‖ ≤ L := (hA₀ (_root_.Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
    dsimp only [e, G]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    let X : F := WithLp.toLp 2 (fun i => (hw i).weakGrad x j)
    calc
      A (w x) X X ≤ ‖A (w x) X X‖ := le_abs_self _
      _ ≤ ‖A (w x)‖ * ‖X‖ * ‖X‖ := (A (w x)).le_opNorm₂ X X
      _ ≤ L * ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖X‖]
  have heBoundary (c : V) (hc : c ∈ _root_.Metric.sphere (0 : V) 1)
      (s : ℝ) (hs0 : 0 < s) (hsR : s ≤ Rb) :
      (∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s, e x) ≤ (L * Cb) * s ^ (2 * αb) := by
    have hcompare : (∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s, e x) ≤
        L * ∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s, G x := by
      rw [← _root_.MeasureTheory.integral_const_mul]
      exact _root_.MeasureTheory.integral_mono_ae (hei.mono_set _root_.Set.inter_subset_left)
        ((hGi.mono_set _root_.Set.inter_subset_left).const_mul L)
        (_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_left heG)
    exact hcompare.trans ((mul_le_mul_of_nonneg_left (hb c hc s ⟨hs0, hsR⟩) hL).trans_eq
      (by ring))
  obtain ⟨p, δ, K, hp, _, hp2, hδ, hδ8, hK0, hpower⟩ :=
    exists_uniform_cap_power_bound_of_boundary_bound_of_half_contraction hei
      (Eventually.of_forall he0) (mul_pos (by norm_num) hαb) (mul_nonneg hL hCb)
      hRb hδi hθ hθ1 heBoundary hstep
  obtain ⟨CΦ, _, hcoercive⟩ := exists_weak_gradient_norm_sq_le_pullback_metric
    g hΦ hN hr hΦN hleft
  have hGe : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : V) 1), G x ≤ (CΦ : ℝ) ^ 2 * e x := by
    filter_upwards [hcoercive 2 (_root_.Metric.ball (0 : V) 1) _root_.Metric.isOpen_ball w hw hwK] with x hx
    dsimp only [G, e]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hx j
  refine ⟨p / 2, (CΦ : ℝ) ^ 2 * K, δ, half_pos hp, by linarith,
    mul_nonneg (sq_nonneg _) hK0, hδ, by linarith, ?_⟩
  intro c hc s hs
  have hcompare : (∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s, G x) ≤
      (CΦ : ℝ) ^ 2 * ∫ x in _root_.Metric.ball (0 : V) 1 ∩ _root_.Metric.ball c s, e x := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    exact _root_.MeasureTheory.integral_mono_ae (hGi.mono_set _root_.Set.inter_subset_left)
      ((hei.mono_set _root_.Set.inter_subset_left).const_mul _)
      (_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset _root_.Set.inter_subset_left hGe)
  have h := hcompare.trans (mul_le_mul_of_nonneg_left (hpower c hc s hs.1 hs.2) (sq_nonneg _))
  have hpE : 2 * (p / 2) = p := by ring
  simpa only [hpE, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_uniform_weak_gradient_power_bound_on_truncated_balls then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_uniform_weak_gradient_power_bound_on_truncated_balls"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_uniform_weak_gradient_power_bound_on_truncated_balls ``Submission.DifferentialGeometry.Geometry.exists_uniform_weak_gradient_power_bound_on_truncated_balls

end DifferentialGeometry.Geometry

end
