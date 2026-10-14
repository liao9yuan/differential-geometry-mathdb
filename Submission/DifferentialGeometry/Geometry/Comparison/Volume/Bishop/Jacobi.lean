import Submission.DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicModel
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Filter _root_.Matrix _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Matrix _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Volume
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
theorem hasDerivAt_denRatio
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q t : ℝ) (d : ℕ)
    (hq : 0 ≤ q) (ht : 0 < t)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hpos : 0 < (curveGram (I := I) g γ V t).det)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    HasDerivAt
      (fun r => curveDensity (I := I) g γ V r / hyperbolicDensity q d r)
      ((curveDensity (I := I) g γ V t / hyperbolicDensity q d t) *
        (curveMean (I := I) g γ V t - hyperbolicMeanCurv q d t)) t := by
  have hden : HasDerivAt (curveDensity (I := I) g γ V)
      (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t) t := by
    refine (hasDerivAt_symmDen (I := I) hn g γ V t hγ hVdiff hpos hW).congr_deriv ?_
    rw [curveMean, curveShape]
  exact hasDerivAt_hyperbolicRatio
    (j' := fun r => curveMean (I := I) g γ V r *
      curveDensity (I := I) g γ V r)
    (m := curveMean (I := I) g γ V) hq ht hden rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hasDerivAt_denRatio then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hasDerivAt_denRatio"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hasDerivAt_denRatio ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hasDerivAt_denRatio

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem denRatio_ge_of_dir
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q B : ℝ)
    (hq : 0 ≤ q) (hB : 0 < B)
    (hLI : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      LinearIndependent ℝ fun i => V i t)
    (hdir : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
        (B * t) ^ 2 ≤
          g.inner (γ t) (∑ i, v i • V i t) (∑ i, v i • V i t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity q (Fintype.card ι) t := by
  refine ⟨(B / 2) ^ Fintype.card ι,
    pow_pos (div_pos hB (by norm_num)) _, ?_⟩
  filter_upwards [hLI, hdir, hyperbolicSn_le_two q, self_mem_nhdsWithin]
    with t hLIt hdirT hsn ht
  change 0 < t at ht
  have hgram := curveGram_posDef (I := I) g γ V t hLIt
  have hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      (B * t) ^ 2 ≤ RCLike.re
        (dotProduct (_root_.Star.star ⇑v) (Matrix.mulVec (curveGram (I := I) g γ V t) ⇑v)) := by
    intro v hv
    have hquad := curveGram_dotVec (I := I) g γ V t (⇑v)
    change (B * t) ^ 2 ≤
      dotProduct (_root_.Star.star ⇑v) (Matrix.mulVec (curveGram (I := I) g γ V t) ⇑v)
    rw [hquad]
    exact hdirT v hv
  have hdet := sqrt_pow_le_sqrt_det_of_rayleigh
    (A := curveGram (I := I) g γ V t) (a := (B * t) ^ 2)
    hgram.posSemidef (sq_nonneg _) hray
  have hsqrt :
      Real.sqrt (((B * t) ^ 2) ^ Fintype.card ι) =
        (B * t) ^ Fintype.card ι := by
    calc
      Real.sqrt (((B * t) ^ 2) ^ Fintype.card ι) =
          Real.sqrt (((B * t) ^ Fintype.card ι) ^ 2) := by
            congr 1
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
      _ = |(B * t) ^ Fintype.card ι| := Real.sqrt_sq_eq_abs _
      _ = (B * t) ^ Fintype.card ι :=
        abs_of_nonneg (pow_nonneg (mul_nonneg hB.le ht.le) _)
  have hcurve :
      (B * t) ^ Fintype.card ι ≤ curveDensity (I := I) g γ V t := by
    rw [← hsqrt]
    simpa only [curveDensity] using hdet
  have hmodel : hyperbolicDensity q (Fintype.card ι) t ≤
      (2 * t) ^ Fintype.card ι := by
    exact pow_le_pow_left₀ (hyperbolicSn_pos hq ht).le hsn _
  rw [le_div_iff₀ (hyperbolicDensity_pos hq ht)]
  calc
    (B / 2) ^ Fintype.card ι * hyperbolicDensity q (Fintype.card ι) t ≤
        (B / 2) ^ Fintype.card ι * (2 * t) ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_left hmodel (pow_nonneg (div_nonneg hB.le (by norm_num)) _)
    _ = (B * t) ^ Fintype.card ι := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ curveDensity (I := I) g γ V t := hcurve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.denRatio_ge_of_dir then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.denRatio_ge_of_dir"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.denRatio_ge_of_dir ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.denRatio_ge_of_dir

omit [NeZero (Module.finrank ℝ E)]
  [T2Space M]
  [SigmaCompactSpace M] in
theorem curveRatio_anti
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q b : ℝ) (d : ℕ)
    (hq : 0 ≤ q)
    (hγ : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hLI : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hmean : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤ hyperbolicMeanCurv q d t) :
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t / hyperbolicDensity q d t)
      (_root_.Set.Ioo (0 : ℝ) b) := by
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / hyperbolicDensity q d t
  have hR : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv q d t)) t := by
    intro t ht
    simpa only [R] using
      hasDerivAt_denRatio (I := I) hn g γ V q t d hq ht.1 (hγ t ht)
        (hVdiff t ht) (curveGram_det_pos (I := I) g γ V t (hLI t ht))
        (hW t ht)
  have hRpos : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (hyperbolicDensity_pos hq ht.1)
  have hdiff : DifferentiableOn ℝ R (_root_.Set.Ioo (0 : ℝ) b) := by
    intro t ht
    exact (hR t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv q d t) ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hRpos t ht).le
      (sub_nonpos.mpr (hmean t ht))
  have hanti : AntitoneOn R (_root_.Set.Ioo (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 b) hdiff.continuousOn ?_ ?_
    · simpa using hdiff
    · intro t ht
      have ht' : t ∈ _root_.Set.Ioo (0 : ℝ) b := by simpa using ht
      rw [(hR t ht').deriv]
      exact hderiv t ht'
  simpa only [R] using hanti

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveRatio_anti then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveRatio_anti"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveRatio_anti ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveRatio_anti

omit [SigmaCompactSpace M] in
theorem curveMean_le_hyperbolic
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q a b : ℝ)
    (hq : 0 ≤ q)
    (ha : 0 < a)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hγ : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hspeed : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = a ^ 2)
    (hVperp : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0)
    (hDVperp : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hVdiff : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity (q * a) (Module.finrank ℝ E - 1) t) :
    ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤
        hyperbolicMeanCurv (q * a) (Module.finrank ℝ E - 1) t := by
  let d : ℕ := Module.finrank ℝ E - 1
  have hqa : 0 ≤ q * a := mul_nonneg hq ha.le
  let m' : ℝ → ℝ := fun t =>
    -_root_.Matrix.trace ((curveGram (I := I) g γ V t)⁻¹ *
        curveCurvGram (I := I) g γ V t) -
      trace ((curveShape (I := I) g γ V t) ^ 2)
  have hm : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      HasDerivAt (curveMean (I := I) g γ V) (m' t) t := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_le (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      hRic).1
  have hmle : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      m' t ≤ (d : ℝ) * (q * a) ^ 2 -
        curveMean (I := I) g γ V t ^ 2 / (d : ℝ) := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_le (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      hRic).2
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / hyperbolicDensity (q * a) d t
  have hR : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv (q * a) d t)) t := by
    intro t ht
    simpa only [R, d] using
      hasDerivAt_denRatio (I := I) hn g γ V (q * a) t d hqa ht.1 (hγ t ht)
        (hVdiff t ht) (curveGram_det_pos (I := I) g γ V t (hLI t ht))
        (hW t ht)
  have hRpos : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (hyperbolicDensity_pos hqa ht.1)
  apply mean_le_hyperbolic_of_ratio hqa hd hm hmle hR hRpos
  simpa only [R, d] using hRatioLower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_hyperbolic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_hyperbolic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_hyperbolic ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_hyperbolic

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
