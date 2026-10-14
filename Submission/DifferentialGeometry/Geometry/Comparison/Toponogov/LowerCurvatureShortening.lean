import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureCoshSupport
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.HyperbolicComparisonAngle
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import Submission.DifferentialGeometry.Analysis.ODE.HyperbolicSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem hyperbolicComparisonCosine_shorten_first
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (o : M) (u v : TangentSpace I o) (k a1 a2 b : ℝ)
    (hk : 0 < k) (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb : 0 < b)
    (hu : g.inner o u u = 1)
    (hminB : (_root_.Manifold.riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal = b)
    (hsec : ∀ s ∈ _root_.Set.Ioo (0 : ℝ) a2, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o v b) y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm o u s) =
        riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o v b)
          (intrinsicGeodesic (I := I) g hEnorm o u s) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2)) :
    hyperbolicComparisonCosine k a1 b
      (_root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal ≤
    hyperbolicComparisonCosine k a2 b
      (_root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b)).toReal := by
  let p := intrinsicGeodesic (I := I) g hEnorm o v b
  let gamma := intrinsicGeodesic (I := I) g hEnorm o u
  let f : ℝ → ℝ := fun s => Real.cosh (k * (_root_.Manifold.riemannianEDist I p (gamma s)).toReal)
  have hpo : _root_.Manifold.riemannianEDist I p o ≠ ⊤ := by
    intro htop
    rw [_root_.Manifold.riemannianEDist_comm, htop, ENNReal.toReal_top] at hminB
    linarith
  have hfin (s : ℝ) : _root_.Manifold.riemannianEDist I p (gamma s) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (_root_.Manifold.riemannianEDist_triangle (y := o))
    apply ENNReal.add_ne_top.mpr
    refine ⟨hpo, ?_⟩
    rcases le_total 0 s with hs | hs
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
        simpa only [intrinsicGeodesic_zero, hu, Real.sqrt_one, one_mul, sub_zero] using
          intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm o u hs)
    · rw [_root_.Manifold.riemannianEDist_comm]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
        simpa only [intrinsicGeodesic_zero, hu, Real.sqrt_one, one_mul] using
          intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm o u hs)
  have hdist : Continuous (fun s => (_root_.Manifold.riemannianEDist I p (gamma s)).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    apply (ENNReal.continuousAt_toReal (hfin s)).comp
      (f := fun t : ℝ => _root_.Manifold.riemannianEDist I p (gamma t))
    simpa only [Function.comp_def, _root_.Manifold.riemannianEDist_comm] using
      ((continuous_riemannianEDist_to (I := I) p).comp
        (intrinsicGeodesic_contMDiff (I := I) g hEnorm o u).continuous).continuousAt
  have hf : ContinuousOn f (_root_.Set.Icc 0 a2) :=
    (Real.continuous_cosh.comp (continuous_const.mul hdist)).continuousOn
  have hsupp : ∀ s ∈ _root_.Set.Ioo 0 a2, ∀ epsilon : ℝ, 0 < epsilon → ∃ psi : ℝ → ℝ,
      ContDiffAt ℝ 2 psi s ∧ psi s = f s ∧
      (∀ᶠ t in 𝓝 s, f t ≤ psi t) ∧ deriv (deriv psi) s ≤ k ^ 2 * f s + epsilon := by
    intro s hs epsilon hepsilon
    obtain ⟨psi, hpsi, hvalue, hupper, hsecond⟩ :=
      cosh_distance_upper_support_of_sectional_lower_bound_on_minimizing_lens
        (I := I) g hEnorm p o u hu hk s (hfin s) (hsec s hs) hepsilon
    exact ⟨psi, hpsi, hvalue, hupper, by rwa [hvalue] at hsecond⟩
  have hzero : f 0 = Real.cosh (k * b) := by
    dsimp [f, gamma, p]
    rw [intrinsicGeodesic_zero, _root_.Manifold.riemannianEDist_comm, hminB]
  have h := Analysis.ODE.hyperbolic_quotient_mono_of_second_deriv_upper_support
    hk (ha1.trans_le ha12) hf hsupp ha1 ha12
  have hdiv := div_le_div_of_nonneg_right h
    ((Real.sinh_pos_iff.mpr (mul_pos hk hb)).le)
  rw [hzero] at hdiv
  dsimp only [hyperbolicComparisonCosine]
  simpa only [div_div, f, gamma, p, _root_.Manifold.riemannianEDist_comm] using hdiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_shorten_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_shorten_first target :: scope.openDecls } }

theorem hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (o : M) (u v : TangentSpace I o) (k a1 a2 b1 b2 : ℝ)
    (hk : 0 < k) (ha1 : 0 < a1) (ha12 : a1 ≤ a2) (hb1 : 0 < b1) (hb12 : b1 ≤ b2)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : (_root_.Manifold.riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o u a2)).toReal = a2)
    (hminB : (_root_.Manifold.riemannianEDist I o (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal = b2)
    (hsec : ∀ s ∈ _root_.Set.Icc (0 : ℝ) a2, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b2, ∀ y : M,
      riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s) y +
        riemannianEDist I y (intrinsicGeodesic (I := I) g hEnorm o v t) =
        riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u s)
          (intrinsicGeodesic (I := I) g hEnorm o v t) →
      SectionalBoundedBelowAt (I := I) g y (-k ^ 2)) :
    hyperbolicComparisonAngle k a2 b2
      (_root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a2)
        (intrinsicGeodesic (I := I) g hEnorm o v b2)).toReal ≤
    hyperbolicComparisonAngle k a1 b1
      (_root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm o u a1)
        (intrinsicGeodesic (I := I) g hEnorm o v b1)).toReal := by
  have hminA1 := unit_intrinsic_subsegment_dist (I := I) g hEnorm o u hu a2 a1
    (ha1.trans_le ha12) ha1.le ha12 hminA
  have hfirst := hyperbolicComparisonCosine_shorten_first (I := I) g hEnorm o u v
    k a1 a2 b2 hk ha1 ha12 (hb1.trans_le hb12) hu hminB (by
      intro s hs y hy
      apply hsec s ⟨hs.1.le, hs.2.le⟩ b2 ⟨(hb1.trans_le hb12).le, le_rfl⟩ y
      simpa only [_root_.Manifold.riemannianEDist_comm, add_comm] using hy)
  have hsecond := hyperbolicComparisonCosine_shorten_first (I := I) g hEnorm o v u
    k b1 b2 a1 hk hb1 hb12 ha1 hv hminA1 (by
      intro t ht y hy
      exact hsec a1 ⟨ha1.le, ha12⟩ t ⟨ht.1.le, ht.2.le⟩ y hy)
  rw [hyperbolicComparisonCosine_comm k b2 a1, hyperbolicComparisonCosine_comm k b1 a1,
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b2),
    riemannianEDist_comm (I := I)
      (x := intrinsicGeodesic (I := I) g hEnorm o v b1)] at hsecond
  exact Real.arccos_le_arccos (hsecond.trans hfirst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_shortening_of_sectional_lower_bound_on_minimizing_lenses

end DifferentialGeometry.Geometry.Comparison.Toponogov
