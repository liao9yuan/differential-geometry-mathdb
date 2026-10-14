import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.FarTriangleAngles
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingRay
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_ratios_of_fast_positive_growth {D : ℕ → ℝ}
    (hpositive : ∀ n, 1 ≤ D n)
    (hgrowth : ∀ n : ℕ, ((n : ℝ) + 2) * D n ≤ D (n + 1)) :
    _root_.Filter.Tendsto (fun n => D (n + 1) / D n) _root_.Filter.atTop _root_.Filter.atTop ∧
      Tendsto (fun n => D n / D (n + 1)) _root_.Filter.atTop (𝓝 0) := by
  have hnat : _root_.Filter.Tendsto (fun n : ℕ => (n : ℝ)) _root_.Filter.atTop atTop := tendsto_natCast_atTop_atTop
  have hle (n : ℕ) : (n : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hlinear : _root_.Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) _root_.Filter.atTop atTop :=
    _root_.Filter.tendsto_atTop_mono hle hnat
  have hforward : _root_.Filter.Tendsto (fun n => D (n + 1) / D n) _root_.Filter.atTop atTop := by
    apply _root_.Filter.tendsto_atTop_mono _ hlinear
    intro n
    have hpos : 0 < D n := by linarith [hpositive n]
    exact (le_div_iff₀ hpos).2 (hgrowth n)
  refine ⟨hforward, ?_⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hforward

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_ratios_of_fast_positive_growth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_ratios_of_fast_positive_growth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_ratios_of_fast_positive_growth ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_ratios_of_fast_positive_growth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

omit [ConnectedSpace M] in
theorem exists_unit_intrinsic_vector_of_pos_distance
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hd : 0 < (_root_.Manifold.riemannianEDist I p q).toReal) :
    ∃ w : TangentSpace I p, g.inner p w w = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm p w (_root_.Manifold.riemannianEDist I p q).toReal = q := by
  obtain ⟨v, hvend, hvlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q
    (by
      intro htop
      rw [htop, ENNReal.toReal_top] at hd
      exact lt_irrefl 0 hd)
  let d : ℝ := (_root_.Manifold.riemannianEDist I p q).toReal
  let w : TangentSpace I p := d⁻¹ • v
  have hdpos : 0 < d := hd
  have hvnorm : g.inner p v v = d ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hvlen]
  have hwunit : g.inner p w w = 1 := by
    dsimp only [w]
    rw [gInner_smul_self (I := I) g p d⁻¹ v, hvnorm, ← mul_pow,
      inv_mul_cancel₀ hdpos.ne', one_pow]
  have hsmul : d • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
  refine ⟨w, hwunit, ?_⟩
  calc
    intrinsicGeodesic (I := I) g hEnorm p w d =
        expMapIntrinsic (I := I) g hEnorm p (d • w) :=
      (intrinsicGeodesic_smul (I := I) g hEnorm p w d).symm
    _ = q := by rw [hsmul, hvend]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_unit_intrinsic_vector_of_pos_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.exists_unit_intrinsic_vector_of_pos_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_unit_intrinsic_vector_of_pos_distance ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.exists_unit_intrinsic_vector_of_pos_distance

omit [ConnectedSpace M] in
theorem exists_convergent_fast_radial_arms
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ)
    (hescape : _root_.Filter.Tendsto (fun i => (_root_.Manifold.riemannianEDist I p (x i)).toReal) _root_.Filter.atTop _root_.Filter.atTop)
    (hscaled : _root_.Filter.Tendsto (fun i => lam i * (_root_.Manifold.riemannianEDist I p (x i)).toReal)
      _root_.Filter.atTop _root_.Filter.atTop) :
    let D : ℕ → ℝ := fun i => (_root_.Manifold.riemannianEDist I p (x i)).toReal
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ (u : TangentSpace I p) (v : ℕ → TangentSpace I p),
        g.inner p u u = 1 ∧ (∀ n, g.inner p (v n) (v n) = 1) ∧
        _root_.Filter.Tendsto v _root_.Filter.atTop (𝓝 u) ∧
        (∀ n, intrinsicGeodesic (I := I) g hEnorm p (v n) (D (phi n)) = x (phi n)) ∧
        (∀ n, 1 ≤ D (phi n)) ∧
        (∀ n : ℕ, ((n : ℝ) + 2) * D (phi n) ≤ D (phi (n + 1))) ∧
        _root_.Filter.Tendsto (fun n => D (phi (n + 1)) / D (phi n)) _root_.Filter.atTop _root_.Filter.atTop ∧
        _root_.Filter.Tendsto (fun n => D (phi n) / D (phi (n + 1))) _root_.Filter.atTop (𝓝 0) ∧
        _root_.Filter.Tendsto (fun n => lam (phi n) * D (phi n)) _root_.Filter.atTop _root_.Filter.atTop ∧
        ∀ L : ℝ, 0 ≤ L → _root_.Manifold.riemannianEDist I p
          (intrinsicGeodesic (I := I) g hEnorm p u L) = ENNReal.ofReal L := by
  dsimp only
  let D : ℕ → ℝ := fun i => (_root_.Manifold.riemannianEDist I p (x i)).toReal
  have hD : _root_.Filter.Tendsto D _root_.Filter.atTop atTop := hescape
  obtain ⟨chi, hchi, hchiPos, _⟩ := exists_fast_positive_subsequence hD
  have hnormalized : ∀ n, ∃ w : TangentSpace I p, g.inner p w w = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm p w (D (chi n)) = x (chi n) := by
    intro n
    apply exists_unit_intrinsic_vector_of_pos_distance (I := I) g hEnorm p (x (chi n))
    change 0 < D (chi n)
    linarith [hchiPos n]
  choose w hwunit hwend using hnormalized
  obtain ⟨u, hu, psi, hpsi, hlim⟩ :=
    (gUnitSphere_isCompact (I := I) g p).tendsto_subseq hwunit
  let D2 : ℕ → ℝ := fun n => D (chi (psi n))
  have hD2 : _root_.Filter.Tendsto D2 _root_.Filter.atTop atTop := hD.comp (hchi.comp hpsi).tendsto_atTop
  obtain ⟨tau, htau, htauPos, htauGrowth⟩ := exists_fast_positive_subsequence hD2
  let phi : ℕ → ℕ := fun n => chi (psi (tau n))
  let v : ℕ → TangentSpace I p := fun n => w (psi (tau n))
  have hphi : StrictMono phi := hchi.comp (hpsi.comp htau)
  have hvunit (n : ℕ) : g.inner p (v n) (v n) = 1 := hwunit (psi (tau n))
  have hvconv : _root_.Filter.Tendsto v _root_.Filter.atTop (𝓝 u) := hlim.comp htau.tendsto_atTop
  have hvend (n : ℕ) :
      intrinsicGeodesic (I := I) g hEnorm p (v n) (D (phi n)) = x (phi n) :=
    hwend (psi (tau n))
  have hpositive (n : ℕ) : 1 ≤ D (phi n) := htauPos n
  have hgrowth (n : ℕ) : ((n : ℝ) + 2) * D (phi n) ≤ D (phi (n + 1)) := htauGrowth n
  have hratios := tendsto_ratios_of_fast_positive_growth hpositive hgrowth
  have hselectedScaled : _root_.Filter.Tendsto (fun n => lam (phi n) * D (phi n)) _root_.Filter.atTop atTop :=
    hscaled.comp hphi.tendsto_atTop
  have hmin (n : ℕ) : (_root_.Manifold.riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (D (phi n)))).toReal = D (phi n) := by
    rw [hvend]
  have hselectedPos (n : ℕ) : 0 < D (phi n) := by linarith [hpositive n]
  refine ⟨phi, hphi, u, v, hu, hvunit, hvconv, hvend, hpositive, hgrowth,
    hratios.1, hratios.2, hselectedScaled, ?_⟩
  exact minimizing_ray_of_tendsto_unit_vectors (I := I) g hEnorm p v
    (fun n => D (phi n)) u hvunit hselectedPos hmin (hD.comp hphi.tendsto_atTop) hvconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_convergent_fast_radial_arms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.exists_convergent_fast_radial_arms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_convergent_fast_radial_arms ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.exists_convergent_fast_radial_arms

end DifferentialGeometry.Geometry.Comparison.Toponogov
