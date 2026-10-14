import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Jacobi
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati.Local

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

omit [SigmaCompactSpace M] in
theorem curveMean_le_on
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
    (hRic : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) ≤
        ricciTensor (I := I) g (γ t)
          (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))
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
    exact (mean_riccati_on (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      (hRic t ht)).1
  have hmle : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) b,
      m' t ≤ (d : ℝ) * (q * a) ^ 2 -
        curveMean (I := I) g γ V t ^ 2 / (d : ℝ) := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_on (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      (hRic t ht)).2
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
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_on ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.curveMean_le_on

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
