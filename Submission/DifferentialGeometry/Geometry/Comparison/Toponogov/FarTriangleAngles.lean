import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonTriangleLimit

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

theorem exists_fast_positive_subsequence {D : ℕ → ℝ} (hD : _root_.Filter.Tendsto D _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ (∀ n, 1 ≤ D (phi n)) ∧
      ∀ n : ℕ, ((n : ℝ) + 2) * D (phi n) ≤ D (phi (n + 1)) := by
  have hex (n k : ℕ) : ∃ j : ℕ, k < j ∧ 1 ≤ D j ∧
      ((n : ℝ) + 2) * D k ≤ D j := by
    have hevent : ∀ᶠ j in _root_.Filter.atTop, k < j ∧ 1 ≤ D j ∧
        ((n : ℝ) + 2) * D k ≤ D j := by
      filter_upwards [_root_.Filter.eventually_gt_atTop k, hD (_root_.Filter.eventually_ge_atTop 1),
        hD (_root_.Filter.eventually_ge_atTop (((n : ℝ) + 2) * D k))] with j hj hOne hGrow
      exact ⟨hj, hOne, hGrow⟩
    exact hevent.exists
  choose next hnext using hex
  have hfirst : ∀ᶠ n in _root_.Filter.atTop, (1 : ℝ) ≤ D n := hD (_root_.Filter.eventually_ge_atTop 1)
  obtain ⟨k0, hk0⟩ := hfirst.exists
  let phi : ℕ → ℕ := fun n => Nat.rec k0 (fun m k => next m k) n
  have hstep (n : ℕ) : phi (n + 1) = next n (phi n) := rfl
  have hmono : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hstep]
    exact (hnext n (phi n)).1
  have hpos : ∀ n, 1 ≤ D (phi n) := by
    intro n
    cases n with
    | zero => exact hk0
    | succ n =>
      rw [hstep]
      exact (hnext n (phi n)).2.1
  refine ⟨phi, hmono, hpos, ?_⟩
  intro n
  rw [hstep]
  exact (hnext n (phi n)).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_fast_positive_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.exists_fast_positive_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_fast_positive_subsequence ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.exists_fast_positive_subsequence

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

theorem tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (u : TangentSpace I p) (w v : ℕ → TangentSpace I p) (a b : ℕ → ℝ)
    (hunit : g.inner p u u = 1)
    (hwunit : ∀ i, g.inner p (w i) (w i) = 1)
    (hvunit : ∀ i, g.inner p (v i) (v i) = 1)
    (hwconv : _root_.Filter.Tendsto w _root_.Filter.atTop (𝓝 u)) (hvconv : _root_.Filter.Tendsto v _root_.Filter.atTop (𝓝 u))
    (ha : ∀ i, 0 < a i) (hseparated : ∀ i, 2 * a i ≤ b i)
    (hminA : ∀ i, (_root_.Manifold.riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (w i) (a i))).toReal = a i)
    (hminB : ∀ i, (_root_.Manifold.riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v i) (b i))).toReal = b i)
    (hratio : _root_.Filter.Tendsto (fun i => a i / b i) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => comparisonAngle (a i)
      (_root_.Manifold.riemannianEDist I
        (intrinsicGeodesic (I := I) g hEnorm p (w i) (a i))
        (intrinsicGeodesic (I := I) g hEnorm p (v i) (b i))).toReal
      (b i)) _root_.Filter.atTop (𝓝 Real.pi) := by
  let alpha : ℕ → M := fun i => intrinsicGeodesic (I := I) g hEnorm p (w i) (a i)
  let beta : ℕ → M := fun i => intrinsicGeodesic (I := I) g hEnorm p (v i) (b i)
  let c : ℕ → ℝ := fun i => (_root_.Manifold.riemannianEDist I (alpha i) (beta i)).toReal
  have hradA (i : ℕ) : (_root_.Manifold.riemannianEDist I p (alpha i)).toReal = a i := hminA i
  have hradB (i : ℕ) : (_root_.Manifold.riemannianEDist I p (beta i)).toReal = b i := hminB i
  have hb (i : ℕ) : 0 < b i := by linarith [ha i, hseparated i]
  have htri (x y z : M) : (_root_.Manifold.riemannianEDist I x z).toReal ≤
      (_root_.Manifold.riemannianEDist I x y).toReal + (_root_.Manifold.riemannianEDist I y z).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) x y,
        riemannianEDist_ne_top (I := I) y z⟩)
      (_root_.Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z))
    simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) x y)
      (riemannianEDist_ne_top (I := I) y z)] using h
  have hlower (i : ℕ) : |a i - b i| ≤ c i := by
    have h1 := htri p (alpha i) (beta i)
    have h2 := htri p (beta i) (alpha i)
    rw [hradA, hradB] at h1 h2
    rw [_root_.Manifold.riemannianEDist_comm (I := I) (x := beta i) (y := alpha i)] at h2
    change b i ≤ a i + c i at h1
    change a i ≤ b i + c i at h2
    apply abs_le.mpr
    constructor <;> linarith
  have hupper (i : ℕ) : c i ≤ a i + b i := by
    have h := htri (alpha i) p (beta i)
    rw [_root_.Manifold.riemannianEDist_comm (I := I) (x := alpha i) (y := p), hradA, hradB] at h
    exact h
  have hc (i : ℕ) : 0 < c i := by
    have hba : b i - a i ≤ c i := by
      have h := neg_le_abs (a i - b i)
      linarith [hlower i]
    linarith [ha i, hseparated i]
  have hinnerContinuous : Continuous
      (fun z : TangentSpace I p × TangentSpace I p => g.inner p z.1 z.2) :=
    ((g.inner p).continuous.comp continuous_fst).clm_apply continuous_snd
  have hinner : _root_.Filter.Tendsto (fun i => g.inner p (w i) (v i)) _root_.Filter.atTop (𝓝 1) := by
    simpa only [Function.comp_def, hunit] using
      (hinnerContinuous.tendsto (u, u)).comp (hwconv.prodMk_nhds hvconv)
  have hactual : _root_.Filter.Tendsto (fun i => Real.arccos (g.inner p (w i) (v i)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.arccos_one] using
      Real.continuous_arccos.continuousAt.tendsto.comp hinner
  have hbase : _root_.Filter.Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) _root_.Filter.atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hactual
    · intro i
      exact (comparisonAngle_mem_Icc (a i) (b i) (c i)).1
    · intro i
      have h := complete_triangle_angle (I := I) g hEnorm hsec p (w i) (v i)
        (a i) (b i) (ha i) (hb i) (hwunit i) (hvunit i) (hminA i) (hminB i)
      rw [hminA i, hminB i] at h
      exact h
  exact tendsto_comparisonAngle_pi_of_tendsto_zero ha hb hc hlower hupper hratio hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_far_comparisonAngle_pi_of_convergent_initial_vectors

end DifferentialGeometry.Geometry.Comparison.Toponogov
