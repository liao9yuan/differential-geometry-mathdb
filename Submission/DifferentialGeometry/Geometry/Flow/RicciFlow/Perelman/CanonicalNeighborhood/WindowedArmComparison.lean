import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmNoReturn
import Submission.DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceSectionalBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Topology
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.MetricArmComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Comparison
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

noncomputable def MinimizingArm.scaleMetric
    {g : SmoothRiemannianMetric I3 M} {x : M} (a : MinimizingArm g x)
    (Q : ℝ) (hQ : 0 < Q) : MinimizingArm (DifferentialGeometry.scaleMetric Q hQ g) x where
  length := Real.sqrt Q * a.length
  length_pos := mul_pos (Real.sqrt_pos.mpr hQ) a.length_pos
  point := fun s => a.point (s / Real.sqrt Q)
  start := by rw [zero_div, a.start]
  minimizing := by
    intro s hs t ht
    have hq := Real.sqrt_pos.mpr hQ
    have hs' : s / Real.sqrt Q ∈ _root_.Set.Icc 0 a.length :=
      ⟨div_nonneg hs.1 hq.le, (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hs.2)⟩
    have ht' : t / Real.sqrt Q ∈ _root_.Set.Icc 0 a.length :=
      ⟨div_nonneg ht.1 hq.le, (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using ht.2)⟩
    change (riemannianEDistOf (DifferentialGeometry.scaleMetric _ _ _) _ _).toReal = _
    rw [edistOf_scale, a.edistOf_eq hs' ht', ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal (abs_nonneg _),
      ← sub_div, abs_div, abs_of_pos hq, mul_div_cancel₀ _ hq.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.scaleMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.scaleMetric

theorem MinimizingArm.mem_closedBall_of_distance_add
    {g : SmoothRiemannianMetric I3 M} {x : M} (a b : MinimizingArm g x)
    {s t A : ℝ} (hs : s ∈ _root_.Set.Icc 0 a.length) (ht : t ∈ _root_.Set.Icc 0 b.length)
    (hsA : s ≤ A) (htA : t ≤ A) {y : M}
    (hlens : riemannianEDistOf g (a.point s) y + riemannianEDistOf g y (b.point t) =
      riemannianEDistOf g (a.point s) (b.point t)) :
    y ∈ riemannianClosedBallOf g x (3 * A) := by
  have hA : 0 ≤ A := hs.1.trans hsA
  have hpair : riemannianEDistOf g (a.point s) (b.point t) ≤ ENNReal.ofReal (s + t) := by
    have hh := riemannianEDistOf_triangle g (a.point s) x (b.point t)
    rw [riemannianEDistOf_comm g (a.point s) x, a.edistOf_start hs, b.edistOf_start ht,
      ← ENNReal.ofReal_add hs.1 ht.1] at hh
    exact hh
  have hleg : riemannianEDistOf g (a.point s) y ≤ ENNReal.ofReal (s + t) := by
    calc
      _ ≤ riemannianEDistOf g (a.point s) y + riemannianEDistOf g y (b.point t) := le_self_add
      _ = _ := hlens
      _ ≤ _ := hpair
  change riemannianEDistOf g x y ≤ ENNReal.ofReal (3 * A)
  calc
    _ ≤ riemannianEDistOf g x (a.point s) + riemannianEDistOf g (a.point s) y :=
      riemannianEDistOf_triangle g x (a.point s) y
    _ ≤ ENNReal.ofReal s + ENNReal.ofReal (s + t) := by
      rw [a.edistOf_start hs]
      exact add_le_add_right hleg _
    _ = ENNReal.ofReal (s + (s + t)) := (ENNReal.ofReal_add hs.1 (add_nonneg hs.1 ht.1)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.mem_closedBall_of_distance_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.mem_closedBall_of_distance_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.mem_closedBall_of_distance_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm.mem_closedBall_of_distance_add

theorem SecLower.sectionalBoundedBelowAt_of_minimizingArm_distance_add
    {g : SmoothRiemannianMetric I3 M} {x : M} {c A : ℝ}
    (hsec : SecLower g c (riemannianClosedBallOf g x (3 * A)))
    (a b : MinimizingArm g x) {s t : ℝ}
    (hs : s ∈ _root_.Set.Icc 0 a.length) (ht : t ∈ _root_.Set.Icc 0 b.length) (hsA : s ≤ A) (htA : t ≤ A)
    {y : M} (hlens : riemannianEDistOf g (a.point s) y + riemannianEDistOf g y (b.point t) =
      riemannianEDistOf g (a.point s) (b.point t)) : SectionalBoundedBelowAt g y c := by
  have hball := a.mem_closedBall_of_distance_add b hs ht hsA htA hlens
  intro v w
  exact hsec y hball v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SecLower.sectionalBoundedBelowAt_of_minimizingArm_distance_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SecLower.sectionalBoundedBelowAt_of_minimizingArm_distance_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SecLower.sectionalBoundedBelowAt_of_minimizingArm_distance_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SecLower.sectionalBoundedBelowAt_of_minimizingArm_distance_add

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem tendsto_inverse_sq_mul_max_of_linear_length_bound
    (L : ℕ → Fin 2 → ℝ)
    (hL : ∀ (i : ℕ) (j : Fin 2), L i j ∈ _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) :
    (∀ j, _root_.Filter.Tendsto (fun i => L i j) _root_.Filter.atTop _root_.Filter.atTop) ∧
      Tendsto (fun i : ℕ => (((i : ℝ) + 1)⁻¹ ^ 2) * _root_.Max.max (L i 0) (L i 1)) _root_.Filter.atTop (𝓝 0) := by
  have hn (i : ℕ) : 0 < (i : ℝ) + 1 := by positivity
  have hnat : _root_.Filter.Tendsto (fun i : ℕ => (i : ℝ) + 1) _root_.Filter.atTop atTop :=
    _root_.Filter.tendsto_atTop_mono (fun i : ℕ => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  refine ⟨fun j => _root_.Filter.tendsto_atTop_mono (fun i => (hL i j).1) hnat, ?_⟩
  have hinv : _root_.Filter.Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹) _root_.Filter.atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      _root_.Filter.Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) _root_.Filter.atTop (𝓝 0))
  have hbound (i : ℕ) : ((i : ℝ) + 1)⁻¹ ^ 2 * _root_.Max.max (L i 0) (L i 1) ≤
      2 * ((i : ℝ) + 1)⁻¹ := by
    calc
      _ ≤ ((i : ℝ) + 1)⁻¹ ^ 2 * (2 * ((i : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (max_le (hL i 0).2 (hL i 1).2) (sq_nonneg _)
      _ = _ := by field_simp [(hn i).ne']
  have hh := squeeze_zero (fun i => mul_nonneg (sq_nonneg _)
    ((hn i).le.trans ((hL i 0).1.trans (le_max_left _ _)))) hbound (by simpa only [_root_.MulZeroClass.mul_zero] using hinv.const_mul 2)
  simpa only [_root_.MulZeroClass.mul_zero] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_inverse_sq_mul_max_of_linear_length_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_inverse_sq_mul_max_of_linear_length_bound target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Comparison _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_windowed_tolerances_for_original_arm_lenses :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)] (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)) (kappa : ℝ)
        (x : ∀ i, M i) (t eps : ℕ → ℝ)
        (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
        (∀ i, eps i ≤ delta i) →
        ∀ (arms : ∀ i, Fin 2 → MinimizingArm ((S i).base.metric (t i)) (x i))
          (ell : ℕ → Fin 2 → ℝ),
          (∀ i j, ell i j ∈ _root_.Set.Ioc 0 (arms i j).length) →
          (∀ (i : ℕ) j, Real.sqrt ((S i).scalar (t i) (x i)) * ell i j ∈
            _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) →
          let Q := fun i => (S i).scalar (t i) (x i)
          let g := fun i => scaleMetric (Q i) (W i).scalar_pos ((S i).base.metric (t i))
          let normalized := fun i j => (arms i j).scaleMetric (Q i) (W i).scalar_pos
          let L := fun i j => Real.sqrt (Q i) * ell i j
          _root_.Filter.Tendsto eps _root_.Filter.atTop (𝓝 0) ∧
            (∀ i, IsCompact {z : M i |
              riemannianEDistOf (g i) (x i) z ≤ ENNReal.ofReal (4 * _root_.Max.max (L i 0) (L i 1))}) ∧
            (∀ i s, s ∈ _root_.Set.Icc 0 (L i 0) → ∀ v, v ∈ _root_.Set.Icc 0 (L i 1) → ∀ y : M i,
              riemannianEDistOf (g i) ((normalized i 0).point s) y +
                riemannianEDistOf (g i) y ((normalized i 1).point v) =
                riemannianEDistOf (g i) ((normalized i 0).point s) ((normalized i 1).point v) →
              SectionalBoundedBelowAt (g i) y (-(((i : ℝ) + 1)⁻¹ ^ 2) ^ 2)) ∧
            (∀ j, _root_.Filter.Tendsto (fun i => L i j) _root_.Filter.atTop _root_.Filter.atTop) ∧
            Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹ ^ 2 * _root_.Max.max (L i 0) (L i 1)) _root_.Filter.atTop (𝓝 0) := by
  obtain ⟨delta, hdelta, hzero, hsource⟩ := exists_uniform_windowed_tolerances_for_growing_source_balls.{u}
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ _ D S kappa x t eps W heps arms ell hell hlength
  dsimp only
  obtain ⟨hepsZero, hballs⟩ := hsource M D S kappa x t eps W heps
  let Q := fun i => (S i).scalar (t i) (x i)
  let g := fun i => scaleMetric (Q i) (W i).scalar_pos ((S i).base.metric (t i))
  let normalized := fun i j => (arms i j).scaleMetric (Q i) (W i).scalar_pos
  let L := fun i j => Real.sqrt (Q i) * ell i j
  have hL : ∀ (i : ℕ) j, L i j ∈ _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1)) := hlength
  have hmax (i : ℕ) : _root_.Max.max (L i 0) (L i 1) ≤ 2 * ((i : ℝ) + 1) :=
    max_le (hL i 0).2 (hL i 1).2
  have hball (i : ℕ) : IsCompact (riemannianClosedBallOf (g i) (x i) (8 * ((i : ℝ) + 1))) ∧
      SecLower (g i) (-(((i : ℝ) + 1)⁻¹ ^ 4))
        (riemannianClosedBallOf (g i) (x i) (8 * ((i : ℝ) + 1))) := by
    simpa only [g, Q, rescaledMetric_zero] using hballs i
  obtain ⟨hlong, hsmall⟩ := tendsto_inverse_sq_mul_max_of_linear_length_bound L hL
  refine ⟨hepsZero, ?_, ?_, hlong, hsmall⟩
  · intro i
    exact (hball i).1.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist (g i) (x i)) continuous_const)
      (riemannianClosedBallOf_mono _ _ (by linarith [hmax i]))
  · intro i s hs v hv y hlens
    have hLlength (j : Fin 2) : L i j ≤ (normalized i j).length :=
      mul_le_mul_of_nonneg_left (hell i j).2 (Real.sqrt_nonneg _)
    have hs' : s ∈ _root_.Set.Icc 0 (normalized i 0).length := ⟨hs.1, hs.2.trans (hLlength 0)⟩
    have hv' : v ∈ _root_.Set.Icc 0 (normalized i 1).length := ⟨hv.1, hv.2.trans (hLlength 1)⟩
    have hsec' : SecLower (g i) (-(((i : ℝ) + 1)⁻¹ ^ 2) ^ 2)
        (riemannianClosedBallOf (g i) (x i) (3 * _root_.Max.max (L i 0) (L i 1))) := by
      have hp : (((i : ℝ) + 1)⁻¹ ^ 2) ^ 2 = ((i : ℝ) + 1)⁻¹ ^ 4 := by ring
      rw [hp]
      intro z hz
      exact (hball i).2 z (riemannianClosedBallOf_mono (g i) (x i)
        (show 3 * _root_.Max.max (L i 0) (L i 1) ≤ 8 * ((i : ℝ) + 1) by
          nlinarith [hmax i, (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i)]) hz)
    exact hsec'.sectionalBoundedBelowAt_of_minimizingArm_distance_add
      (normalized i 0) (normalized i 1) hs' hv'
      (hs.2.trans (le_max_left _ _)) (hv.2.trans (le_max_right _ _)) hlens

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_lenses then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_lenses"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_lenses ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_lenses

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_windowed_tolerances_for_original_arm_comparisonAngles :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)] (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)) (kappa : ℝ)
        (x : ∀ i, M i) (t eps : ℕ → ℝ)
        (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
        (∀ i, eps i ≤ delta i) →
        ∀ (arms : ∀ i, Fin 2 → MinimizingArm ((S i).base.metric (t i)) (x i))
          (ell : ℕ → Fin 2 → ℝ),
          (∀ i j, ell i j ∈ _root_.Set.Ioc 0 (arms i j).length) →
          (∀ (i : ℕ) j, Real.sqrt ((S i).scalar (t i) (x i)) * ell i j ∈
            _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) →
          ∀ theta : ℝ, 0 < theta →
            (∀ᶠ i in _root_.Filter.atTop, theta ≤ comparisonAngle (ell i 0) (ell i 1)
              (metricDistance ((S i).base.metric (t i))
                ((arms i 0).point (ell i 0)) ((arms i 1).point (ell i 1)))) →
            ∀ r : ℝ, 0 < r → ∀ᶠ i in _root_.Filter.atTop,
              theta / 2 ≤ comparisonAngle r r
                (metricDistance
                  (rescaledMetric (S i) (t i) ((S i).scalar (t i) (x i)) (W i).scalar_pos 0)
                  ((arms i 0).point (r / Real.sqrt ((S i).scalar (t i) (x i))))
                  ((arms i 1).point (r / Real.sqrt ((S i).scalar (t i) (x i))))) := by
  obtain ⟨delta, hdelta, hzero, hinput⟩ := exists_windowed_tolerances_for_original_arm_lenses.{u}
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ _ D S kappa x t eps W heps arms ell hell hlength theta htheta hangle
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Q := fun i => (S i).scalar (t i) (x i)
  let g := fun i => scaleMetric (Q i) (W i).scalar_pos ((S i).base.metric (t i))
  let normalized := fun i j => (arms i j).scaleMetric (Q i) (W i).scalar_pos
  let L := fun i j => Real.sqrt (Q i) * ell i j
  obtain ⟨_hepsZero, hcompact, hsec, hlong, hsmall⟩ :=
    hinput M D S kappa x t eps W heps arms ell hell hlength
  have hLpos (i : ℕ) (j : Fin 2) : 0 < L i j :=
    mul_pos (Real.sqrt_pos.mpr (W i).scalar_pos) (hell i j).1
  have hLlength (i : ℕ) (j : Fin 2) : L i j ≤ (normalized i j).length :=
    mul_le_mul_of_nonneg_left (hell i j).2 (Real.sqrt_nonneg _)
  have hmetric (i : ℕ) (j : Fin 2) (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 (L i j))
      (v : ℝ) (hv : v ∈ _root_.Set.Icc 0 (L i j)) :
      riemannianEDistOf (g i) ((normalized i j).point s) ((normalized i j).point v) =
        ENNReal.ofReal |s - v| :=
    (normalized i j).edistOf_eq ⟨hs.1, hs.2.trans (hLlength i j)⟩
      ⟨hv.1, hv.2.trans (hLlength i j)⟩
  have hend (i : ℕ) (j : Fin 2) : (normalized i j).point (L i j) = (arms i j).point (ell i j) := by
    change (arms i j).point ((Real.sqrt (Q i) * ell i j) / Real.sqrt (Q i)) = _
    rw [mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (W i).scalar_pos).ne']
  have hdist (i : ℕ) (y z : M i) : metricDistance (g i) y z =
      Real.sqrt (Q i) * metricDistance ((S i).base.metric (t i)) y z := by
    simp only [g, metricDistance, edistOf_scale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hangleNorm : ∀ᶠ i in _root_.Filter.atTop, theta ≤ comparisonAngle (L i 0) (L i 1)
      (riemannianEDistOf (g i) ((normalized i 0).point (L i 0))
        ((normalized i 1).point (L i 1))).toReal := by
    filter_upwards [hangle] with i hi
    change theta ≤ comparisonAngle (L i 0) (L i 1)
      (metricDistance (g i) ((normalized i 0).point (L i 0)) ((normalized i 1).point (L i 1)))
    rw [hend, hend, hdist]
    dsimp only [L]
    rw [comparisonAngle_scale _ _ _ (Real.sqrt_pos.mpr (W i).scalar_pos)]
    exact hi
  have hh := eventually_comparisonAngle_ge_half_of_sectional_lower_bound_on_minimizing_lenses
    (I := I3) g x (fun i j => (normalized i j).point) L
    (fun i : ℕ => ((i : ℝ) + 1)⁻¹ ^ 2) (fun i => by positivity) hLpos
    (fun i j => (normalized i j).start) hmetric hcompact hsec hlong hsmall htheta hangleNorm
  intro r hr
  simpa only [normalized, MinimizingArm.scaleMetric, g, Q, rescaledMetric_zero, metricDistance] using hh r hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_comparisonAngles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_comparisonAngles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_comparisonAngles ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_comparisonAngles

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end
