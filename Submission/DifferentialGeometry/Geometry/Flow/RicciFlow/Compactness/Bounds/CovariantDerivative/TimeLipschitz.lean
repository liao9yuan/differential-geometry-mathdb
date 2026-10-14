import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance uniformLocalEvolutionC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformLocalEvolutionC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.uniformLocalEvolutionC1 target :: scope.openDecls } }
private local instance uniformLocalEvolutionC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformLocalEvolutionC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.uniformLocalEvolutionC2 target :: scope.openDecls } }

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem exists_metric_time_lipschitz_constant_of_local_evolution
    {U : Set M} (hU : IsOpen U)
    (gRef : SmoothRiemannianMetric I M) {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ) (C : ℕ → ℝ) {KShi : ℝ} (hKShi : 0 ≤ KShi) :
    ∀ q ≤ N, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ},
        (∀ t ∈ Set.Ico a b, MetricUniformEquivalentOn (I := I) U gRef (g t) B) →
        (∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
          metricCovDerivNorm (I := I) r (g t) gRef x ≤ C r) →
        (∀ ψ ∈ Set.Ico a b,
          MovingShiBoundOn (I := I) U a ψ (fun _ t => g t) N KShi) →
        (∀ t ∈ Set.Ico a b, ∀ x ∈ U, ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt (fun s => metricCovDeriv (I := I) (g s) gRef q x v)
            (((-2 : ℝ) • nablaRicReal (I := I) (fun _ s => g s) gRef q 0 t x) v) t) →
        ∀ s ∈ Set.Ico a b, ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
          metricDerivNorm (I := I) q (g s) (g t) gRef x ≤ L * |s - t| := by
  intro q hq
  have hric : ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ},
        (∀ t ∈ Set.Ico a b, MetricUniformEquivalentOn (I := I) U gRef (g t) B) →
        (∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
          metricCovDerivNorm (I := I) r (g t) gRef x ≤ C r) →
        (∀ ψ ∈ Set.Ico a b,
          MovingShiBoundOn (I := I) U a ψ (fun _ t => g t) N KShi) →
        ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
          Real.sqrt (normSq0S (I := I) gRef x (q + 2)
            ((-2 : ℝ) • nablaRicReal (I := I) (fun _ t => g t) gRef q 0 t x)) ≤ L := by
    by_cases hzero : q = 0
    · subst q
      refine ⟨2 * (Real.sqrt (B ^ 2) * KShi), by positivity, ?_⟩
      intro g a b heq _ hShi t ht x hx
      have hsym := metricUniformEquivalentOn_symm (I := I) (heq t ht)
      have hcomp := sqrt_normSq0S_le_of_metric_equiv (I := I)
        (g := g t) (h := gRef) x 2 hB
        (fun v => hsym.2 x hx v)
        (ricCovTower (I := I) (g t) gRef 0 x)
      have hmove := hShi t ht 0 (Nat.zero_le N) 0 t ⟨ht.1, le_rfl⟩ x hx
      rw [sqrt_normSq0S_smul, nablaRicReal_normSq]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left
        (hcomp.trans (mul_le_mul_of_nonneg_left hmove (Real.sqrt_nonneg _))) (by norm_num)
    · let coeff := ricTowerCoeffs (Module.finrank ℝ E) q B C KShi
      have hcoeff := ricCoeffs_nonneg (Module.finrank ℝ E) q B C KShi hB hKShi
      have hA : 0 ≤ coeff.slope := hcoeff.1
      have hB₀ : 0 ≤ coeff.offset := hcoeff.2
      refine ⟨2 * (coeff.slope * _root_.Max.max (C q) 0 + coeff.offset), by positivity, ?_⟩
      intro g a b heq hC hShi t ht x hx
      have hb := ric_bound_field_on (I := I) (gRef := gRef)
        (β := a) (ψ := t) (gSeq := fun _ t => g t) hU q (by omega) B hB
        (fun _ r hr => heq r ⟨hr.1, hr.2.trans_lt ht.2⟩) C
        (fun r h1 hr _ s hs y hy => hC r h1 (by omega) s
          ⟨hs.1, hs.2.trans_lt ht.2⟩ y hy) KShi hKShi
        (fun r hr => hShi t ht r (hr.trans hq)) 0 t ⟨ht.1, le_rfl⟩ x hx
      rw [sqrt_normSq0S_smul]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left
        (hb.trans (add_le_add (mul_le_mul_of_nonneg_left
          ((hC q (by omega) hq t ht x hx).trans (le_max_left _ _)) hA) le_rfl)) (by norm_num)
  obtain ⟨L, hL, hric⟩ := hric
  refine ⟨L, hL, ?_⟩
  intro g a b heq hC hShi hev s hs t ht x hx
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I M := fun _ t => g t
  let ψ := _root_.Max.max s t
  have hψ : ψ ∈ Set.Ico a b := ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩
  exact timeLipschitz_of_hasDerivAt (I := I) gRef q (fun r => g r)
    (fun r y => (-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q 0 r y) U a ψ L
    (fun y hy r hr => hev r ⟨hr.1, hr.2.trans_lt hψ.2⟩ y hy)
    (fun y hy r hr => hric g heq hC hShi r ⟨hr.1, hr.2.trans_lt hψ.2⟩ y hy)
    s ⟨hs.1, le_max_left _ _⟩ t ⟨ht.1, le_max_right _ _⟩ x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_metric_time_lipschitz_constant_of_local_evolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_metric_time_lipschitz_constant_of_local_evolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_metric_time_lipschitz_constant_of_local_evolution ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_metric_time_lipschitz_constant_of_local_evolution


end DifferentialGeometry.PDE.RicciFlow
