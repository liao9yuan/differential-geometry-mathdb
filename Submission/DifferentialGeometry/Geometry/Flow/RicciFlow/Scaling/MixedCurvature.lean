import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ParabolicScaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureTerminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedParabolicC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedParabolicC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedParabolicC1 target :: scope.openDecls } }
private local instance mixedParabolicC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedParabolicC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedParabolicC2 target :: scope.openDecls } }

theorem mixedCurvatureTensor_parabolicSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : parabolicTime t₀ Q s ∈ D.regular) (x : M) :
    mixedCurvatureTensor (parabolicSolution S t₀ Q hQ ht₀) p q s x =
      (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x := by
  have hdiff (j : ℕ) (v : ℝ) (hv : v ∈ D.regular) :
      DifferentiableAt ℝ (fun u => mixedCurvatureTensor S p j u x) v := by
    obtain ⟨P, hP⟩ := exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p j
    exact (hP S hS v hv x (Module.finBasis ℝ (TangentSpace I x))).1
  induction q generalizing s with
  | zero =>
      simp only [mixedCurvatureTensor_zero, pow_zero, mul_one]
      rw [parabolicNablaKRm04Field]
      rfl
  | succ q ih =>
      let T := parabolicSolution S t₀ Q hQ ht₀
      let D' := parabolicInterval D t₀ Q ht₀
      have hs' : s ∈ D'.regular := hs
      have heq : (fun u => mixedCurvatureTensor T p q u x) =ᶠ[𝓝 s]
          (fun u => (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q u) x) := by
        filter_upwards [D'.regular_isOpen.mem_nhds hs'] with u hu
        exact ih hu
      have hpoint := ih hs
      have hderiv := (heq.filter_mono (nhdsWithin_le_nhds (s := D'.carrier))).derivWithin_eq hpoint
      change metricTimeDerivWithin T.base.metric D'.carrier
          (fun u => mixedCurvatureTensor T p q u x) s = _
      rw [metricTimeDerivWithin]
      erw [hderiv]
      rw [hpoint]
      change metricTimeDerivWithin
          (fun u => scaleMetric Q hQ (S.base.metric (t₀ + u / Q))) D'.carrier
          (fun u => (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (t₀ + u / Q) x) s = _
      rw [metricTimeDerivWithin_parabolic_of_mapsTo S.base.metric
        (fun u => mixedCurvatureTensor S p q u x) hQ (Q * Q⁻¹ ^ q)
        (show _root_.Set.MapsTo (fun u : ℝ => t₀ + u / Q) D'.carrier D.carrier from fun _ hu => hu)
        (uniqueDiffWithinAt_of_mem_nhds (D'.regular_mem_nhds hs'))
        (hdiff q (parabolicTime t₀ Q s) hs).differentiableWithinAt]
      have hc : (Q * Q⁻¹ ^ q) * Q⁻¹ = Q * Q⁻¹ ^ (q + 1) := by
        rw [pow_succ, mul_assoc]
      rw [hc]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureTensor_parabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureTensor_parabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureTensor_parabolicSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureTensor_parabolicSolution

theorem mixedCurvatureNormSq_parabolicSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : parabolicTime t₀ Q s ∈ D.regular) (x : M) :
    normSq0S (I := I) ((parabolicSolution S t₀ Q hQ ht₀).base.metric s)
        x (4 + p) (mixedCurvatureTensor (parabolicSolution S t₀ Q hQ ht₀) p q s x) =
      Q⁻¹ ^ (2 + p + 2 * q) * normSq0S (I := I) (S.base.metric (parabolicTime t₀ Q s))
        x (4 + p) (mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x) := by
  rw [mixedCurvatureTensor_parabolicSolution S hS t₀ Q hQ ht₀ p q hs x]
  change normSq0S (scaleMetric Q hQ (S.base.metric (parabolicTime t₀ Q s))) x (4 + p)
    ((Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x) = _
  rw [normSq0S_scale, normSq0S_smul, ← mul_assoc]
  congr 1
  have hexp : 4 + p = 2 + (2 + p) := by omega
  calc
    Q⁻¹ ^ (4 + p) * (Q * Q⁻¹ ^ q) ^ 2 =
        (Q⁻¹ ^ 2 * Q ^ 2) * (Q⁻¹ ^ (2 + p) * Q⁻¹ ^ (q * 2)) := by
      rw [hexp, pow_add, mul_pow, pow_mul]
      ring
    _ = Q⁻¹ ^ (2 + p + 2 * q) := by
      rw [← mul_pow, inv_mul_cancel₀ hQ.ne', one_pow, one_mul, ← pow_add]
      congr 1
      omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNormSq_parabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNormSq_parabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNormSq_parabolicSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNormSq_parabolicSolution

theorem mixedCurvatureNorm_parabolicSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : parabolicTime t₀ Q s ∈ D.regular) (x : M) :
    mixedCurvatureNorm (parabolicSolution S t₀ Q hQ ht₀) p q s x =
      Q ^ (-(1 : ℝ) - (p : ℝ) / 2 - (q : ℝ)) *
        mixedCurvatureNorm S p q (parabolicTime t₀ Q s) x := by
  unfold mixedCurvatureNorm
  rw [mixedCurvatureNormSq_parabolicSolution S hS t₀ Q hQ ht₀ p q hs x,
    Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hQ.le) _)]
  congr 1
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (inv_nonneg.mpr hQ.le), ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  push_cast
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm_parabolicSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm_parabolicSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm_parabolicSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm_parabolicSolution

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
