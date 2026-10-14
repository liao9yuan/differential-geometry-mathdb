import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeCoefficientContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth
import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance metricCoefficientC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCoefficientC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCoefficientC1 target :: scope.openDecls } }


theorem ancient_metric_hasDerivWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (ht : t ≤ b) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun s => (S.base.metric s).inner x v w)
      (-2 * S.ricciAt t x (vec2 v w)) (_root_.Set.Iic b) t := by
  have hint (s : ℝ) (hs : s < b) :
      HasDerivAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt s x (vec2 v w)) s :=
    metricDerivAt S hS ⟨s, by rwa [hregular]⟩ x v w
  rcases ht.lt_or_eq with htb | htb
  · exact (hint t htb).hasDerivWithinAt
  · subst t
    have hRic : ContinuousOn (fun s => S.ricciAt s x (vec2 v w)) D.carrier := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hS.ricciCont.eval_continuous (P := {s : ℝ // s ∈ D.carrier})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun s => s.2) continuous_const (v := fun i _ => vec2 v w i)
        (fun _ => continuous_const)
    have hb : b ∈ D.carrier := by simp only [hcarrier, _root_.Set.mem_Iic, le_refl]
    have hmetric := hS.smoothMetric.coeff_cont x v w b hb
    have hrhs : ContinuousWithinAt (fun s => -2 * S.ricciAt s x (vec2 v w))
        (_root_.Set.Iio b) b :=
      continuousWithinAt_const.mul ((hRic b hb).mono (by
        rw [hcarrier]; exact _root_.Set.Iio_subset_Iic_self))
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := _root_.Set.Ioo (b - 1) b)
      (fun s hs => (hint s hs.2).differentiableAt.differentiableWithinAt)
      (hmetric.mono (by rw [hcarrier]; exact fun _ hs => hs.2.le))
      (Ioo_mem_nhdsLT (by linarith : b - 1 < b)) ?_
    exact hrhs.tendsto.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT (by linarith : b - 1 < b))
        fun s hs => (hint s hs.2).deriv).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_metric_hasDerivWithinAt

omit [CompleteSpace E] [T2Space M] in
theorem basisInvMetric_hasDerivWithinAt_of_pairings
    {n : ℕ} {x : M} (g : ℝ → SmoothRiemannianMetric I M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (R : Fin n → Fin n → ℝ) {J : Set ℝ} {t : ℝ}
    (hmetric : ∀ i j, HasDerivWithinAt
      (fun s => (g s).inner x (basis i) (basis j)) (-2 * R i j) J t)
    (i j : Fin n) :
    HasDerivWithinAt (fun s => basisInvMetric (I := I) (g s) x basis i j)
      (2 * ∑ a : Fin n, ∑ c : Fin n,
        basisInvMetric (I := I) (g t) x basis i a *
          basisInvMetric (I := I) (g t) x basis j c * R a c) J t := by
  classical
  let metric : ℝ → Fin n → Fin n → ℝ := fun s a c =>
    (g s).inner x (basis a) (basis c)
  let gInv : ℝ → Fin n → Fin n → ℝ :=
    fun s => basisInvMetric (I := I) (g s) x basis
  let G : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fun s => matrixCLM (metric s)
  let Gdot : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := matrixCLM (fun a c => -2 * R a c)
  let InvG : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.inverse (G t)
  let dInv : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := -(InvG * Gdot * InvG)
  have hinv (s : ℝ) := basisInvMetric_isInverse (I := I) (g s) x basis
  have hGInv (s : ℝ) : G s * matrixCLM (gInv s) = ContinuousLinearMap.id ℝ _ := by
    ext v a
    simpa [G, metric, mul_apply_eq_comp] using
      metric_mul_inverse_apply (metric s) (gInv s) (fun p q => (hinv s p q).2) v a
  have hInvG (s : ℝ) : matrixCLM (gInv s) * G s = ContinuousLinearMap.id ℝ _ := by
    ext v a
    simpa [G, metric, mul_apply_eq_comp] using
      inverse_mul_metric_apply (metric s) (gInv s) (fun p q => (hinv s p q).1) v a
  have hGinvertible : (G t).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (hGInv t) (hInvG t)
  have hInverse (s : ℝ) : ContinuousLinearMap.inverse (G s) = matrixCLM (gInv s) :=
    ContinuousLinearMap.inverse_eq (hGInv s) (hInvG s)
  have hG : HasDerivWithinAt G Gdot J t := by
    dsimp only [G, Gdot]
    unfold matrixCLM
    apply HasDerivWithinAt.fun_sum
    intro a _
    apply HasDerivWithinAt.fun_sum
    intro c _
    exact (hmetric a c).smul_const (frameEntryCLM a c)
  have hInv : HasDerivWithinAt
      (fun s => ContinuousLinearMap.inverse (G s)) dInv J t := by
    have hF := (hasFDerivAt_clmInv (G t) hGinvertible).comp_hasFDerivWithinAt
      t hG.hasFDerivWithinAt
    simpa [dInv, InvG, Function.comp_def, ContinuousLinearMap.mulLeftRight_apply]
      using hF.hasDerivWithinAt
  have hApp := hInv.clm_apply
    (hasDerivWithinAt_const t J (Pi.single (M := fun _ : Fin n => ℝ) j 1))
  have hProj := (hasDerivWithinAt_const t J
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)).clm_apply hApp
  have hentry := matrixInvDerivEntry (gInv t) R
    (basisInvMetric_symm (I := I) (g t) x basis) i j
  refine (hProj.congr_deriv ?_).congr ?_ ?_
  · simpa [dInv, InvG, Gdot, hInverse, ContinuousLinearMap.mulLeftRight_apply, gInv]
      using hentry
  · intro s _hs
    rw [hInverse s]
    simp [gInv, sum_mul_pi_single]
  · rw [hInverse t]
    simp [gInv, sum_mul_pi_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.basisInvMetric_hasDerivWithinAt_of_pairings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.basisInvMetric_hasDerivWithinAt_of_pairings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.basisInvMetric_hasDerivWithinAt_of_pairings ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.basisInvMetric_hasDerivWithinAt_of_pairings

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
