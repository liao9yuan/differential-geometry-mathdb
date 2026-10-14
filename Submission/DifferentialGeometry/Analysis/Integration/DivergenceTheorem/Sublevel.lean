import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem integral_laplacian_nonneg_on_lt_sublevel_of_compact
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (t : Real)
    (hcompact : IsCompact {x : M | f x ≤ t}) :
    0 ≤ ∫ x in {x : M | f x < t},
      ΔG (I := I) g f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let mu : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let K : Set M := {x : M | f x ≤ t}
  let U : Set M := {x : M | f x < t}
  let a : Nat → Real := fun n => n + 1
  let u : Nat → M → Real := fun n x => 2 + a n * (f x - t)
  let chi : Nat → M → Real := fun n x => CutoffProfile.value (u n x)
  have ha_pos (n : Nat) : 0 < a n := by
    dsimp only [a]
    positivity
  have hu_smooth (n : Nat) : ContMDiff I 𝓘(Real) ∞ (u n) := by
    dsimp only [u, a]
    exact contMDiff_const.add
      (contMDiff_const.mul (f.contMDiff.sub contMDiff_const))
  have hchi_smooth (n : Nat) : ContMDiff I 𝓘(Real) ∞ (chi n) := by
    exact CutoffProfile.contDiff.comp_contMDiff (hu_smooth n)
  have hchi_range (n : Nat) (x : M) : chi n x ∈ Set.Icc (0 : Real) 1 :=
    CutoffProfile.mem_Icc _
  have hchi_zero (n : Nat) {x : M} (hx : t ≤ f x) : chi n x = 0 := by
    apply CutoffProfile.zero_of_two_le
    dsimp only [chi, u]
    nlinarith [ha_pos n]
  have hchi_support (n : Nat) : Function.support (chi n) ⊆ U := by
    intro x hx
    change f x < t
    by_contra hnot
    exact hx (hchi_zero n (le_of_not_gt hnot))
  have hchi_cs (n : Nat) : HasCompactSupport (chi n) := by
    refine HasCompactSupport.of_support_subset_isCompact hcompact ?_
    intro x hx
    have hxU := hchi_support n hx
    change f x < t at hxU
    exact hxU.le
  let X : Nat → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun n =>
    smoothSmul (I := I) (chi n) (hchi_smooth n) (gradG (I := I) g f)
  have hX_cs (n : Nat) : HasCompactSupport (X n) := by
    refine HasCompactSupport.of_support_subset_isCompact (hchi_cs n : IsCompact (tsupport (chi n))) ?_
    intro x hx
    apply subset_tsupport
    intro hzero
    apply hx
    change chi n x • gradFun (I := I) g f x = 0
    rw [hzero, zero_smul]
  have hgrad_chi (n : Nat) (x : M) :
      gradFun (I := I) g (chi n) x =
        (deriv CutoffProfile.value (u n x) * a n) •
          gradFun (I := I) g f x := by
    let affine : Real → Real := fun s => 2 + a n * (s - t)
    let profile : Real → Real := fun s => CutoffProfile.value (affine s)
    have haffine : HasDerivAt affine (a n) (f x) := by
      have h := (hasDerivAt_const (f x) (2 : Real)).add
        ((hasDerivAt_const (f x) (a n)).mul
          ((hasDerivAt_id (f x)).sub_const t))
      exact (h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
    have hvalue : HasDerivAt CutoffProfile.value
        (deriv CutoffProfile.value (affine (f x))) (affine (f x)) :=
      (CutoffProfile.contDiff.differentiable (by simp) _).hasDerivAt
    have hprofile : HasDerivAt profile
        (deriv CutoffProfile.value (affine (f x)) * a n) (f x) := by
      exact (hvalue.comp (f x) haffine).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    have hgradient := gradFun_comp (I := I) g hprofile.differentiableAt
      (f.contMDiff.mdifferentiable (by simp) x)
    have hfun : chi n = fun y => profile (f y) := by
      rfl
    rw [hfun]
    simpa only [profile, affine, u, hprofile.deriv] using hgradient
  have haction_nonpos (n : Nat) (x : M) :
      tangentSectionAction (I := I) (gradG (I := I) g f) (chi n) x ≤ 0 := by
    rw [tangentSectionAction_def]
    rw [grad_g_apply]
    rw [← inner_gradFun_right (I := I) g (chi n) x (gradFun (I := I) g f x)]
    rw [hgrad_chi]
    rw [map_smul, smul_eq_mul]
    have hnorm : 0 ≤ g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x) := by
      let v : TangentSpace I x := gradFun (I := I) g f x
      change 0 ≤ g.inner x v v
      by_cases hv : v = 0
      · rw [hv]
        simp
      · exact (g.pos x v hv).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (CutoffProfile.deriv_nonpos _) (ha_pos n).le)
      hnorm
  have hweighted_nonneg (n : Nat) :
      0 ≤ ∫ x, chi n x * ΔG (I := I) g f x ∂mu := by
    have hdiv := integral_divergence_eq_zero_of_hasCompactSupport
      (I := I) g (X n) (hX_cs n)
    have hpoint (x : M) :
        divergenceG (I := I) g (X n) x =
          chi n x * ΔG (I := I) g f x +
            tangentSectionAction (I := I) (gradG (I := I) g f) (chi n) x := by
      exact divergence_g_smoothSmul (I := I) g (chi n) (hchi_smooth n)
        (gradG (I := I) g f) x
    have hmul_cont : Continuous (fun x : M => chi n x * ΔG (I := I) g f x) :=
      (hchi_smooth n).continuous.mul (Δ_g_contMDiff (I := I) g f).continuous
    have hmul_cs : HasCompactSupport (fun x : M => chi n x * ΔG (I := I) g f x) :=
      (hchi_cs n).mul_right
    have hact_cont : Continuous
        (tangentSectionAction (I := I) (gradG (I := I) g f) (chi n)) :=
      (tangentSectionAction_contMDiff (I := I) (gradG (I := I) g f)
        (hchi_smooth n)).continuous
    have hact_cs : HasCompactSupport
        (tangentSectionAction (I := I) (gradG (I := I) g f) (chi n)) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (hchi_cs n : IsCompact (tsupport (chi n))) ?_
      intro x hx
      by_contra hxnot
      apply hx
      have heq : chi n =ᶠ[𝓝 x] fun _ : M => (0 : Real) := by
        filter_upwards [(isClosed_tsupport (chi n)).isOpen_compl.mem_nhds hxnot] with y hy
        exact Function.notMem_support.mp (fun h => hy (subset_tsupport _ h))
      rw [tangentSectionAction_def, heq.mfderiv_eq, mfderiv_const]
      rfl
    have hmul_int : _root_.MeasureTheory.Integrable (fun x : M => chi n x * ΔG (I := I) g f x) mu :=
      Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g hmul_cont hmul_cs
    have hact_int : _root_.MeasureTheory.Integrable
        (tangentSectionAction (I := I) (gradG (I := I) g f) (chi n)) mu :=
      Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g hact_cont hact_cs
    have hsum :
        (∫ x, chi n x * ΔG (I := I) g f x ∂mu) +
          ∫ x, tangentSectionAction (I := I) (gradG (I := I) g f) (chi n) x ∂mu = 0 := by
      rw [← _root_.MeasureTheory.integral_add hmul_int hact_int]
      rw [← _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      exact hdiv
    have hact_le :
        ∫ x, tangentSectionAction (I := I) (gradG (I := I) g f) (chi n) x ∂mu ≤ 0 :=
      _root_.MeasureTheory.integral_nonpos (haction_nonpos n)
    linarith
  have hmu_finite : _root_.MeasureTheory.IsFiniteMeasureOnCompacts mu :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  let _ : _root_.MeasureTheory.IsFiniteMeasureOnCompacts mu := hmu_finite
  let lap : M → Real := ΔG (I := I) g f
  let bound : M → Real := K.indicator fun x => |lap x|
  have hbound_int : _root_.MeasureTheory.Integrable bound mu := by
    apply IntegrableOn.integrable_indicator
    · exact ((Δ_g_contMDiff (I := I) g f).continuous.abs.continuousOn.integrableOn_compact
        hcompact)
    · exact hcompact.measurableSet
  have hF_meas : ∀ n : Nat, _root_.MeasureTheory.AEStronglyMeasurable (fun x => chi n x * lap x) mu := by
    intro n
    exact ((hchi_smooth n).continuous.mul
      (Δ_g_contMDiff (I := I) g f).continuous).aestronglyMeasurable
  have hF_bound : ∀ n : Nat, ∀ x : M, ‖chi n x * lap x‖ ≤ bound x := by
    intro n x
    by_cases hx : x ∈ K
    · rw [show bound x = |lap x| by simp [bound, hx]]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (by
        rw [abs_of_nonneg (hchi_range n x).1]
        exact (hchi_range n x).2)
    · have htx : t < f x := lt_of_not_ge hx
      rw [hchi_zero n htx.le]
      simp [bound, hx]
  have hlimit (x : M) : _root_.Filter.Tendsto (fun n : Nat => chi n x * lap x) _root_.Filter.atTop
      (nhds (U.indicator lap x)) := by
    by_cases hx : x ∈ U
    · have hcoeff : _root_.Filter.Tendsto a _root_.Filter.atTop atTop := by
        simpa only [a, Nat.cast_add, Nat.cast_one] using
          _root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop (1 : Real) tendsto_natCast_atTop_atTop
      have harg : _root_.Filter.Tendsto (fun n : Nat => u n x) _root_.Filter.atTop atBot := by
        dsimp only [u]
        exact _root_.Filter.tendsto_atBot_add_const_left _root_.Filter.atTop 2
          (hcoeff.atTop_mul_const_of_neg (sub_neg.mpr hx))
      have hev : ∀ᶠ n : Nat in _root_.Filter.atTop, u n x ≤ 1 :=
        (tendsto_atBot.1 harg 1)
      have hchi_one : (fun n : Nat => chi n x) =ᶠ[_root_.Filter.atTop] fun _ => (1 : Real) := by
        filter_upwards [hev] with n hn
        exact CutoffProfile.one_of_le_one hn
      have hprod : (fun n : Nat => chi n x * lap x) =ᶠ[_root_.Filter.atTop]
          fun _ => lap x := by
        filter_upwards [hchi_one] with n hn
        rw [hn, one_mul]
      rw [Set.indicator_of_mem hx]
      exact tendsto_const_nhds.congr' hprod.symm
    · have htx : t ≤ f x := le_of_not_gt hx
      have hzero : ∀ n : Nat, chi n x * lap x = 0 := by
        intro n
        rw [hchi_zero n htx, _root_.MulZeroClass.zero_mul]
      rw [Set.indicator_of_notMem hx]
      simpa only [hzero] using (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : Nat => (0 : Real)) _root_.Filter.atTop (nhds 0))
  have htendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := _root_.Filter.atTop) (μ := mu) (F := fun n x => chi n x * lap x)
    (f := U.indicator lap) (bound := bound)
    (Filter.Eventually.of_forall hF_meas)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hF_bound n))
    hbound_int (Filter.Eventually.of_forall hlimit)
  have hlim_nonneg : 0 ≤ ∫ x, U.indicator lap x ∂mu :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htendsto
      (Filter.Eventually.of_forall hweighted_nonneg)
  have hUmeas : MeasurableSet U := by
    exact (isOpen_lt f.contMDiff.continuous continuous_const).measurableSet
  simpa only [MeasureTheory.integral_indicator hUmeas, lap, U, mu] using hlim_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.integral_laplacian_nonneg_on_lt_sublevel_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.integral_laplacian_nonneg_on_lt_sublevel_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.integral_laplacian_nonneg_on_lt_sublevel_of_compact ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.integral_laplacian_nonneg_on_lt_sublevel_of_compact

end DifferentialGeometry.Integral.DivergenceTheorem
