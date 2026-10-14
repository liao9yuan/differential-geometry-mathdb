import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Semicontinuity.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

noncomputable def timeQuad
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeL2 X T) : ℝ :=
  _root_.Inner.inner ℝ (timeOp A hA C hC u) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad

omit [CompleteSpace X] in
theorem timeQuad_int
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hT : 0 ≤ T)
    (u : timeL2 X T) :
    IntervalIntegrable (fun t ↦ _root_.Inner.inner ℝ (A t (u t)) (u t)) _root_.MeasureTheory.MeasureSpace.volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  change _root_.MeasureTheory.Integrable (fun t ↦ _root_.Inner.inner ℝ (A t (u t)) (u t)) (timeMeasure T)
  refine (L2.integrable_inner (timeOp A hA C hC u) u).congr ?_
  filter_upwards [timeOp_apply_ae A hA C hC u] with t ht
  rw [ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_int ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_int

omit [CompleteSpace X] in
theorem timeQuad_eq_integral
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hT : 0 ≤ T)
    (u : timeL2 X T) :
    timeQuad A hA C hC u =
      ∫ t in (0 : ℝ)..T, _root_.Inner.inner ℝ (A t (u t)) (u t) := by
  rw [timeQuad, inner_def, intervalIntegral.integral_of_le hT,
    ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [timeOp_apply_ae A hA C hC u] with t ht
  rw [ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_eq_integral ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_eq_integral

omit [CompleteSpace X] in
theorem isBoundedUnder_norm_timeQuad {ι : Type*} {l : Filter ι}
    (A : ι → ℝ → X →L[ℝ] X)
    (hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (A n) (timeMeasure T))
    (C : ι → NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (B : NNReal) (hB : ∀ᶠ n in l, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (B : ℝ))
    (u : ι → timeL2 X T)
    (hu : _root_.Filter.IsBoundedUnder (· ≤ ·) l (fun n ↦ ‖u n‖)) :
    _root_.Filter.IsBoundedUnder (· ≤ ·) l
      (fun n ↦ ‖timeQuad (A n) (hA n) (C n) (hC n) (u n)‖) := by
  obtain ⟨D₀, hD₀⟩ := hu
  let D : ℝ := _root_.Max.max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hnorm : ∀ᶠ n in l, ‖u n‖ ≤ D :=
    hD₀.mono fun _ hn ↦ hn.trans (le_max_left _ _)
  refine ⟨(B : ℝ) * D * D, ?_⟩
  change ∀ᶠ n in l, ‖timeQuad (A n) (hA n) (C n) (hC n) (u n)‖ ≤ _
  filter_upwards [hB, hnorm] with n hn hun
  have hop : timeOp (A n) (hA n) (C n) (hC n) = timeOp (A n) (hA n) B hn := by
    ext f
    filter_upwards [timeOp_apply_ae (A n) (hA n) (C n) (hC n) f,
      timeOp_apply_ae (A n) (hA n) B hn f] with t ht ht'
    exact ht.trans ht'.symm
  rw [timeQuad, hop]
  calc
    ‖inner ℝ (timeOp (A n) (hA n) B hn (u n)) (u n)‖ ≤
        ‖timeOp (A n) (hA n) B hn (u n)‖ * ‖u n‖ := norm_inner_le_norm _ _
    _ ≤ ((B : ℝ) * ‖u n‖) * ‖u n‖ := by
      exact mul_le_mul_of_nonneg_right
        (((timeOp (A n) (hA n) B hn).le_opNorm (u n)).trans
          (mul_le_mul_of_nonneg_right (timeOp_norm_le _ _ _ _) (norm_nonneg _)))
        (norm_nonneg _)
    _ ≤ (B : ℝ) * D * D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hun B.coe_nonneg) hun
        (norm_nonneg _) (mul_nonneg B.coe_nonneg hD)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.isBoundedUnder_norm_timeQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.isBoundedUnder_norm_timeQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.isBoundedUnder_norm_timeQuad ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.isBoundedUnder_norm_timeQuad

omit [CompleteSpace X] in
private theorem timeOp_nonneg
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ _root_.Inner.inner ℝ (A t x) x)
    (u : timeL2 X T) :
    0 ≤ _root_.Inner.inner ℝ (timeOp A hA C hC u) u := by
  rw [L2.inner_def]
  apply _root_.MeasureTheory.integral_nonneg_of_ae
  filter_upwards [timeOp_apply_ae A hA C hC u, hpos] with t hu ht
  rw [hu]
  exact ht (u t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_nonneg target :: scope.openDecls } }

private theorem timeOp_positive
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ _root_.Inner.inner ℝ (A t x) x) :
    (timeOp A hA C hC).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨?_, ?_⟩
  · intro u v
    rw [L2.inner_def, L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [timeOp_apply_ae A hA C hC u,
      timeOp_apply_ae A hA C hC v, hself] with t hu hv ht
    change _root_.Inner.inner ℝ ((timeOp A hA C hC u) t) (v t) =
      _root_.Inner.inner ℝ (u t) ((timeOp A hA C hC v) t)
    rw [hu, hv]
    exact ht.isSymmetric (u t) (v t)
  · intro u
    exact timeOp_nonneg A hA C hC hpos u

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_positive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_positive target :: scope.openDecls } }

private theorem quad_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (hL : L.IsPositive) :
    ConvexOn ℝ _root_.Set.univ (fun x ↦ _root_.Inner.inner ℝ (L x) x) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hxy : 0 ≤ _root_.Inner.inner ℝ (L (x - y)) (x - y) := hL.inner_nonneg_left (x - y)
  have hsym : _root_.Inner.inner ℝ (L x) y = _root_.Inner.inner ℝ x (L y) :=
    hL.inner_left_eq_inner_right x y
  have hid :
      _root_.Inner.inner ℝ (L (a • x + b • y)) (a • x + b • y) =
        a * _root_.Inner.inner ℝ (L x) x + b * _root_.Inner.inner ℝ (L y) y -
          a * b * _root_.Inner.inner ℝ (L (x - y)) (x - y) := by
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hsym, real_inner_comm x (L y)]
    have hb_eq : b = 1 - a := by linarith
    rw [hb_eq]
    ring
  change _root_.Inner.inner ℝ (L (a • x + b • y)) (a • x + b • y) ≤
    a * _root_.Inner.inner ℝ (L x) x + b * _root_.Inner.inner ℝ (L y) y
  rw [hid]
  have habpos : 0 ≤ a * b * _root_.Inner.inner ℝ (L (x - y)) (x - y) :=
    mul_nonneg (mul_nonneg ha hb) hxy
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.quad_convex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.quad_convex target :: scope.openDecls } }

private theorem quad_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) :
    Continuous (fun x ↦ _root_.Inner.inner ℝ (L x) x) :=
  L.continuous.inner continuous_id

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.quad_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.quad_continuous target :: scope.openDecls } }

private theorem weak_lsc_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ConvexOn ℝ _root_.Set.univ f) (hc : Continuous f) :
    LowerSemicontinuous (fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  let s : Set E := {x | f x ≤ r}
  have hsconv : Convex ℝ s := by
    simpa [s] using hf.convex_le r
  have hsclosed : IsClosed s := by
    exact isClosed_le hc continuous_const
  have himage : IsClosed ((toWeakSpace ℝ E) '' s) := by
    rw [← closure_eq_iff_isClosed]
    rw [← hsconv.toWeakSpace_closure ℝ, hsclosed.closure_eq]
  have heq :
      (fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x)) ⁻¹' _root_.Set.Iic r =
        (toWeakSpace ℝ E) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨(toWeakSpace ℝ E).symm x, hx, (toWeakSpace ℝ E).apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [s] using hy
  rw [heq]
  exact himage

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.weak_lsc_of_convex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.weak_lsc_of_convex target :: scope.openDecls } }

omit [CompleteSpace X] in
theorem timeQuad_nonneg
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ _root_.Inner.inner ℝ (A t x) x)
    (u : timeL2 X T) :
    0 ≤ timeQuad A hA C hC u :=
  timeOp_nonneg A hA C hC hpos u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_nonneg

theorem timeQuad_convex
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ _root_.Inner.inner ℝ (A t x) x) :
    ConvexOn ℝ _root_.Set.univ (timeQuad A hA C hC) := by
  exact quad_convex _ (timeOp_positive A hA C hC hself hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_convex ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_convex

theorem timeQuad_weak_lsc
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (hpos : ∀ᵐ t ∂timeMeasure T, ∀ x, 0 ≤ _root_.Inner.inner ℝ (A t x) x) :
    LowerSemicontinuous
      (fun u : WeakSpace ℝ (timeL2 X T) ↦
        timeQuad A hA C hC ((toWeakSpace ℝ (timeL2 X T)).symm u)) := by
  apply weak_lsc_of_convex
  · exact timeQuad_convex A hA C hC hself hpos
  · exact quad_continuous (timeOp A hA C hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_weak_lsc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_weak_lsc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_weak_lsc ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_weak_lsc

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
