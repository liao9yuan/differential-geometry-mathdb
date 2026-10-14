import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

private theorem hasWeakPartialDeriv_ball_of_forall_smaller_ball
    {c : E} {a : ℝ} {u v : E → ℝ} {j : Fin d}
    (h : ∀ r < a, DeGiorgi.HasWeakPartialDeriv j v u (Metric.ball c r)) :
    DeGiorgi.HasWeakPartialDeriv j v u (Metric.ball c a) := by
  intro ψ hψ hψc hψB
  obtain ⟨r, hra, hψr⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψB
  have hid := h r hra ψ hψ hψc hψr
  have hleft (s : Set E) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1)) =
        ∫ x, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1) := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport ψ := fun hmem => hx (hs hmem)
    rw [fderiv_of_notMem_tsupport ℝ hxs, zero_apply, _root_.MulZeroClass.mul_zero]
  have hright (s : Set E) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, v x * ψ x) = ∫ x, v x * ψ x := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport ψ := fun hmem => hx (hs hmem)
    rw [image_eq_zero_of_notMem_tsupport hxs, _root_.MulZeroClass.mul_zero]
  rw [hleft (Metric.ball c r) hψr, hright (Metric.ball c r) hψr] at hid
  rw [hleft (Metric.ball c a) hψB, hright (Metric.ball c a) hψB]
  exact hid

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_ball_of_forall_smaller_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_ball_of_forall_smaller_ball target :: scope.openDecls } }

theorem exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv
    {c : E} {a : ℝ} {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) (Metric.ball c a))
    (T : F → H) (hT : ContDiff ℝ 1 T)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ T y‖ ≤ C) :
    ∃ hw : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => T (f x) k) (Metric.ball c a),
      ∀ k x j, (hw k).weakGrad x j =
        (fderiv ℝ T (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) k := by
  let B := Metric.ball c a
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((_root_.MeasureTheory.measure_mono Metric.ball_subset_closedBall).trans_lt
      (_root_.ProperSpace.isCompact_closedBall c a).measure_lt_top).ne
  have hfm : _root_.MeasureTheory.MemLp f 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => (hf i).memLp
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ T 0)).trans (hC 0)
  let L : ℝ≥0 := NNReal.mk C hC0
  have hLip : LipschitzWith L T := lipschitzWith_of_nnnorm_fderiv_le
    (hT.differentiable one_ne_zero) (fun y => hC y)
  have hTm : _root_.MeasureTheory.MemLp (fun x => T (f x)) 2 (volume.restrict B) := by
    have hsub : _root_.MeasureTheory.MemLp (fun x => T (f x) - T 0) 2 (volume.restrict B) := by
      apply hfm.of_le_mul
        ((hT.continuous.comp_aestronglyMeasurable hfm.aestronglyMeasurable).sub
          _root_.MeasureTheory.aestronglyMeasurable_const)
      exact Filter.Eventually.of_forall fun x => by
        change ‖T (f x) - T 0‖ ≤ (L : ℝ) * ‖f x‖
        simpa only [sub_zero] using hLip.norm_sub_le (f x) 0
    simpa only [Pi.add_def, sub_add_cancel] using hsub.add (_root_.MeasureTheory.memLp_const (T 0))
  let G (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hG (j : Fin d) : _root_.MeasureTheory.MemLp (G j) 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  have htarget (j : Fin d) :
      MemLp (fun x => fderiv ℝ T (f x) (G j x)) 2 (volume.restrict B) :=
    MemLp.clm_apply_of_ae_norm_le
      ((hT.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hfm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hC (f x)) (hG j)
  have hweak (k : κ) (j : Fin d) :
      DeGiorgi.HasWeakPartialDeriv j
        (fun x => (fderiv ℝ T (f x) (G j x)) k) (fun x => T (f x) k) B := by
    apply hasWeakPartialDeriv_ball_of_forall_smaller_ball
    intro r hra
    obtain ⟨hw, hweq⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball
      Metric.isOpen_ball hf T hT hC (Metric.closedBall_subset_ball hra)
    have heq : (fun x => (hw k).weakGrad x j) =
        fun x => (fderiv ℝ T (f x) (G j x)) k := by
      funext x
      exact hweq k x j
    have hh := (hw k).isWeakGrad j
    change DeGiorgi.HasWeakPartialDeriv j (fun x => (hw k).weakGrad x j)
      (fun x => T (f x) k) (Metric.ball c r) at hh
    rw [heq] at hh
    exact hh
  let hw (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => T (f x) k) B :=
    { memLp := hTm.eval_piLp k
      weakGrad := fun x => WithLp.toLp 2 (fun j => (fderiv ℝ T (f x) (G j x)) k)
      weakGrad_component_memLp := fun j => (htarget j).eval_piLp k
      isWeakGrad := fun j => hweak k j }
  exact ⟨hw, fun k x j => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
