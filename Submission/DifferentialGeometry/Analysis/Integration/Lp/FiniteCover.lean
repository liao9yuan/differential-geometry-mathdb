import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem memLp_of_finite_ae_cover
    {α ι E : Type*} [MeasurableSpace α] [Finite ι] [NormedAddCommGroup E]
    {μ : _root_.MeasureTheory.Measure α} {p : ℝ≥0∞} {f : α → E}
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hf : ∀ i, _root_.MeasureTheory.MemLp f p (μ.restrict (s i))) : _root_.MeasureTheory.MemLp f p μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hμ : μ.restrict (⋃ i, s i) = μ :=
    Measure.restrict_eq_self_of_ae_mem hcover
  have hfm : _root_.MeasureTheory.AEStronglyMeasurable f μ := by
    rw [← hμ]
    exact AEStronglyMeasurable.iUnion (fun i => (hf i).aestronglyMeasurable)
  let b : α → ℝ := fun x => ∑ i, ‖(s i).indicator f x‖
  have hb : _root_.MeasureTheory.MemLp b p μ := by
    exact _root_.MeasureTheory.memLp_finsetSum Finset.univ (fun i _ =>
      ((_root_.MeasureTheory.memLp_indicator_iff_restrict (hs i)).mpr (hf i)).norm)
  apply hb.mono' hfm
  filter_upwards [hcover] with x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hsum : ‖(s i).indicator f x‖ ≤ ∑ j, ‖(s j).indicator f x‖ :=
    Finset.single_le_sum (f := fun j => ‖(s j).indicator f x‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  simpa only [Set.indicator_of_mem hi, b] using hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.memLp_of_finite_ae_cover then
    throwError "Refusing to shadow existing declaration MeasureTheory.memLp_of_finite_ae_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.memLp_of_finite_ae_cover ``Submission.MeasureTheory.memLp_of_finite_ae_cover

open _root_.MeasureTheory in
theorem exists_lp_lift_of_finite_ae_cover
    {α ι E F : Type*} [MeasurableSpace α] [Finite ι] [NormedAddCommGroup E]
    {μ : _root_.MeasureTheory.Measure α} {p : ℝ≥0∞} {j : E → F}
    (hinj : Function.Injective j) {g : α → F}
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (v : ∀ i, _root_.MeasureTheory.Lp E p (μ.restrict (s i)))
    (hv : ∀ i, (fun x => j (v i x)) =ᵐ[μ.restrict (s i)] g) :
    ∃ u : _root_.MeasureTheory.Lp E p μ, (fun x => j (u x)) =ᵐ[μ] g ∧
      ∀ i, (fun x => u x) =ᵐ[μ.restrict (s i)] fun x => v i x := by
  classical
  let f : α → E := fun x => if h : ∃ e : E, j e = g x then h.choose else 0
  have hfv (i : ι) : f =ᵐ[μ.restrict (s i)] fun x => v i x := by
    filter_upwards [hv i] with x hx
    have hex : ∃ e : E, j e = g x := ⟨v i x, hx⟩
    apply hinj
    have hfg : j (f x) = g x := by
      simp only [f, dif_pos hex]
      exact hex.choose_spec
    exact hfg.trans hx.symm
  have hf : _root_.MeasureTheory.MemLp f p μ :=
    memLp_of_finite_ae_cover s hs hcover
      (fun i => MemLp.ae_eq (hfv i).symm (Lp.memLp (v i)))
  have hproj : (fun x => j (f x)) =ᵐ[μ.restrict (⋃ i, s i)] g := by
    apply (_root_.MeasureTheory.ae_restrict_iUnion_iff s (fun x => j (f x) = g x)).mpr
    intro i
    filter_upwards [hfv i, hv i] with x hxf hxv
    exact (congrArg j hxf).trans hxv
  rw [Measure.restrict_eq_self_of_ae_mem hcover] at hproj
  let u : _root_.MeasureTheory.Lp E p μ := hf.toLp f
  have huf : (fun x => u x) =ᵐ[μ] f := hf.coeFn_toLp
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [huf, hproj] with x hxf hxg
    exact (congrArg j hxf).trans hxg
  · intro i
    have huf' : (fun x => u x) =ᵐ[μ.restrict (s i)] f := _root_.MeasureTheory.ae_restrict_of_ae huf
    exact huf'.trans (hfv i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_lp_lift_of_finite_ae_cover then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_lp_lift_of_finite_ae_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_lp_lift_of_finite_ae_cover ``Submission.MeasureTheory.exists_lp_lift_of_finite_ae_cover

end MeasureTheory
