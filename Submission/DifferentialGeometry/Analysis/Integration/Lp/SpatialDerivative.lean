import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.Analysis.Calculus.ContDiff.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

open _root_.Filter
open scoped _root_.NNReal _root_.Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_comp_inl_le_of_lipschitzOn
    (f : E × F → G) (z : E × F) {U : Set E} (hU : U ∈ 𝓝 z.1)
    {C : ℝ≥0} (hf : LipschitzOnWith C (fun x => f (x, z.2)) U) :
    ‖(fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E F)‖ ≤ C := by
  by_cases hdiff : DifferentiableAt ℝ f z
  · have he : fderiv ℝ (fun x => f (x, z.2)) z.1 =
        (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E F) :=
      (hdiff.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)).fderiv
    rw [← he]
    exact norm_fderiv_le_of_lipschitzOn ℝ hU hf
  · rw [fderiv_zero_of_not_differentiableAt hdiff]
    simpa only [ContinuousLinearMap.zero_comp, norm_zero] using C.coe_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn ``Submission.DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn

end DifferentialGeometry.Analysis.Calculus

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Set
open scoped _root_.ENNReal _root_.NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open _root_.MeasureTheory in
theorem memLp_fderiv_comp_inl_of_lipschitzOn
    (f : E × ℝ → ℝ) (μ : _root_.MeasureTheory.Measure (E × ℝ)) {U K : Set E} {J : Set ℝ}
    (hU : IsOpen U) (hK : MeasurableSet K) (hJ : MeasurableSet J) (hKU : K ⊆ U)
    [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (K ×ˢ J))] {C : ℝ≥0}
    (hf : ∀ t ∈ J, LipschitzOnWith C (fun x => f (x, t)) U) (p : ℝ≥0∞) :
    _root_.MeasureTheory.MemLp (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)) p
      (μ.restrict (K ×ˢ J)) := by
  have hm : Measurable
      (fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ f)
  apply MemLp.of_bound hm.aestronglyMeasurable (C : ℝ)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (hK.prod hJ)] with z hz
  exact DifferentialGeometry.Analysis.Calculus.norm_fderiv_comp_inl_le_of_lipschitzOn
    f z (hU.mem_nhds (hKU hz.1)) (hf z.2 hz.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.memLp_fderiv_comp_inl_of_lipschitzOn then
    throwError "Refusing to shadow existing declaration MeasureTheory.memLp_fderiv_comp_inl_of_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.memLp_fderiv_comp_inl_of_lipschitzOn ``Submission.MeasureTheory.memLp_fderiv_comp_inl_of_lipschitzOn

end MeasureTheory

end

end

section

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {Z E F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace (Z × E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem memLp_top_and_spatial_fderiv_of_contDiffOn
    {S J : Set Z} (hS : IsOpen S) (hJ : IsCompact J) (hJS : J ⊆ S)
    {U Ω : Set E} (hU : IsOpen U) (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U)
    {A : Z → E → F}
    (hA : ContDiffOn ℝ 1 (fun p : Z × E => A p.1 p.2) (S ×ˢ U))
    (μ : _root_.MeasureTheory.Measure (Z × E)) :
    _root_.MeasureTheory.MemLp (fun p : Z × E => A p.1 p.2) ∞ (μ.restrict (J ×ˢ Ω)) ∧
      (∀ v : E, _root_.MeasureTheory.MemLp (fun p : Z × E => fderiv ℝ (A p.1) p.2 v)
        ∞ (μ.restrict (J ×ˢ Ω))) := by
  constructor
  · exact (hA.continuousOn.mono (_root_.Set.prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (_root_.Set.prod_mono Subset.rfl subset_closure)
  · intro v
    have hc : ContinuousOn (fun p : Z × E =>
        fderiv ℝ (fun q : Z × E => A q.1 q.2) p (0, v)) (S ×ˢ U) :=
      (hA.continuousOn_fderiv_of_isOpen (hS.prod hU) le_rfl).clm_apply continuousOn_const
    have heq (p : Z × E) (hp : p ∈ S ×ˢ U) :
        fderiv ℝ (A p.1) p.2 v = fderiv ℝ (fun q : Z × E => A q.1 q.2) p (0, v) := by
      have hd := ((hA.differentiableOn (by norm_num) p hp).differentiableAt
        ((hS.prod hU).mem_nhds hp)).hasFDerivAt
      have hh := hd.comp p.2 ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
      exact congrArg (fun L : E →L[ℝ] F => L v) hh.fderiv
    have hs : ContinuousOn (fun p : Z × E => fderiv ℝ (A p.1) p.2 v) (S ×ˢ U) :=
      hc.congr (fun p hp => heq p hp)
    exact (hs.mono (_root_.Set.prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (_root_.Set.prod_mono Subset.rfl subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.memLp_top_and_spatial_fderiv_of_contDiffOn

end DifferentialGeometry.Analysis

end

end
