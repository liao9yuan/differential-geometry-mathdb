import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationChart
import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationHessian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem parameterDifferential_eq_of_eventuallyEq {n : ℕ} {φ ψ : Fin n → E → ℝ}
    {x : E} (h : ∀ i, φ i =ᶠ[𝓝 x] ψ i) :
    parameterDifferential (I := 𝓘(ℝ, E)) φ x = parameterDifferential (I := 𝓘(ℝ, E)) ψ x := by
  apply ContinuousLinearMap.ext
  intro p
  simp only [parameterDifferential_apply, mfderiv_eq_fderiv]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun D : E →L[ℝ] ℝ => p i • D) (h i).fderiv_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.parameterDifferential_eq_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.parameterDifferential_eq_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.parameterDifferential_eq_of_eventuallyEq ``Submission.DifferentialGeometry.Morse.parameterDifferential_eq_of_eventuallyEq

variable [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem exists_open_ae_nondegenerate_finitePerturbation {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) {x : M} (hx : I.IsInteriorPoint x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)), ∀ y ∈ V,
        Surjective (parameterDifferential (I := I) φ y) →
        mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) y = 0 →
        _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => finitePerturbation f φ p ((extChartAt I y).symm z)))
          (extChartAt I y y)) := by
  let g : Option (Fin n) → M → ℝ := fun i => match i with | _root_.Option.none => f | _root_.Option.some j => φ j
  have hg : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (g i) := by
    intro i
    cases i with
    | none => exact hf
    | some j => exact hφ j
  obtain ⟨W,F,hW,hxW,hWc,hF⟩ := exists_contDiff_interiorChart_extensions hg hx
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let V := c.source ∩ c ⁻¹' W
  have hV : IsOpen V := c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source hW
  have hxc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  refine ⟨V,hV,⟨hxc,hxW⟩,?_⟩
  have hFeq : ∀ p, _root_.Set.EqOn (finitePerturbation (F _root_.Option.none) (fun i => F (_root_.Option.some i)) p)
      (fun z => finitePerturbation f φ p (c.symm z)) W := by
    intro p z hz
    unfold finitePerturbation
    congr 1
    · exact (hF _root_.Option.none).2.2.2 hz
    · exact Finset.sum_congr rfl fun i _ => congrArg (fun t : ℝ => p i * t) ((hF (_root_.Option.some i)).2.2.2 hz)
  filter_upwards [ae_nondegenerate_finitePerturbation (hF _root_.Option.none).1 (fun i => (hF (_root_.Option.some i)).1)
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))] with p hp y hy hreg hcrit
  have hyc : y ∈ c.source := hy.1
  have hzW : c y ∈ W := hy.2
  have hzc : c y ∈ c.target := hWc hzW
  have heq : finitePerturbation (F _root_.Option.none) (fun i => F (_root_.Option.some i)) p =ᶠ[𝓝 (c y)]
      (fun z => finitePerturbation f φ p (c.symm z)) := by
    filter_upwards [hW.mem_nhds hzW] with z hz
    exact hFeq p hz
  have hφeq : ∀ i, F (_root_.Option.some i) =ᶠ[𝓝 (c y)] (fun z => φ i (c.symm z)) := by
    intro i
    filter_upwards [hW.mem_nhds hzW] with z hz
    exact (hF (_root_.Option.some i)).2.2.2 hz
  have hreg' : _root_.Function.Surjective (parameterDifferential (I := 𝓘(ℝ, E)) (fun i => F (_root_.Option.some i)) (c y)) := by
    rw [parameterDifferential_eq_of_eventuallyEq hφeq]
    apply surjective_parameterDifferential_partialDiffeomorph_symm hφ c hzc
    exact (congrArg (fun t => _root_.Function.Surjective (parameterDifferential (I := I) φ t)) (c.left_inv hyc)).mpr hreg
  have hfp := contMDiff_finitePerturbation hf hφ p
  have hcrit' : fderiv ℝ (finitePerturbation (F _root_.Option.none) (fun i => F (_root_.Option.some i)) p) (c y) = 0 := by
    rw [heq.fderiv_eq]
    apply (fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff hfp c hzc).mpr
    let D : M → E →L[ℝ] ℝ := fun t => mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) t
    change D (c.symm (c y)) = 0
    exact (congrArg D (c.left_inv hyc)).trans hcrit
  have hess := hp (c y) hreg' hcrit'
  rw [heq.fderiv.fderiv_eq] at hess
  let d := DifferentialGeometry.Manifold.interiorChart I ∞ y
  have hyd : y ∈ d.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ y).mpr
    (DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞ (by simp) hyc)
  exact (bijective_hessian_partialDiffeomorph_chart_iff hfp c d hyc hyd hcrit).mpr hess

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_open_ae_nondegenerate_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_open_ae_nondegenerate_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_open_ae_nondegenerate_finitePerturbation ``Submission.DifferentialGeometry.Morse.exists_open_ae_nondegenerate_finitePerturbation


theorem ae_nondegenerate_finitePerturbation_on_isCompact {n : ℕ} {f : M → ℝ}
    {φ : Fin n → M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) {K : Set M}
    (hK : IsCompact K) (hKI : ∀ x ∈ K, I.IsInteriorPoint x) :
    ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)), ∀ x ∈ K,
      Surjective (parameterDifferential (I := I) φ x) →
      mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0 →
      _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => finitePerturbation f φ p ((extChartAt I x).symm z)))
        (extChartAt I x x)) := by
  classical
  choose V hV hxV hAE using fun x : K =>
    exists_open_ae_nondegenerate_finitePerturbation hf hφ (hKI x x.property)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hall := MeasureTheory.ae_all_iff.mpr (fun i : s => hAE i.val)
  filter_upwards [hall] with p hp x hx hreg hcrit
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact hp ⟨i,hi⟩ x hxi hreg hcrit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.ae_nondegenerate_finitePerturbation_on_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.ae_nondegenerate_finitePerturbation_on_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.ae_nondegenerate_finitePerturbation_on_isCompact ``Submission.DifferentialGeometry.Morse.ae_nondegenerate_finitePerturbation_on_isCompact


theorem exists_relative_nondegenerate_manifold_finitePerturbation [T2Space M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ p, _root_.Set.EqOn (finitePerturbation f φ p) f N) ∧
      ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)), ∀ x ∈ K,
        mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0 →
        _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => finitePerturbation f φ p ((extChartAt I x).symm z)))
          (extChartAt I x x)) := by
  obtain ⟨n,φ,hφ,hspan⟩ := exists_supported_differentials_span_of_isCompact (I := I) hK hU hKU
  refine ⟨n,φ,hφ,exists_open_finitePerturbation_eq (f := f) (fun i => (hφ i).2.2),?_⟩
  filter_upwards [ae_nondegenerate_finitePerturbation_on_isCompact hf (fun i => (hφ i).1) hK hKI]
    with p hp x hx hc
  exact hp x hx (surjective_parameterDifferential (hspan x hx)) hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_relative_nondegenerate_manifold_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_relative_nondegenerate_manifold_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_relative_nondegenerate_manifold_finitePerturbation ``Submission.DifferentialGeometry.Morse.exists_relative_nondegenerate_manifold_finitePerturbation


theorem exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation [T2Space M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x) :
    ∃ (n : ℕ) (φ : Fin n → M → ℝ),
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ ∀ p, _root_.Set.EqOn (finitePerturbation f φ p) f N) ∧
      ∀ ε : ℝ, 0 < ε → ∃ p : Fin n → ℝ, ‖p‖ < ε ∧ ∀ x ∈ K,
        mfderiv I 𝓘(ℝ, ℝ) (finitePerturbation f φ p) x = 0 →
        _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => finitePerturbation f φ p ((extChartAt I x).symm z)))
          (extChartAt I x x)) := by
  obtain ⟨n,φ,hφ,hfix,hae⟩ := exists_relative_nondegenerate_manifold_finitePerturbation hf hK hU hKU hKI
  refine ⟨n,φ,hφ,hfix,fun ε hε => ?_⟩
  obtain ⟨p,hp,hreg⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) 0 hε).ne'
    (MeasureTheory.ae_restrict_of_ae hae)
  exact ⟨p,by simpa only [Metric.mem_ball, dist_zero_right] using hp,hreg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation ``Submission.DifferentialGeometry.Morse.exists_arbitrarily_small_relative_nondegenerate_manifold_finitePerturbation

end DifferentialGeometry.Morse
