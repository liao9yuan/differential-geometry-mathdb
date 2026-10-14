import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def densityOnEuclidClosureSup
    (g : SmoothRiemannianMetric I M) (α : M) (Ω' : Set EuclN) : ℝ :=
  sSup ((fun x => |densityOnEuclid (I := I) g α x|) '' closure Ω')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclidClosureSup_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (Ω' : Set EuclN) :
    0 ≤ densityOnEuclidClosureSup (I := I) (M := M) g α Ω' := by
  unfold densityOnEuclidClosureSup
  refine Real.sSup_nonneg ?_
  rintro y ⟨x, _, rfl⟩
  exact abs_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclidClosureSup_nonneg

omit [NeZero (Module.finrank ℝ E)] in
lemma abs_densityOnEuclid_le_closureSup
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {x : EuclN} (hx : x ∈ closure Ω') :
    |densityOnEuclid (I := I) g α x| ≤
      densityOnEuclidClosureSup (I := I) (M := M) g α Ω' := by
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (closure Ω') :=
    ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono hΩ'_closure_in
  have h_abs_contOn : ContinuousOn
      (fun x => |densityOnEuclid (I := I) g α x|) (closure Ω') :=
    h_dens_contOn.abs
  have h_bddAbove : BddAbove
      ((fun x => |densityOnEuclid (I := I) g α x|) '' closure Ω') :=
    hΩ'_closure_compact.bddAbove_image h_abs_contOn
  exact le_csSup h_bddAbove (Set.mem_image_of_mem _ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.abs_densityOnEuclid_le_closureSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.abs_densityOnEuclid_le_closureSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.abs_densityOnEuclid_le_closureSup ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.abs_densityOnEuclid_le_closureSup

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_mul_memLp
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))) :
    MemLp (fun x => densityOnEuclid (I := I) g α x * f x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')) := by
  classical
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (closure Ω') :=
    ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono hΩ'_closure_in
  have h_dens_aesm : _root_.MeasureTheory.AEStronglyMeasurable (densityOnEuclid (I := I) g α)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')) :=
    h_dens_contOn.aestronglyMeasurable hΩ'_closure_meas
  set Mden : ℝ := densityOnEuclidClosureSup (I := I) (M := M) g α Ω' with hMden_def
  have hMden_nn : 0 ≤ Mden :=
    densityOnEuclidClosureSup_nonneg (I := I) (M := M) g α Ω'
  have h_pt_le : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')),
      ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖Mden * f x‖ := by
    refine _root_.MeasureTheory.ae_restrict_of_forall_mem hΩ'_closure_meas ?_
    intro x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hMden_nn]
    have h_dens_bd : |densityOnEuclid (I := I) g α x| ≤ Mden :=
      abs_densityOnEuclid_le_closureSup
        hΩ'_closure_compact hΩ'_closure_in hx
    exact mul_le_mul_of_nonneg_right h_dens_bd (abs_nonneg _)
  exact MemLp.mono (hf.const_mul Mden)
    (h_dens_aesm.mul hf.aestronglyMeasurable) h_pt_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_mul_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_mul_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_mul_memLp ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_mul_memLp

omit [NeZero (Module.finrank ℝ E)] in
lemma eLpNorm_densityOnEuclid_mul_sq_le
    {g : SmoothRiemannianMetric I M} {α : M} {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))) :
    (_root_.MeasureTheory.eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
      (densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2 *
        (_root_.MeasureTheory.eLpNorm f 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω'))).toReal ^ 2 := by
  classical
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  set μ : _root_.MeasureTheory.Measure EuclN := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (closure Ω')
    with hμ_def
  set Mden : ℝ := densityOnEuclidClosureSup (I := I) (M := M) g α Ω' with hMden_def
  have hMden_nn : 0 ≤ Mden :=
    densityOnEuclidClosureSup_nonneg (I := I) (M := M) g α Ω'
  have h_pt_le : ∀ᵐ x ∂μ,
      ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖(Mden • f) x‖ := by
    rw [hμ_def]
    refine _root_.MeasureTheory.ae_restrict_of_forall_mem hΩ'_closure_meas ?_
    intro x hx
    change ‖densityOnEuclid (I := I) g α x * f x‖ ≤ ‖Mden • f x‖
    rw [Real.norm_eq_abs, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hMden_nn]
    have h_dens_bd : |densityOnEuclid (I := I) g α x| ≤ Mden :=
      abs_densityOnEuclid_le_closureSup
        hΩ'_closure_compact hΩ'_closure_in hx
    exact mul_le_mul_of_nonneg_right h_dens_bd (abs_nonneg _)
  have h_eLp_le :
      eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ ≤
        (‖Mden‖ₑ : ℝ≥0∞) * _root_.MeasureTheory.eLpNorm f 2 μ := by
    calc _root_.MeasureTheory.eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ
        ≤ _root_.MeasureTheory.eLpNorm (Mden • f) 2 μ := _root_.MeasureTheory.eLpNorm_mono_ae h_pt_le
      _ = (‖Mden‖ₑ : ℝ≥0∞) * _root_.MeasureTheory.eLpNorm f 2 μ := _root_.MeasureTheory.eLpNorm_const_smul Mden f 2 μ
  have h_eLpf_ne_top : _root_.MeasureTheory.eLpNorm f 2 μ ≠ (⊤ : ℝ≥0∞) := by
    rw [hμ_def]; exact hf.2.ne
  have h_toReal_le :
      (_root_.MeasureTheory.eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal ≤
        Mden * (_root_.MeasureTheory.eLpNorm f 2 μ).toReal := by
    have h_mono := ENNReal.toReal_mono
      (by
        rw [hμ_def]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top hf.2.ne) h_eLp_le
    rwa [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs,
      abs_of_nonneg hMden_nn] at h_mono
  have h_lhs_nn : 0 ≤
      (_root_.MeasureTheory.eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal :=
    ENNReal.toReal_nonneg
  have h_rhs_nn : 0 ≤ Mden * (_root_.MeasureTheory.eLpNorm f 2 μ).toReal :=
    mul_nonneg hMden_nn ENNReal.toReal_nonneg
  calc (_root_.MeasureTheory.eLpNorm (fun x => densityOnEuclid (I := I) g α x * f x) 2 μ).toReal ^ 2
      ≤ (Mden * (_root_.MeasureTheory.eLpNorm f 2 μ).toReal) ^ 2 := by
        exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
    _ = Mden ^ 2 * (_root_.MeasureTheory.eLpNorm f 2 μ).toReal ^ 2 := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.eLpNorm_densityOnEuclid_mul_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.eLpNorm_densityOnEuclid_mul_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.eLpNorm_densityOnEuclid_mul_sq_le ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.eLpNorm_densityOnEuclid_mul_sq_le

end MetricExtension

end Laplacian
end Analysis
end DifferentialGeometry
