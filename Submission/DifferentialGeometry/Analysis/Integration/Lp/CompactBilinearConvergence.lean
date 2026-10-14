import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Group.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

variable {P X : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [T2Space P]
  {μ : Measure P} [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
private local instance domainDualNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.MeasureTheory.domainDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.domainDualNormedAddCommGroup target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance domainDualNormedSpace : NormedSpace ℝ (X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.MeasureTheory.domainDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.domainDualNormedSpace target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance scalarBilinearNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.MeasureTheory.scalarBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.scalarBilinearNormedAddCommGroup target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance scalarBilinearNormedSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.MeasureTheory.scalarBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.scalarBilinearNormedSpace target :: scope.openDecls } }

section General

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open _root_.MeasureTheory in
private local instance codomainMapNormedAddCommGroup : NormedAddCommGroup (Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.MeasureTheory.codomainMapNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.codomainMapNormedAddCommGroup target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance codomainMapNormedSpace : NormedSpace ℝ (Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.MeasureTheory.codomainMapNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.codomainMapNormedSpace target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance bilinearMapNormedAddCommGroup : NormedAddCommGroup (X →L[ℝ] Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.MeasureTheory.bilinearMapNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.bilinearMapNormedAddCommGroup target :: scope.openDecls } }

open _root_.MeasureTheory in
private local instance bilinearMapNormedSpace : NormedSpace ℝ (X →L[ℝ] Y →L[ℝ] Z) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.MeasureTheory.bilinearMapNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.bilinearMapNormedSpace target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem integrableOn_bilinear_of_continuousOn_of_isCompact
    [SecondCountableTopologyEither P Z]
    {K : Set P} (hK : IsCompact K)
    (B : P → X →L[ℝ] Y →L[ℝ] Z) (hB : ContinuousOn B K)
    {u : P → X} {v : P → Y}
    (hu : _root_.MeasureTheory.MemLp u 2 (μ.restrict K)) (hv : _root_.MeasureTheory.MemLp v 2 (μ.restrict K)) :
    IntegrableOn (fun z => B z (u z) (v z)) K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hB
  apply integrable_bilinear_of_apply_aestronglyMeasurable B
    (fun x y =>
      ((hB.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
        hK.measurableSet) (C := C) _ hu hv
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
  exact hC z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrableOn_bilinear_of_continuousOn_of_isCompact then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrableOn_bilinear_of_continuousOn_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrableOn_bilinear_of_continuousOn_of_isCompact ``Submission.MeasureTheory.integrableOn_bilinear_of_continuousOn_of_isCompact

end General

open _root_.MeasureTheory in
theorem tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact
    {K : Set P} (hK : IsCompact K)
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, ContinuousOn (B n) K) (hB₀ : ContinuousOn B₀ K)
    (hconv : TendstoUniformlyOn B B₀ _root_.Filter.atTop K)
    (u : ℕ → P → X) (u₀ v : P → X)
    (hu : ∀ n, _root_.MeasureTheory.MemLp (u n) 2 (μ.restrict K))
    (hu₀ : _root_.MeasureTheory.MemLp u₀ 2 (μ.restrict K)) (hv : _root_.MeasureTheory.MemLp v 2 (μ.restrict K))
    (htendsto : _root_.Filter.Tendsto (fun n => (hu n).toLp (u n)) _root_.Filter.atTop (𝓝 (hu₀.toLp u₀))) :
    _root_.Filter.Tendsto (fun n => ∫ z in K, B n z (u n z) (v z) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ z in K, B₀ z (u₀ z) (v z) ∂μ)) := by
  classical
  choose C hC using fun n => hK.exists_bound_of_continuousOn (hB n)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hB₀
  have hmeas (n : ℕ) (x y : X) :
      AEStronglyMeasurable (fun z => (B n z).flip x y) (μ.restrict K) :=
    (((hB n).clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hmeas₀ (x y : X) :
      AEStronglyMeasurable (fun z => (B₀ z).flip x y) (μ.restrict K) :=
    ((hB₀.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      hK.measurableSet
  have hbound (n : ℕ) : ∀ᵐ z ∂μ.restrict K, ‖(B n z).flip‖ ≤ C n := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
    simpa only [ContinuousLinearMap.opNorm_flip] using hC n z hz
  have hbound₀ : ∀ᵐ z ∂μ.restrict K, ‖(B₀ z).flip‖ ≤ C₀ := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
    simpa only [ContinuousLinearMap.opNorm_flip] using hC₀ z hz
  have hconv' : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in _root_.Filter.atTop,
      ∀ᵐ z ∂μ.restrict K, ‖(B n z).flip - (B₀ z).flip‖ ≤ δ := by
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
    have heq : (B n z).flip - (B₀ z).flip = (B n z - B₀ z).flip := rfl
    rw [heq, ContinuousLinearMap.opNorm_flip]
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn z hz)
  have h := tendsto_integral_bilinear_of_weak
    (fun n z => (B n z).flip) (fun z => (B₀ z).flip)
    hmeas hmeas₀ C C₀ hbound hbound₀ hconv'
    (fun n => (hu n).toLp (u n)) (hu₀.toLp u₀) (hv.toLp v)
    (fun L => L.continuous.continuousAt.tendsto.comp htendsto)
  have heq (n : ℕ) :
      (∫ z in K, (B n z).flip (hv.toLp v z) ((hu n).toLp (u n) z) ∂μ) =
        ∫ z in K, B n z (u n z) (v z) ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp, hv.coeFn_toLp] with z huz hvz
    rw [huz, hvz, ContinuousLinearMap.flip_apply]
  have heq₀ :
      (∫ z in K, (B₀ z).flip (hv.toLp v z) (hu₀.toLp u₀ z) ∂μ) =
        ∫ z in K, B₀ z (u₀ z) (v z) ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hu₀.coeFn_toLp, hv.coeFn_toLp] with z huz hvz
    rw [huz, hvz, ContinuousLinearMap.flip_apply]
  simpa only [heq, heq₀] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact ``Submission.MeasureTheory.tendsto_setIntegral_bilinear_of_tendstoUniformlyOn_of_isCompact

end MeasureTheory
