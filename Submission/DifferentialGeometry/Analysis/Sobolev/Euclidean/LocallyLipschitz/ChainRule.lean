import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem lineDeriv_extension_ae_fderiv
    {Ω : Set E} (hΩ : IsOpen Ω) {f g : E → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hfg : _root_.Set.EqOn f g Ω) (i : Fin d) :
    (fun x => lineDeriv ℝ g x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
        (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet,
    _root_.MeasureTheory.ae_mono Measure.restrict_le_self hg.ae_differentiableAt] with x hx hdx
  have hloc : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hfg hy
  rw [hdx.lineDeriv_eq_fderiv, hloc.fderiv_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.lineDeriv_extension_ae_fderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.lineDeriv_extension_ae_fderiv target :: scope.openDecls } }

theorem hasWeakPartialDeriv_fderiv_of_lipschitzOnWith
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  refine (hasWeakPart_of_lip (Omega := Ω) hg i).congr_ae ?_
    (lineDeriv_extension_ae_fderiv hΩ hg hfg i)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with x hx
  exact (hfg hx).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_fderiv_of_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_fderiv_of_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_fderiv_of_lipschitzOnWith ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_fderiv_of_lipschitzOnWith

theorem memLp_top_fderiv_of_lipschitzOnWith
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    _root_.MeasureTheory.MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) ∞
      (volume.restrict Ω) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  exact (_root_.MeasureTheory.memLp_congr_ae (lineDeriv_extension_ae_fderiv hΩ hg hfg i)).mp
    (hg.memLp_lineDeriv (μ := volume.restrict Ω) (EuclideanSpace.single i 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_top_fderiv_of_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_top_fderiv_of_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_top_fderiv_of_lipschitzOnWith ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_top_fderiv_of_lipschitzOnWith

theorem memLp_fderiv_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (p : ℝ≥0∞) (i : Fin d) :
    _root_.MeasureTheory.MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p
      (volume.restrict Ω) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (_root_.MeasureTheory.measure_mono (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  exact (memLp_top_fderiv_of_lipschitzOnWith hΩ (hC.mono subset_closure) i).mono_exponent
    le_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_fderiv_of_locallyLipschitzOn

theorem memW1p_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (p : ℝ≥0∞) :
    DeGiorgi.MemW1p p f Ω := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by
      simpa only [Measure.restrict_apply_univ] using
        (_root_.MeasureTheory.measure_mono (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
          (subset_closure : Ω ⊆ closure Ω)).trans_lt hΩc.measure_lt_top⟩
  refine ⟨(hf.continuousOn.memLp_top_of_subset_isCompact hΩc hΩ.measurableSet
    subset_closure).mono_exponent le_top, ?_⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  intro i
  exact ⟨fun x => fderiv ℝ f x (EuclideanSpace.single i 1),
    memLp_fderiv_of_locallyLipschitzOn hΩ hΩc hf p i,
    hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ (hC.mono subset_closure) i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_of_locallyLipschitzOn

private theorem locallyLipschitzOn_exp_neg
    {s : Set E} {f : E → ℝ} (hf : LocallyLipschitzOn s f) :
    LocallyLipschitzOn s (fun x => Real.exp (-f x)) := by
  have hcont : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t)) := contDiff_id.neg.exp
  have he : LocallyLipschitz (fun t : ℝ => Real.exp (-t)) := hcont.locallyLipschitz
  apply locallyLipschitzOn_iff_restrict.mpr
  exact he.comp hf.restrict

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.locallyLipschitzOn_exp_neg target :: scope.openDecls } }

private theorem fderiv_exp_neg_ae
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f Ω) (i : Fin d) :
    (fun x => fderiv ℝ (fun y => Real.exp (-f y)) x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
        (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet,
    hf.ae_differentiableWithinAt (μ := _root_.MeasureTheory.MeasureSpace.volume) hΩ.measurableSet] with x hx hdx
  have hd : DifferentiableAt ℝ f x := hdx.differentiableAt (hΩ.mem_nhds hx)
  simpa only [Pi.neg_apply, smul_apply,
    neg_apply, smul_eq_mul, mul_neg, neg_mul] using
      congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
        hd.hasFDerivAt.neg.exp.fderiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_exp_neg_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_exp_neg_ae target :: scope.openDecls } }

theorem hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1))
      (fun x => Real.exp (-f x)) Ω := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  have he := locallyLipschitzOn_exp_neg hf
  obtain ⟨D, hD⟩ := he.exists_lipschitzOnWith_of_compact hΩc
  exact (hasWeakPartialDeriv_fderiv_of_lipschitzOnWith hΩ
    (hD.mono subset_closure) i).congr_ae (Filter.EventuallyEq.rfl)
      (fderiv_exp_neg_ae hΩ (hC.mono subset_closure) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_exp_neg_of_locallyLipschitzOn

theorem memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f)
    (p : ℝ≥0∞) (i : Fin d) :
    _root_.MeasureTheory.MemLp
      (fun x => -Real.exp (-f x) * fderiv ℝ f x (EuclideanSpace.single i 1))
      p (volume.restrict Ω) := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith_of_compact hΩc
  exact (_root_.MeasureTheory.memLp_congr_ae (fderiv_exp_neg_ae hΩ (hC.mono subset_closure) i)).mp
    (memLp_fderiv_of_locallyLipschitzOn hΩ hΩc (locallyLipschitzOn_exp_neg hf) p i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_exp_neg_mul_fderiv_of_locallyLipschitzOn

theorem memW1p_exp_neg_of_locallyLipschitzOn
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {f : E → ℝ} (hf : LocallyLipschitzOn (closure Ω) f) (p : ℝ≥0∞) :
    DeGiorgi.MemW1p p (fun x => Real.exp (-f x)) Ω :=
  memW1p_of_locallyLipschitzOn hΩ hΩc (locallyLipschitzOn_exp_neg hf) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_exp_neg_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_exp_neg_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_exp_neg_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memW1p_exp_neg_of_locallyLipschitzOn

end DifferentialGeometry.Analysis.Sobolev.Euclidean
