import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.ENNReal

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {α E 𝕜 : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  {μ : Measure α} {p : ℝ≥0∞} {s : Set α}

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def zeroExtend (hs : MeasurableSet s) (u : _root_.MeasureTheory.Lp E p (μ.restrict s)) : _root_.MeasureTheory.Lp E p μ :=
  ((_root_.MeasureTheory.memLp_indicator_iff_restrict hs).mpr (Lp.memLp u)).toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.zeroExtend then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.zeroExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.zeroExtend ``Submission.MeasureTheory.Lp.zeroExtend

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_zeroExtend (hs : MeasurableSet s) (u : _root_.MeasureTheory.Lp E p (μ.restrict s)) :
    zeroExtend hs u =ᵐ[μ] s.indicator u := MemLp.coeFn_toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_zeroExtend then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_zeroExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_zeroExtend ``Submission.MeasureTheory.Lp.coeFn_zeroExtend

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp] theorem norm_zeroExtend (hs : MeasurableSet s) (u : _root_.MeasureTheory.Lp E p (μ.restrict s)) :
    ‖zeroExtend hs u‖ = ‖u‖ := by
  rw [zeroExtend, Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hs]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_zeroExtend then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_zeroExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_zeroExtend ``Submission.MeasureTheory.Lp.norm_zeroExtend

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem zeroExtend_add (hs : MeasurableSet s) (u v : _root_.MeasureTheory.Lp E p (μ.restrict s)) :
    zeroExtend hs (u + v) = zeroExtend hs u + zeroExtend hs v := by
  apply Lp.ext
  have hadd : s.indicator (fun x => (u + v) x) =ᵐ[μ] s.indicator (fun x => u x + v x) := by
    have hh := Lp.coeFn_add u v
    rw [_root_.Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hs] at hh
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ s
    · simp only [_root_.Set.indicator_of_mem hxs, hx hxs, Pi.add_apply]
    · simp only [_root_.Set.indicator_of_notMem hxs]
  filter_upwards [coeFn_zeroExtend hs (u + v), coeFn_zeroExtend hs u, coeFn_zeroExtend hs v,
    Lp.coeFn_add (zeroExtend hs u) (zeroExtend hs v), hadd] with x ha hu hv hvv haddx
  rw [ha, haddx, hvv, Pi.add_apply, hu, hv]
  by_cases hxs : x ∈ s
  · simp only [_root_.Set.indicator_of_mem hxs]
  · simp only [_root_.Set.indicator_of_notMem hxs, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.zeroExtend_add then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.zeroExtend_add"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.zeroExtend_add ``Submission.MeasureTheory.Lp.zeroExtend_add

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem zeroExtend_smul (hs : MeasurableSet s) (c : 𝕜) (u : _root_.MeasureTheory.Lp E p (μ.restrict s)) :
    zeroExtend hs (c • u) = c • zeroExtend hs u := by
  apply Lp.ext
  have hsm : s.indicator (fun x => (c • u) x) =ᵐ[μ] s.indicator (fun x => c • u x) := by
    have hh := Lp.coeFn_smul c u
    rw [_root_.Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hs] at hh
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ s
    · simp only [_root_.Set.indicator_of_mem hxs, hx hxs, Pi.smul_apply]
    · simp only [_root_.Set.indicator_of_notMem hxs]
  filter_upwards [coeFn_zeroExtend hs (c • u), coeFn_zeroExtend hs u,
    Lp.coeFn_smul c (zeroExtend hs u), hsm] with x ha hu hv hsmx
  rw [ha, hsmx, hv, Pi.smul_apply, hu]
  by_cases hxs : x ∈ s
  · simp only [_root_.Set.indicator_of_mem hxs]
  · simp only [_root_.Set.indicator_of_notMem hxs, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.zeroExtend_smul then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.zeroExtend_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.zeroExtend_smul ``Submission.MeasureTheory.Lp.zeroExtend_smul

variable [Fact (1 ≤ p)]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def zeroExtendₗᵢ (hs : MeasurableSet s) : _root_.MeasureTheory.Lp E p (μ.restrict s) →ₗᵢ[𝕜] _root_.MeasureTheory.Lp E p μ where
  toFun := zeroExtend hs
  map_add' := zeroExtend_add hs
  map_smul' := zeroExtend_smul hs
  norm_map' := norm_zeroExtend hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.zeroExtendₗᵢ then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.zeroExtendₗᵢ"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.zeroExtendₗᵢ ``Submission.MeasureTheory.Lp.zeroExtendₗᵢ

end MeasureTheory.Lp
