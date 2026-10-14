import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Algebra.Structures

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def sublevelCutoff (ρ : C^∞⟮I, M; ℝ⟯) (R : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => CutoffProfile.value (ρ x / R),
    CutoffProfile.contDiff.contMDiff.comp (ρ.contMDiff.div_const R)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sublevelCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sublevelCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sublevelCutoff ``Submission.DifferentialGeometry.Analysis.sublevelCutoff

theorem sublevelCutoff_mem_Icc (ρ : C^∞⟮I, M; ℝ⟯) (R : ℝ) (x : M) :
    sublevelCutoff ρ R x ∈ Set.Icc 0 1 :=
  CutoffProfile.mem_Icc _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sublevelCutoff_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sublevelCutoff_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sublevelCutoff_mem_Icc ``Submission.DifferentialGeometry.Analysis.sublevelCutoff_mem_Icc

theorem sublevelCutoff_eq_one (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R)
    {x : M} (hx : ρ x ≤ R) : sublevelCutoff ρ R x = 1 := by
  exact CutoffProfile.one_of_le_one ((div_le_one hR).2 hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sublevelCutoff_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sublevelCutoff_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sublevelCutoff_eq_one ``Submission.DifferentialGeometry.Analysis.sublevelCutoff_eq_one

theorem tsupport_sublevelCutoff_subset (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R) :
    tsupport (sublevelCutoff ρ R) ⊆ {x | ρ x ≤ 2 * R} :=
  CutoffProfile.tsupport_value_comp_div_subset_sublevel ρ.contMDiff.continuous hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tsupport_sublevelCutoff_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tsupport_sublevelCutoff_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tsupport_sublevelCutoff_subset ``Submission.DifferentialGeometry.Analysis.tsupport_sublevelCutoff_subset

theorem hasCompactSupport_sublevelCutoff (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R)
    (hc : IsCompact {x | ρ x ≤ 2 * R}) : HasCompactSupport (sublevelCutoff ρ R) :=
  CutoffProfile.hasCompactSupport_value_comp_div ρ.contMDiff.continuous hR hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasCompactSupport_sublevelCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasCompactSupport_sublevelCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasCompactSupport_sublevelCutoff ``Submission.DifferentialGeometry.Analysis.hasCompactSupport_sublevelCutoff

theorem sublevelCutoff_eventually_eq_one (ρ : C^∞⟮I, M; ℝ⟯) (x : M) :
    ∀ᶠ R in _root_.Filter.atTop, sublevelCutoff ρ R x = 1 := by
  filter_upwards [_root_.Filter.eventually_gt_atTop (0 : ℝ), _root_.Filter.eventually_ge_atTop (ρ x)] with R hR hx
  exact sublevelCutoff_eq_one ρ hR hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one ``Submission.DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one

theorem sublevelCutoff_eventually_eq_one_on_compact (ρ : C^∞⟮I, M; ℝ⟯)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ R in _root_.Filter.atTop, ∀ x ∈ K, sublevelCutoff ρ R x = 1 := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image ρ.contMDiff.continuous.continuousOn
  filter_upwards [_root_.Filter.eventually_gt_atTop (0 : ℝ), _root_.Filter.eventually_ge_atTop B] with R hR hBR x hx
  exact sublevelCutoff_eq_one ρ hR ((hB (Set.mem_image_of_mem ρ hx)).trans hBR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one_on_compact ``Submission.DifferentialGeometry.Analysis.sublevelCutoff_eventually_eq_one_on_compact

end DifferentialGeometry.Analysis
