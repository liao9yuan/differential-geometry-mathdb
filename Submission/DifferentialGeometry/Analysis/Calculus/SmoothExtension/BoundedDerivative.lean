import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_contDiff_extension_fderiv_bound
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) :
    ∃ R : F → F, ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧ R =ᶠ[𝓝ˢ K] r ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ R y‖ ≤ C := by
  obtain ⟨R, hR, hRc, hReq⟩ := exists_contDiff_compactSupport_extension_on_isCompact hK hU hKU hr
  obtain ⟨C, hC⟩ := (hR.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hRc.fderiv (𝕜 := ℝ))
  exact ⟨R, hR, hRc, hReq, _root_.Max.max C 0, le_max_right _ _, fun y =>
    (hC y).trans (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_extension_fderiv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_extension_fderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_extension_fderiv_bound ``Submission.DifferentialGeometry.Analysis.exists_contDiff_extension_fderiv_bound

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_contDiff_retraction_extension_fderiv_bound
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U)
    (hmap : _root_.Set.MapsTo r U K) (hfix : ∀ y ∈ K, r y = y) :
    ∃ (V : Set F) (R : F → F) (C : ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ _root_.Set.EqOn R r V ∧
      ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧
      0 ≤ C ∧ (∀ y, ‖fderiv ℝ R y‖ ≤ C) ∧
      MapsTo R V K ∧ (∀ y ∈ K, R y = y) := by
  obtain ⟨R, hR, hRc, hReq, C, hC, hCb⟩ :=
    exists_contDiff_extension_fderiv_bound hK hU hKU r hr
  have hnear : ∀ᶠ y in 𝓝ˢ K, R y = r y ∧ y ∈ U :=
    hReq.and (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨V, hV, hKV, hVU⟩ := eventually_nhdsSet_iff_exists.mp hnear
  refine ⟨V, R, C, hV, hKV, (fun y hy => (hVU y hy).2),
    (fun y hy => (hVU y hy).1), hR, hRc, hC, hCb, ?_, ?_⟩
  · intro y hy
    rw [(hVU y hy).1]
    exact hmap (hVU y hy).2
  · intro y hy
    exact ((hVU y (hKV hy)).1).trans (hfix y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound ``Submission.DifferentialGeometry.Analysis.exists_contDiff_retraction_extension_fderiv_bound

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)
variable {ι : Type*} [Fintype ι]
local notation "F" => EuclideanSpace ℝ ι

theorem exists_contDiff_extension_eq_fixed_on_compact
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hfix : ∀ y ∈ K, r y = y) :
    ∃ R : F → F, ContDiff ℝ ∞ R ∧ HasCompactSupport R ∧
      (∀ y ∈ K, R y = y) ∧
      (∀ y ∈ K, fderiv ℝ R y = fderiv ℝ r y) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ R y‖ ≤ C := by
  obtain ⟨R, hR, hRc, hReq, C, hC, hCb⟩ :=
    Analysis.exists_contDiff_extension_fderiv_bound hK hU hKU r hr
  refine ⟨R, hR, hRc, ?_, ?_, C, hC, hCb⟩
  · intro y hy
    exact ((hReq.filter_mono (nhds_le_nhdsSet hy)).eq_of_nhds).trans (hfix y hy)
  · intro y hy
    exact (hReq.filter_mono (nhds_le_nhdsSet hy)).fderiv_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiff_extension_eq_fixed_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiff_extension_eq_fixed_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiff_extension_eq_fixed_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiff_extension_eq_fixed_on_compact

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.Metric
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_contDiff_extension_compact_image_fderiv_bound
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hfix : ∀ y ∈ K, r y = y) :
    ∃ (V K' : Set F) (T : F → F) (C : ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ _root_.Set.EqOn T r V ∧
      ContDiff ℝ ∞ T ∧ HasCompactSupport T ∧
      0 ≤ C ∧ (∀ y, ‖fderiv ℝ T y‖ ≤ C) ∧
      IsCompact K' ∧ K' ⊆ U ∧ K' ⊆ r '' U ∧
      MapsTo T V K' ∧ (∀ y ∈ K, T y = y) := by
  obtain ⟨T, hT, hTs, heq, C, hC, hCb⟩ :=
    exists_contDiff_extension_fderiv_bound hK hU hKU r hr
  have hTf (y : F) (hy : y ∈ K) : T y = y :=
    ((heq.filter_mono (nhds_le_nhdsSet hy)).eq_of_nhds).trans (hfix y hy)
  have hnear : ∀ᶠ y in 𝓝ˢ K, T y = r y ∧ y ∈ U :=
    heq.and (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨W, hW, hKW, hWprop⟩ := eventually_nhdsSet_iff_exists.mp hnear
  let O := W ∩ T ⁻¹' U
  have hO : IsOpen O := hW.inter (hU.preimage hT.continuous)
  have hKO : K ⊆ O := by
    intro y hy
    refine ⟨hKW hy, ?_⟩
    change T y ∈ U
    rw [hTf y hy]
    exact hKU hy
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let A := _root_.Metric.cthickening δ K
  let V := _root_.Metric.thickening δ K
  let K' := T '' A
  have hVA : V ⊆ A := _root_.Metric.thickening_subset_cthickening δ K
  have hVU : V ⊆ U := fun y hy => (hWprop y (hδO (hVA hy)).1).2
  refine ⟨V, K', T, C, _root_.Metric.isOpen_thickening, _root_.Metric.self_subset_thickening hδ K,
    hVU, (fun y hy => (hWprop y (hδO (hVA hy)).1).1), hT, hTs, hC, hCb,
    hK.cthickening.image hT.continuous, ?_, ?_, ?_, hTf⟩
  · rintro y ⟨x, hx, rfl⟩
    exact (hδO hx).2
  · rintro y ⟨x, hx, rfl⟩
    have hxW := hWprop x (hδO hx).1
    exact ⟨x, hxW.2, hxW.1.symm⟩
  · intro y hy
    exact _root_.Set.mem_image_of_mem T (hVA hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiff_extension_compact_image_fderiv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiff_extension_compact_image_fderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiff_extension_compact_image_fderiv_bound ``Submission.DifferentialGeometry.Analysis.exists_contDiff_extension_compact_image_fderiv_bound

end DifferentialGeometry.Analysis

end

end
