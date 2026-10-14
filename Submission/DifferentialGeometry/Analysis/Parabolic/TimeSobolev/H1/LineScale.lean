import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X] [CompleteSpace X]
variable {T : Real}

namespace timeH1

omit [CompleteSpace X] in
theorem exists_line_scale (u v : timeH1 X T) {U : Set X} (hU : IsOpen U)
    (hu : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) T) U) :
    ∃ scale : Real, 0 < scale ∧ scale ≤ 1 ∧
      _root_.Set.MapsTo
        (fun q : Real × Real ↦
          u.toFun q.2 + q.1 • (scale • v).toFun q.2)
        (_root_.Set.Icc (-1 : Real) 1 ×ˢ _root_.Set.Icc (0 : Real) T) U := by
  let K : Set X := u.toFun '' _root_.Set.Icc (0 : Real) T
  have hKcompact : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hu ht
  obtain ⟨δ, hδ, hδU⟩ := hKcompact.exists_cthickening_subset_open hU hKU
  obtain ⟨V₀, hV₀⟩ := isCompact_Icc.bddAbove_image
    v.continuousOn_toFun.norm
  let V : Real := _root_.Max.max V₀ 0
  have hV0 : 0 ≤ V := le_max_right V₀ 0
  have hV : ∀ t ∈ _root_.Set.Icc (0 : Real) T, ‖v.toFun t‖ ≤ V := by
    intro t ht
    exact (hV₀ ⟨t, ht, rfl⟩).trans (le_max_left V₀ 0)
  let raw : Real := δ / (V + 1)
  have hden : 0 < V + 1 := by linarith
  have hraw : 0 < raw := div_pos hδ hden
  have hrawV : raw * V ≤ δ := by
    calc
      raw * V ≤ raw * (V + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hraw.le
      _ = δ := by
        dsimp only [raw]
        field_simp
  let scale : Real := _root_.Min.min raw 1
  have hscale : 0 < scale := lt_min hraw zero_lt_one
  have hscale1 : scale ≤ 1 := min_le_right raw 1
  have hscaleRaw : scale ≤ raw := min_le_left raw 1
  refine ⟨scale, hscale, hscale1, ?_⟩
  intro q hq
  apply hδU
  refine Metric.mem_cthickening_of_dist_le
    (u.toFun q.2 + q.1 • (scale • v).toFun q.2) (u.toFun q.2) δ K
    ⟨q.2, hq.2, rfl⟩ ?_
  rw [dist_eq_norm, add_sub_cancel_left,
    timeH1.toFun_smul scale v hq.2, smul_smul, norm_smul]
  have hc : ‖q.1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact hq.1
  have hs : ‖q.1 * scale‖ ≤ scale := by
    calc
      ‖q.1 * scale‖ = ‖q.1‖ * scale := by
        rw [norm_mul, show ‖scale‖ = scale by
          rw [Real.norm_eq_abs, abs_of_pos hscale]]
      _ ≤ 1 * scale := mul_le_mul_of_nonneg_right hc hscale.le
      _ = scale := one_mul scale
  calc
    ‖q.1 * scale‖ * ‖v.toFun q.2‖ ≤ scale * V := by
      exact mul_le_mul hs (hV q.2 hq.2) (norm_nonneg _) hscale.le
    _ ≤ raw * V := mul_le_mul_of_nonneg_right hscaleRaw hV0
    _ ≤ δ := hrawV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_line_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_line_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_line_scale ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_line_scale

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
