import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] FiniteHorn.ambient_metric
attribute [local instance] EndAngles.metric

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

omit [SigmaCompactSpace W] in
theorem not_unrestricted_neckEndScale {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, 0 < d i)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    ¬ (∀ a b : ℝ, -1 < a → a < b → b < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - a) * d i} ⊆ H.subend j ∧
      H.subend j ⊆ {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 + b) * d i} ∧
      (∀ x ∈ H.subend j, (neckTube g H ray d i).height x < 1 / 2)) := by
  intro hscale
  have hspec : ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < (1 - (-0.9)) * d i} ⊆
        H.subend j ∧
      H.subend j ⊆ {x : W | _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint <
        (1 + 0.05) * d i} ∧
      (∀ x ∈ H.subend j, (neckTube g H ray d i).height x < 1 / 2) :=
    hscale (-0.9) 0.05 (by norm_num) (by norm_num) (by norm_num)
  have hlim : Filter.Tendsto (fun i => 1.2 * d i) Filter.atTop (nhds 0) := by
    simpa using hzero.const_mul (1.2 : ℝ)
  have hsmall : ∀ᶠ i in Filter.atTop, 1.2 * d i < H.axial.length :=
    hlim.eventually (eventually_lt_nhds H.axial.length_pos)
  obtain ⟨i, hsi, hi⟩ := (hspec.and hsmall).exists
  obtain ⟨j, hsub, hsup, _⟩ := hsi
  have hmem : 1.2 * d i ∈ Set.Ioc 0 H.axial.length := ⟨by linarith [hd i], hi.le⟩
  have hrad := H.axial.radial (1.2 * d i) hmem
  have hx1 : _root_.Dist.dist (H.axial.point (1.2 * d i) : UniformSpace.Completion W) H.endpoint <
      (1 - (-0.9)) * d i := by
    rw [hrad, show (1 - (-0.9)) * d i = 1.9 * d i by norm_num]
    linarith [hd i]
  have hx2 : _root_.Dist.dist (H.axial.point (1.2 * d i) : UniformSpace.Completion W) H.endpoint <
      (1 + 0.05) * d i := hsup (hsub hx1)
  rw [hrad, show (1 + 0.05) * d i = 1.05 * d i by norm_num] at hx2
  linarith [hd i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_unrestricted_neckEndScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_unrestricted_neckEndScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_unrestricted_neckEndScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_unrestricted_neckEndScale

private theorem radialSpread_lt_half {L eta s e : ℝ} (hL : 0 < L) (heta : 0 < eta)
    (h : (2 * L / eta) ^ 2 < s * e) : L / Real.sqrt (s * e) < eta / 2 := by
  have hpos : 0 < 2 * L / eta := by positivity
  have hlt : 2 * L / eta < Real.sqrt (s * e) := by
    rw [Real.lt_sqrt hpos.le]
    exact h
  have hdiv := div_lt_div_of_pos_left hL hpos hlt
  have heq : L / (2 * L / eta) = eta / 2 := by field_simp
  simpa only [heq] using hdiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialSpread_lt_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radialSpread_lt_half target :: scope.openDecls } }

private theorem div_sqrt_lt_mul {L eta s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (h : L / Real.sqrt (s * d ^ 2) < eta) : L / Real.sqrt s < d * eta := by
  have hsqrt : Real.sqrt (s * d ^ 2) = Real.sqrt s * d := by
    rw [Real.sqrt_mul hs.le, Real.sqrt_sq hd.le]
  rw [hsqrt] at h
  calc L / Real.sqrt s = d * (L / (Real.sqrt s * d)) := by field_simp
    _ < d * eta := mul_lt_mul_of_pos_left h hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.div_sqrt_lt_mul target :: scope.openDecls } }

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_neckEndScaleWindow
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hscale : NeckEndScaleWindow g H ray d) :
    HornRadialExitPositionAtEndChart g H ray d := by
  intro e he he10
  filter_upwards [hscale.2 e he he10,
    hlarge.eventually_ge_atTop (_root_.Max.max 1 ((2 * transverseShortcutConstant W / e) ^ 2 + 1))]
    with i hj hbig
  obtain ⟨j, hsub, hsup⟩ := hj
  intro hx x hxfar
  set E := endChart g H (ray.point (d i)) hx
  have hdpos : 0 < d i := (hd i).1
  have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
    le_trans (le_max_left _ _) hbig
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e / 2 := by
    refine radialSpread_lt_half (transverseShortcutConstant_pos W) he ?_
    have h2 : (2 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
        metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
    linarith
  have hcenter : ∀ q : Sphere 2, E.F (q, 0) ∈ H.subend j := by
    intro q
    have hle : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (e / 2) :=
      div_sqrt_lt_mul hs_pos hdpos hspread
    have hdiam := endChart_section_diameter_le g H (ray.point (d i)) hx (E.F (q, 0))
      (by
        rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
          show (fun r : Sphere 2 => E.cross.tube.map (r, 1 / 2)) =
            (fun r : Sphere 2 => E.F (r, 0)) from funext E.cross.center_eq]
        exact ⟨q, rfl⟩)
    have hlt : _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) < (e / 2) * d i := by
      rw [mul_comm (e / 2) (d i)]
      exact lt_of_le_of_lt hdiam hle
    refine hsub ?_
    calc _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint
        ≤ _root_.Dist.dist (E.F (q, 0) : UniformSpace.Completion W)
            (ray.point (d i) : UniformSpace.Completion W) +
          dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
      _ = _root_.Dist.dist (ray.point (d i)) (E.F (q, 0)) + d i := by
            rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (q, 0)) (ray.point (d i)),
              ray.radial (d i) (hd i)]
      _ < (e / 2) * d i + d i := by linarith
      _ = (1 + e / 2) * d i := by ring
  have hout : x ∉ H.subend j := fun hmem => absurd (hsup hmem) (not_lt.mpr hxfar.le)
  exact GlobalNeckCrossSection.outer_side_of_center_in_subend g H E.cross j hcenter x hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_neckEndScaleWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_neckEndScaleWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_neckEndScaleWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornRadialExitPositionAtEndChart_of_neckEndScaleWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
