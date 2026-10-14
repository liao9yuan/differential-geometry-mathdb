import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology _root_.Filter
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

private theorem exists_cutoff_smul_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (s ∩ U)) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g s ∧ HasCompactSupport g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let φ : ContDiffBump x :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hφU : tsupport φ ⊆ U := by
    rw [φ.tsupport_eq]
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    have hh : _root_.Dist.dist y x ≤ r / 2 := hy
    linarith
  let g : E → F := fun y => φ y • f y
  have hg : ContDiffOn ℝ ∞ g s := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact φ.contDiff.contDiffWithinAt.smul
        ((contDiffWithinAt_inter (hU.mem_nhds hyU)).mp (hf y ⟨hy, hyU⟩))
    · have hyφ : y ∉ tsupport φ := fun hh => hyU (hφU hh)
      have heq : g =ᶠ[𝓝 y] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hyφ] with z hz
        change φ z • f z = 0
        rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  refine ⟨g, hg, φ.hasCompactSupport.smul_right, ?_⟩
  filter_upwards [φ.eventuallyEq_one] with y hy
  change φ y • f y = f y
  rw [hy]
  exact one_smul ℝ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_cutoff_smul_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.BoundaryCollar.exists_cutoff_smul_contDiffOn target :: scope.openDecls } }

theorem exists_contDiff_halfSpace_extension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set (ℝ × E)} (hU : IsOpen U) {z : E} (hz : (0, z) ∈ U)
    {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f ((_root_.Set.Ici (0 : ℝ) ×ˢ (_root_.Set.univ : Set E)) ∩ U)) :
    ∃ g : ℝ × E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝[_root_.Set.Ici (0 : ℝ) ×ˢ (_root_.Set.univ : Set E)] (0, z)] f := by
  obtain ⟨f₀, hf₀, _, he₀⟩ := exists_cutoff_smul_contDiffOn hU hz hf
  obtain ⟨G, V, hV, hG, heG⟩ := DifferentialGeometry.Analysis.borel_halfLine_extend_param
    (fun t x => f₀ (t, x)) _root_.Set.univ z (by simp) hf₀
  obtain ⟨W, hWV, hW, hzW⟩ := mem_nhds_iff.mp hV
  have hGW : ContDiffOn ℝ ∞ (_root_.Function.uncurry G) ((_root_.Set.univ : Set ℝ) ×ˢ W) :=
    hG.mono (_root_.Set.prod_mono_right hWV)
  obtain ⟨g, hg, hgK, heg⟩ := exists_cutoff_smul_contDiffOn (s := _root_.Set.univ) (f := _root_.Function.uncurry G)
    (isOpen_univ.prod hW) (show (0, z) ∈ (_root_.Set.univ : Set ℝ) ×ˢ W from ⟨mem_univ _, hzW⟩)
    (by simpa only [_root_.Set.univ_inter] using hGW)
  refine ⟨g, contDiffOn_univ.mp hg, hgK, ?_⟩
  have hWVnhds : (_root_.Set.univ : Set ℝ) ×ˢ W ∈ 𝓝 ((0 : ℝ), z) :=
    (isOpen_univ.prod hW).mem_nhds ⟨mem_univ _, hzW⟩
  filter_upwards [heg.filter_mono nhdsWithin_le_nhds, he₀.filter_mono nhdsWithin_le_nhds,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hWVnhds, self_mem_nhdsWithin]
    with p hpg hp₀ hpW hpH
  exact hpg.trans ((heG p.1 hpH.1 p.2 (hWV hpW.2)).trans hp₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_contDiff_halfSpace_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_contDiff_halfSpace_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_contDiff_halfSpace_extension ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_contDiff_halfSpace_extension

end DifferentialGeometry.Manifold.BoundaryCollar
