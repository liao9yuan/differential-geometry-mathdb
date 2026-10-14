import Submission.DifferentialGeometry.Analysis.Calculus.Smoothness.ExtendInterval
import Submission.DifferentialGeometry.Topology.Manifold.SmoothExtension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Filter _root_.Function
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (k : ℕ) M]

theorem exists_contMDiffOn_local_extension_Icc
    {a b : ℝ} {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (_root_.Set.Icc a b))
    {x : ℝ} (hx : x ∈ _root_.Set.Icc a b) :
    ∃ U : ℝ → M, ∃ V : Set ℝ,
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) U V ∧
        EqOn U gamma (_root_.Set.Icc a b ∩ V) := by
  let p : M := gamma x
  have hsrcNear : gamma ⁻¹' (chartAt H p).source ∈ 𝓝[_root_.Set.Icc a b] x := by
    have hc := hgamma.continuousOn x hx
    exact hc ((chartAt H p).open_source.mem_nhds (by
      simpa only [p] using mem_chart_source H (gamma x)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hsrcNear
  let c := _root_.Max.max a (x - r / 2)
  let d := _root_.Min.min b (x + r / 2)
  have hsub : _root_.Set.Icc c d ⊆ _root_.Set.Icc a b := by
    intro t ht
    exact ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hxsmall : x ∈ _root_.Set.Icc c d := by
    constructor
    · exact max_le hx.1 (by linarith)
    · exact le_min hx.2 (by linarith)
  have hsrc : _root_.Set.MapsTo gamma (_root_.Set.Icc c d) (chartAt H p).source := by
    intro t ht
    apply hball
    refine ⟨?_, hsub ht⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have hh := (le_max_right a (x - r / 2)).trans ht.1
      linarith
    · have hh := ht.2.trans (min_le_right b (x + r / 2))
      linarith
  have hchart : ContDiffOn ℝ (k : ℕ) ((extChartAt I p) ∘ gamma) (_root_.Set.Icc c d) :=
    ((contMDiffOn_extChartAt (I := I) (n := (k : ℕ∞)) (x := p)).comp
      (hgamma.mono hsub) hsrc).contDiffOn
  obtain ⟨g, hg, hgeq⟩ := Analysis.exists_contDiff_extension_Icc k _ hchart
  let V := g ⁻¹' (extChartAt I p).target ∩ _root_.Set.Ioo (x - r / 2) (x + r / 2)
  have hV : IsOpen V :=
    ((isOpen_extChartAt_target (I := I) p).preimage hg.continuous).inter isOpen_Ioo
  have hxV : x ∈ V := by
    refine ⟨?_, ⟨by linarith, by linarith⟩⟩
    rw [_root_.Set.mem_preimage, hgeq hxsmall]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc hxsmall)
  refine ⟨(extChartAt I p).symm ∘ g, V, hV, hxV,
    (contMDiffOn_extChartAt_symm (I := I) (n := (k : ℕ∞)) p).comp
      hg.contMDiff.contMDiffOn (fun _ ht => ht.1), ?_⟩
  intro t ht
  have htsmall : t ∈ _root_.Set.Icc c d :=
    ⟨max_le ht.1.1 ht.2.2.1.le, le_min ht.1.2 ht.2.2.2.le⟩
  change (extChartAt I p).symm (g t) = gamma t
  rw [hgeq htsmall]
  exact (extChartAt I p).left_inv (by
    rw [extChartAt_source]
    exact hsrc htsmall)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiffOn_local_extension_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiffOn_local_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiffOn_local_extension_Icc ``Submission.DifferentialGeometry.Topology.exists_contMDiffOn_local_extension_Icc

end DifferentialGeometry.Topology

end
section

open _root_.Set _root_.Filter _root_.Function
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (k : ℕ) M]

private theorem exists_contMDiff_extension_Icc_of_lt
    {a b : ℝ} (hab : a < b) {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (_root_.Set.Icc a b)) :
    ∃ g : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (k : ℕ) g ∧ _root_.Set.EqOn g gamma (_root_.Set.Icc a b) := by
  let gamma0 : ℝ → M := _root_.Set.IccExtend hab.le (fun t : _root_.Set.Icc a b => gamma t)
  have h0 : Continuous gamma0 :=
    (continuous_IccExtend_iff (h := hab.le)).mpr
      (continuousOn_iff_continuous_domRestrict.mp hgamma.continuousOn)
  have h0eq : _root_.Set.EqOn gamma0 gamma (_root_.Set.Icc a b) := by
    intro t ht
    exact _root_.Set.IccExtend_of_mem hab.le _ ht
  obtain ⟨g, _, hgeq, N, hN, hsub, hgs⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (I := I) (n := (k : ℕ∞)) h0 _root_.CompactIccSpace.isCompact_Icc (by
      intro t ht
      obtain ⟨U, V, hV, htV, hU, heq⟩ := exists_contMDiffOn_local_extension_Icc hgamma ht
      refine ⟨U, V, hV, htV, hU, ?_⟩
      intro s hs
      exact (heq hs).trans (h0eq hs.1).symm)
  obtain ⟨G, hG, hGeq⟩ := hgs.exists_extension_uIcc (a := a) (b := b) hN (by
    simpa only [_root_.Set.uIcc_of_le hab.le] using hsub)
  refine ⟨G, hG, ?_⟩
  intro t ht
  exact ((hGeq t (by simpa only [_root_.Set.uIcc_of_le hab.le] using ht)).self_of_nhds).trans
    ((hgeq ht).trans (h0eq ht))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exists_contMDiff_extension_Icc_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exists_contMDiff_extension_Icc_of_lt target :: scope.openDecls } }

theorem exists_contMDiff_extension_Icc
    {a b : ℝ} {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (_root_.Set.Icc a b)) :
    ∃ g : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (k : ℕ) g ∧ _root_.Set.EqOn g gamma (_root_.Set.Icc a b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact exists_contMDiff_extension_Icc_of_lt hab hgamma
  · subst b
    refine ⟨fun _ ↦ gamma a, contMDiff_const, ?_⟩
    intro t ht
    have ht' : t = a := le_antisymm ht.2 ht.1
    rw [ht']
  · refine ⟨fun _ ↦ gamma a, contMDiff_const, ?_⟩
    simp only [_root_.Set.Icc_eq_empty_of_lt hab, _root_.Set.eqOn_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiff_extension_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiff_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiff_extension_Icc ``Submission.DifferentialGeometry.Topology.exists_contMDiff_extension_Icc

end DifferentialGeometry.Topology

end
