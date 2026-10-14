import Submission.DifferentialGeometry.Topology.Embedding.GraphChartNeighborhood
import Submission.DifferentialGeometry.Analysis.ODE.SaddleBandCurve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Analysis.ODE (saddleBandCurve saddleBandCurve_zero saddleBandCurve_height)

namespace DifferentialGeometry.Topology.Morse

theorem image_inter_range_eq_saddle_band_time_change
    {E M : Type*} (B : (ℝ × ℝ) ≃ E) {T : E × ℝ → E × ℝ}
    (hT : Function.Injective T) {e : M → E × ℝ} {s ell : ℝ}
    {V W : Set (E × ℝ)}
    (hgraph : W ∩ _root_.Set.range e = W ∩ {p |
      (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
        s + (p.2 - ell)})
    {ψ : ℝ × ℝ → ℝ}
    (hmodel : ∀ p ∈ V, T p =
      (B (saddleBandCurve (B.symm p.1) (ψ (p.2 - ell, (B.symm p.1).1))), p.2))
    (hregular : ∀ p ∈ V, ψ (p.2 - ell, (B.symm p.1).1) = 0 ∨
      (1 - (B.symm p.1).1 ^ 2 ≠ 0 ∧ (B.symm p.1).2 ≠ 0 ∧
        0 ≤ 1 + 2 * (1 - (B.symm p.1).1 ^ 2)⁻¹ *
          ψ (p.2 - ell, (B.symm p.1).1) / (B.symm p.1).2 ^ 2)) :
    T '' (V ∩ W) ∩ _root_.Set.range (T ∘ e) = T '' (V ∩ W) ∩ {p |
      (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
        s + (p.2 - ell) + ψ (p.2 - ell, (B.symm p.1).1)} := by
  have hmodeliff (p : E × ℝ) (hp : p ∈ V) :
      (1 - (B.symm (T p).1).1 ^ 2) * ((B.symm (T p).1).2 ^ 2 + 2 * s) / 2 =
          s + ((T p).2 - ell) + ψ ((T p).2 - ell, (B.symm (T p).1).1) ↔
        (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
          s + (p.2 - ell) := by
    have henergy : (1 - (saddleBandCurve (B.symm p.1)
        (ψ (p.2 - ell, (B.symm p.1).1))).1 ^ 2) *
        ((saddleBandCurve (B.symm p.1) (ψ (p.2 - ell, (B.symm p.1).1))).2 ^ 2 +
          2 * s) / 2 =
        (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 +
          ψ (p.2 - ell, (B.symm p.1).1) := by
      rcases hregular p hp with hz | hr
      · rw [hz, saddleBandCurve_zero, add_zero]
      · simpa only [zero_add] using saddleBandCurve_height hr.1 hr.2.1 hr.2.2 0 s
    rw [hmodel p hp]
    simp only [Equiv.symm_apply_apply]
    change _ = s + (p.2 - ell) + ψ (p.2 - ell, (B.symm p.1).1) ↔ _
    rw [henergy]
    exact add_right_cancel_iff
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, m, hm⟩
    have hxrange : x ∈ _root_.Set.range e := ⟨m, hT hm⟩
    have hxgraph := (hgraph.subset ⟨hx.2, hxrange⟩).2
    exact ⟨⟨x, hx, rfl⟩, (hmodeliff x hx.1).mpr hxgraph⟩
  · rintro ⟨⟨x, hx, rfl⟩, htarget⟩
    have hxgraph := (hmodeliff x hx.1).mp htarget
    obtain ⟨m, hm⟩ := (hgraph.symm.subset ⟨hx.2, hxgraph⟩).2
    exact ⟨⟨x, hx, rfl⟩, m, congrArg T hm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.image_inter_range_eq_saddle_band_time_change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.image_inter_range_eq_saddle_band_time_change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.image_inter_range_eq_saddle_band_time_change ``Submission.DifferentialGeometry.Topology.Morse.image_inter_range_eq_saddle_band_time_change

theorem exists_cthickening_inter_range_comp_eq_saddle_band_time_change
    {E M : Type*} [PseudoMetricSpace E]
    (B : (ℝ × ℝ) ≃ E) (T : (E × ℝ) ≃ₜ (E × ℝ))
    {e : M → E × ℝ} {s ell : ℝ} {V W : Set (E × ℝ)}
    (hV : IsOpen V) (hW : IsOpen W)
    (hgraph : W ∩ _root_.Set.range e = W ∩ {p |
      (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
        s + (p.2 - ell)})
    {ψ : ℝ × ℝ → ℝ}
    (hmodel : ∀ p ∈ V, T p =
      (B (saddleBandCurve (B.symm p.1) (ψ (p.2 - ell, (B.symm p.1).1))), p.2))
    (hregular : ∀ p ∈ V, ψ (p.2 - ell, (B.symm p.1).1) = 0 ∨
      (1 - (B.symm p.1).1 ^ 2 ≠ 0 ∧ (B.symm p.1).2 ≠ 0 ∧
        0 ≤ 1 + 2 * (1 - (B.symm p.1).1 ^ 2)⁻¹ *
          ψ (p.2 - ell, (B.symm p.1).1) / (B.symm p.1).2 ^ 2))
    {K : Set (E × ℝ)} (hK : IsCompact K) (hKV : K ⊆ V) (hKW : K ⊆ W) :
    ∃ Z : Set (E × ℝ), Z = T '' (V ∩ W) ∧ IsOpen Z ∧ Z ⊆ T '' V ∧
      T '' K ⊆ Z ∧
      Z ∩ _root_.Set.range (T ∘ e) = Z ∩ {p |
        (1 - (B.symm p.1).1 ^ 2) * ((B.symm p.1).2 ^ 2 + 2 * s) / 2 =
          s + (p.2 - ell) + ψ (p.2 - ell, (B.symm p.1).1)} ∧
      ∃ ε > 0, _root_.Metric.cthickening ε (T '' K) ⊆ Z := by
  let Z := T '' (V ∩ W)
  have hZ : IsOpen Z := T.isOpenMap _ (hV.inter hW)
  have hKZ : T '' K ⊆ Z := _root_.Set.image_mono (_root_.Set.subset_inter hKV hKW)
  obtain ⟨ε, hε, hεZ⟩ := (hK.image T.continuous).exists_cthickening_subset_open hZ hKZ
  exact ⟨Z, rfl, hZ, _root_.Set.image_mono _root_.Set.inter_subset_left, hKZ,
    image_inter_range_eq_saddle_band_time_change B T.injective hgraph hmodel hregular,
    ε, hε, hεZ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change ``Submission.DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change

end DifferentialGeometry.Topology.Morse

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_comp_eq_saddle_band_time_change
    {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ P H} [I.Boundaryless] [IsManifold I ∞ M]
    {e : M → (ℝ × ℝ) × ℝ} (he : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, (ℝ × ℝ) × ℝ) ∞ e)
    (T : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ))
    {s ell : ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ P)
    (hgraph : (fun z : ℝ × ℝ => (z, ell + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' U ⊆
      _root_.Set.range e)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {W : Set ((ℝ × ℝ) × ℝ)} (hW : IsOpen W)
    (hKW : (fun z : ℝ × ℝ => (z, ell + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' K ⊆ W)
    {ψ : ℝ × ℝ → ℝ}
    (hmodel : ∀ p ∈ W, T p = (saddleBandCurve p.1 (ψ (p.2 - ell, p.1.1)), p.2))
    (hregular : ∀ p ∈ W, ψ (p.2 - ell, p.1.1) = 0 ∨
      (1 - p.1.1 ^ 2 ≠ 0 ∧ p.1.2 ≠ 0 ∧
        0 ≤ 1 + 2 * (1 - p.1.1 ^ 2)⁻¹ * ψ (p.2 - ell, p.1.1) / p.1.2 ^ 2)) :
    ∃ V : Set ((ℝ × ℝ) × ℝ), IsOpen V ∧ V ⊆ T '' W ∧
      V ∩ _root_.Set.range (T ∘ e) = V ∩ {p | (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 =
        s + (p.2 - ell) + ψ (p.2 - ell, p.1.1)} ∧
      ∃ ε > 0, _root_.Metric.cthickening ε
        (T '' ((fun z : ℝ × ℝ => (z, ell + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s)) '' K)) ⊆ V := by
  let q : ℝ × ℝ → ℝ := fun z => ell + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 - s
  have hq : ContDiff ℝ ∞ q := by fun_prop
  obtain ⟨V₀, hV₀, hgraphV₀, _, hV₀eq⟩ :=
    he.exists_isOpen_inter_range_eq_graph hU hq.contDiffOn hdim hgraph
  have henergy : V₀ ∩ _root_.Set.range e = V₀ ∩
      {p | (1 - p.1.1 ^ 2) * (p.1.2 ^ 2 + 2 * s) / 2 = s + (p.2 - ell)} := by
    rw [hV₀eq]
    ext p
    simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_ofPred_eq]
    apply and_congr_right
    intro _
    dsimp only [q]
    constructor <;> intro h <;> linarith
  have hcompact : IsCompact ((fun z => (z, q z)) '' K) :=
    hK.image (continuous_id.prodMk hq.continuous)
  have hsubset : (fun z => (z, q z)) '' K ⊆ V₀ :=
    (_root_.Set.image_mono hKU).trans hgraphV₀
  obtain ⟨V, _, hV, hVW, _, hVeq, ε, hε, hεV⟩ :=
    DifferentialGeometry.Topology.Morse.exists_cthickening_inter_range_comp_eq_saddle_band_time_change
      (Equiv.refl (ℝ × ℝ)) T hW hV₀ henergy hmodel hregular hcompact hKW hsubset
  exact ⟨V, hV, hVW, hVeq, ε, hε, hεV⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_comp_eq_saddle_band_time_change then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_comp_eq_saddle_band_time_change"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_comp_eq_saddle_band_time_change ``Submission.Manifold.IsSmoothEmbedding.exists_cthickening_inter_range_comp_eq_saddle_band_time_change
