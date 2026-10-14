import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace ContDiffOn
open _root_.ContDiffOn

open _root_.Set

open _root_.ContDiffOn in
theorem exists_contDiff_extension_Ici_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {a : ℝ} (hf : ContDiffOn ℝ ∞ f (_root_.Set.Ici a ×ˢ _root_.Set.univ)) :
    ∃ G : ℝ × E → F, ContDiff ℝ ∞ G ∧ _root_.Set.EqOn G f (_root_.Set.Ici a ×ˢ _root_.Set.univ) := by
  let g : ℝ → E → F := fun t z => f (t + a, z)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (_root_.Set.Ici 0 ×ˢ _root_.Set.univ) :=
    hf.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨mem_Ici.mpr (le_add_of_nonneg_left (mem_Ici.mp hq.1)), _root_.Set.mem_univ _⟩)
  let C : ℝ × E → Set F := fun q => {v | a ≤ q.1 → v = f q}
  have hC (q : ℝ × E) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro u hu v hv s t _ _ hsum hq
    rw [hu hq, hv hq, ← add_smul, hsum, one_smul]
  have hlocal (q₀ : ℝ × E) : ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × E → F,
      ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) ∞ G U ∧ ∀ q ∈ U, G q ∈ C q := by
    obtain ⟨gext, V, hV, hgext, hgeq⟩ :=
      DifferentialGeometry.Analysis.borel_halfLine_extend_param
        g _root_.Set.univ q₀.2 (by simp) hg
    refine ⟨univ ×ˢ V, prod_mem_nhds (by simp) hV,
      fun q => gext (q.1 - a) q.2, ?_, ?_⟩
    · apply contMDiffOn_iff_contDiffOn.mpr
      exact hgext.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
        (fun _ hq => ⟨mem_univ _, hq.2⟩)
    · intro q hq ha
      change gext (q.1 - a) q.2 = f q
      simpa only [g, sub_add_cancel] using hgeq (q.1 - a) (sub_nonneg.mpr ha) q.2 hq.2
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ × E)) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff.contDiff, fun q hq => hG q (mem_Ici.mp hq.1)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.exists_contDiff_extension_Ici_prod then
    throwError "Refusing to shadow existing declaration ContDiffOn.exists_contDiff_extension_Ici_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.exists_contDiff_extension_Ici_prod ``Submission.ContDiffOn.exists_contDiff_extension_Ici_prod

open _root_.ContDiffOn in
theorem exists_contDiff_extension_Ici_prod_nhdsWithin
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {a : ℝ} {U : Set (ℝ × E)}
    (hf : ContDiffOn ℝ ∞ f ((_root_.Set.Ici a ×ˢ _root_.Set.univ) ∩ U))
    (hU : IsOpen U) {x : ℝ × E} (hx : x ∈ U) :
    ∃ G : ℝ × E → F, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝[_root_.Set.Ici a ×ˢ _root_.Set.univ] x] f := by
  obtain ⟨g, hg, -, hgeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_cutoff_extension hU hf hx
  obtain ⟨G, hG, hGg⟩ := hg.exists_contDiff_extension_Ici_prod
  refine ⟨G, hG, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hgeq.filter_mono nhdsWithin_le_nhds] with y hy hyeq
  exact (hGg hy).trans hyeq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin then
    throwError "Refusing to shadow existing declaration ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin ``Submission.ContDiffOn.exists_contDiff_extension_Ici_prod_nhdsWithin

end ContDiffOn
