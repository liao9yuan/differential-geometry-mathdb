import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Topology

variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {m n : ℕ∞ω} {G : P → E → F} {A : Set P} {V : Set E}

open _root_.ContDiffOn in
theorem ContDiffOn.fderiv_snd
    (hG : ContDiffOn 𝕜 n (Function.uncurry G) (A ×ˢ V))
    (hV : IsOpen V) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p : P × E => fderiv 𝕜 (G p.1) p.2) (A ×ˢ V) := by
  have hwithin : ContDiffOn 𝕜 m
      (fun p : P × E => fderivWithin 𝕜 (G p.1) V p.2) (A ×ˢ V) := by
    intro p hp
    have harg : ContDiffWithinAt 𝕜 n
        (fun q : (P × E) × E => (q.1.1, q.2)) ((A ×ˢ V) ×ˢ V) (p, p.2) :=
      contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd
    have hf : ContDiffWithinAt 𝕜 n
        (fun q : (P × E) × E => G q.1.1 q.2) ((A ×ˢ V) ×ˢ V) (p, p.2) :=
      (hG p hp).comp (g := Function.uncurry G) (p, p.2) harg
        (show _root_.Set.MapsTo (fun q : (P × E) × E => (q.1.1, q.2))
          ((A ×ˢ V) ×ˢ V) (A ×ˢ V) from fun _ hq => ⟨hq.1.1, hq.2⟩)
    exact hf.fderivWithin contDiffWithinAt_snd hV.uniqueDiffOn hmn hp (fun _ h => h.2)
  apply hwithin.congr
  intro p hp
  exact (fderivWithin_of_isOpen hV hp.2).symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContDiffOn
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.fderiv_snd then
    throwError "Refusing to shadow existing declaration ContDiffOn.fderiv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.fderiv_snd ``Submission.ContDiffOn.fderiv_snd

open _root_.ContDiffOn in
theorem ContDiffOn.iteratedFDeriv_snd
    (hG : ContDiffOn 𝕜 n (Function.uncurry G) (A ×ˢ V))
    (hV : IsOpen V) (r : ℕ) (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m (fun p : P × E => iteratedFDeriv 𝕜 r (G p.1) p.2) (A ×ˢ V) := by
  induction r generalizing m with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.contDiff.comp_contDiffOn
      (hG.of_le (by simpa using hmn))
  | succ r ih =>
    have hr : (m + 1) + r ≤ n := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hmn
    let : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) F) :=
      ContinuousMultilinearMap.normedAddCommGroup
    let : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) F) :=
      ContinuousMultilinearMap.normedSpace
    have hd := (ih hr).fderiv_snd (G := fun p x => iteratedFDeriv 𝕜 r (G p) x) hV le_rfl
    exact (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (r + 1) => E) F).symm.contDiff.comp_contDiffOn hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.iteratedFDeriv_snd then
    throwError "Refusing to shadow existing declaration ContDiffOn.iteratedFDeriv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.iteratedFDeriv_snd ``Submission.ContDiffOn.iteratedFDeriv_snd

open _root_.ContDiffOn in
theorem ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_snd
    (hG : ContDiffOn 𝕜 n (Function.uncurry G) (A ×ˢ V))
    (hV : IsOpen V) {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (r : ℕ) (hr : r ≤ n) {p : P} (hp : p ∈ A) :
    TendstoUniformlyOn (fun q => iteratedFDeriv 𝕜 r (G q))
      (iteratedFDeriv 𝕜 r (G p)) (𝓝[A] p) K := by
  have hc := (hG.iteratedFDeriv_snd hV r (m := 0) (by simpa using hr)).continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W, hW, hsmall⟩ := hK.mem_uniformity_of_prod (f := fun q x => iteratedFDeriv 𝕜 r (G q) x)
    (hc.mono (_root_.Set.prod_mono_right hKV)) hp (Metric.dist_mem_uniformity hε)
  filter_upwards [hW] with q hq
  intro x hx
  have hh : _root_.Dist.dist (iteratedFDeriv 𝕜 r (G q) x) (iteratedFDeriv 𝕜 r (G p) x) < ε :=
    hsmall q hq x hx
  simpa only [dist_comm] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_snd then
    throwError "Refusing to shadow existing declaration ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_snd ``Submission.ContDiffOn.tendstoUniformlyOn_iteratedFDeriv_snd

namespace DifferentialGeometry.Analysis

theorem spatial_iteratedFDeriv_contDiffOn
    {G : P → E → F} {J : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ContDiffOn 𝕜 ∞ (Function.uncurry G) (J ×ˢ V)) (r : ℕ) :
    ContDiffOn 𝕜 ∞ (fun p : P × E => iteratedFDeriv 𝕜 r (G p.1) p.2) (J ×ˢ V) :=
  hG.iteratedFDeriv_snd hV r (m := ∞)
    (by exact_mod_cast (le_top : (⊤ : ℕ∞) + (r : ℕ∞) ≤ ⊤))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn ``Submission.DifferentialGeometry.Analysis.spatial_iteratedFDeriv_contDiffOn

theorem exists_bound_spatial_iteratedFDeriv_on_compact
    {ι : Type*} [Finite ι] {G : ι → P → E → F} {J : Set P} {V K : ι → Set E}
    (hV : ∀ i, IsOpen (V i)) (hJc : IsCompact J)
    (hK : ∀ i, IsCompact (K i))
    (hKV : ∀ i, K i ⊆ V i)
    (hG : ∀ i, ContDiffOn 𝕜 n (Function.uncurry (G i)) (J ×ˢ V i))
    (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ i t, t ∈ J → ∀ x ∈ K i, ‖iteratedFDeriv 𝕜 k (G i t) x‖ ≤ C := by
  let f := fun i (p : P × E) => iteratedFDeriv 𝕜 k (G i p.1) p.2
  have hc (i : ι) : ContinuousOn (f i) (J ×ˢ K i) :=
    ((hG i).iteratedFDeriv_snd (hV i) k (m := 0) (by simpa using hk)).continuousOn.mono
      (_root_.Set.prod_mono_right (hKV i))
  have hcompact : IsCompact (⋃ i, f i '' (J ×ˢ K i)) :=
    isCompact_iUnion (fun i => (hJc.prod (hK i)).image_of_continuousOn (hc i))
  obtain ⟨C, hC, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun i t ht x hx => hbound _ (mem_iUnion.mpr ⟨i, ⟨(t, x), ⟨ht, hx⟩, rfl⟩⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact ``Submission.DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact

end DifferentialGeometry.Analysis
