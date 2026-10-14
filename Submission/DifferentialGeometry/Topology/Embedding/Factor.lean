import Submission.DifferentialGeometry.Topology.Manifold.ImmersionRange
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.Interval.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F V : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {H G P M N Q : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace Q] [ChartedSpace P Q]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {K : ModelWithCorners 𝕜 V P} [I.Boundaryless] [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {g : N → Q}

open _root_.Manifold _root_.Manifold.IsImmersion in
theorem IsImmersion.of_comp (h : _root_.Manifold.IsImmersion I K n (g ∘ f)) (hn : n ≠ 0)
    (hf : ContMDiff I J n f) (hg : ContMDiff J K n g) : _root_.Manifold.IsImmersion I J n f := by
  apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv hn hf
  intro x
  have hinj := (h.isImmersionAt x).injective_mfderiv hn
  rw [mfderiv_comp x (hg.mdifferentiableAt hn) (hf.mdifferentiableAt hn)] at hinj
  exact Function.Injective.of_comp hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.of_comp then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.of_comp ``Submission.Manifold.IsImmersion.of_comp

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.of_comp (h : _root_.Manifold.IsSmoothEmbedding I K n (g ∘ f)) (hn : n ≠ 0)
    (hf : ContMDiff I J n f) (hg : ContMDiff J K n g) : _root_.Manifold.IsSmoothEmbedding I J n f :=
  ⟨h.isImmersion.of_comp hn hf hg,
    _root_.Topology.IsEmbedding.of_comp hf.continuous hg.continuous h.isEmbedding⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.of_comp then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.of_comp ``Submission.Manifold.IsSmoothEmbedding.of_comp

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.fst_of_snd_eq_const
    {f : M → F × V} {a : V} (h : _root_.Manifold.IsSmoothEmbedding I 𝓘(𝕜, F × V) n f)
    (hn : n ≠ 0) (hsnd : ∀ x, (f x).2 = a) :
    IsSmoothEmbedding I 𝓘(𝕜, F) n (fun x => (f x).1) := by
  let p : M → F := fun x => (f x).1
  let j : F → F × V := fun y => (y, a)
  have hp : ContMDiff I 𝓘(𝕜, F) n p := contDiff_fst.contMDiff.comp h.contMDiff
  have hj : ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, F × V) n j :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have heq : j ∘ p = f := by
    funext x
    exact Prod.ext rfl (hsnd x).symm
  have hh : _root_.Manifold.IsSmoothEmbedding I 𝓘(𝕜, F × V) n (j ∘ p) := heq ▸ h
  exact hh.of_comp hn hp hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.fst_of_snd_eq_const then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.fst_of_snd_eq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.fst_of_snd_eq_const ``Submission.Manifold.IsSmoothEmbedding.fst_of_snd_eq_const


open _root_.Manifold _root_.Manifold.IsImmersion in
theorem IsImmersion.isOpen_preimage_range_of_range_subset
    {e : M → Q} (he : _root_.Manifold.IsImmersion I K n e) (hg : _root_.Manifold.IsSmoothEmbedding J K n g)
    (hn : n ≠ 0) (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F)
    (hsub : Set.range e ⊆ Set.range g) : IsOpen (g ⁻¹' Set.range e) := by
  let q : M → N := fun x => hg.isEmbedding.toHomeomorph.symm
    ⟨e x, hsub (Set.mem_range_self x)⟩
  have heq (x : M) : g (q x) = e x :=
    congrArg Subtype.val (hg.isEmbedding.toHomeomorph.apply_symm_apply
      ⟨e x, hsub (Set.mem_range_self x)⟩)
  have hqcont : Continuous q := hg.isEmbedding.toHomeomorph.symm.continuous.comp
    (he.contMDiff.continuous.subtype_mk _)
  have hq : ContMDiff I J n q :=
    (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr
      ⟨hqcont, he.contMDiff.congr heq⟩
  have hcomp : _root_.Manifold.IsImmersion I K n (g ∘ q) := by
    simpa only [Function.comp_def, heq] using he
  have hqi := hcomp.of_comp hn hq hg.contMDiff
  have hqo : IsOpen (Set.range q) :=
    _root_.Submission.Manifold.isOpen_range_of_isImmersion hdim hqi
  have hr : g ⁻¹' Set.range e = Set.range q := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, hg.isEmbedding.injective ((heq x).trans hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (heq x).symm⟩
  rwa [hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsImmersion.isOpen_preimage_range_of_range_subset then
    throwError "Refusing to shadow existing declaration Manifold.IsImmersion.isOpen_preimage_range_of_range_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsImmersion.isOpen_preimage_range_of_range_subset ``Submission.Manifold.IsImmersion.isOpen_preimage_range_of_range_subset

end Manifold

namespace Manifold
open _root_.Manifold

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.fst_Icc_of_snd_eq_const
    {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} [Fact (a < b)] {f : Set.Icc a b → F × V} {c : V}
    (h : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, F × V) ∞ f)
    (hsnd : ∀ x, (f x).2 = c) :
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, F) ∞ (fun x => (f x).1) := by
  let p : Set.Icc a b → F := fun x => (f x).1
  let j : F → F × V := fun y => (y, c)
  have hp : ContMDiff (𝓡∂ 1) 𝓘(ℝ, F) ∞ p := contDiff_fst.contMDiff.comp h.contMDiff
  have hj : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × V) ∞ j :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have heq : j ∘ p = f := by
    funext x
    exact Prod.ext rfl (hsnd x).symm
  have hh : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, F × V) ∞ (j ∘ p) := heq ▸ h
  refine ⟨isImmersion_Icc_of_injective_mfderiv hp ?_,
    Topology.IsEmbedding.of_comp hp.continuous hj.continuous hh.isEmbedding⟩
  intro x
  have hinj := (hh.isImmersion.isImmersionAt x).injective_mfderiv (by simp)
  rw [mfderiv_comp x (hj.mdifferentiableAt (by simp)) (hp.mdifferentiableAt (by simp))] at hinj
  exact Function.Injective.of_comp hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.fst_Icc_of_snd_eq_const then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.fst_Icc_of_snd_eq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.fst_Icc_of_snd_eq_const ``Submission.Manifold.IsSmoothEmbedding.fst_Icc_of_snd_eq_const

end Manifold
