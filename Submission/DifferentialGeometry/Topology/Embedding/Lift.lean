import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace Manifold
open _root_.Manifold

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} {f : M → N} {g : P → N}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
noncomputable def IsSmoothEmbedding.lift (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (g : P → N) (hgf : Set.range g ⊆ Set.range f) : P → M :=
  fun x => hf.isEmbedding.toHomeomorph.symm ⟨g x, hgf (Set.mem_range_self x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.lift then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.lift"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.lift ``Submission.Manifold.IsSmoothEmbedding.lift

omit [TopologicalSpace P] in
open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.comp_lift (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hgf : Set.range g ⊆ Set.range f) (x : P) :
    f (hf.lift g hgf x) = g x := by
  exact congrArg Subtype.val
    (hf.isEmbedding.toHomeomorph.apply_symm_apply ⟨g x, hgf (Set.mem_range_self x)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.comp_lift then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.comp_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.comp_lift ``Submission.Manifold.IsSmoothEmbedding.comp_lift

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.contMDiff_lift (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hg : ContMDiff K J n g) (hgf : Set.range g ⊆ Set.range f) :
    ContMDiff K I n (hf.lift g hgf) := by
  apply (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr
  refine ⟨?_, hg.congr (hf.comp_lift hgf)⟩
  exact hf.isEmbedding.toHomeomorph.symm.continuous.comp
    (hg.continuous.subtype_mk (fun x => hgf (Set.mem_range_self x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.contMDiff_lift then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.contMDiff_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.contMDiff_lift ``Submission.Manifold.IsSmoothEmbedding.contMDiff_lift

end

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''} [I.Boundaryless] [K.Boundaryless]
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold K n P] {f : M → N} {g : P → N}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.isSmoothEmbedding_lift (hf : _root_.Manifold.IsSmoothEmbedding I J n f)
    (hg : _root_.Manifold.IsSmoothEmbedding K J n g) (hn : n ≠ 0) (hgf : Set.range g ⊆ Set.range f) :
    IsSmoothEmbedding K I n (hf.lift g hgf) := by
  have hcomp : _root_.Manifold.IsSmoothEmbedding K J n (f ∘ hf.lift g hgf) := by
    rw [show f ∘ hf.lift g hgf = g from funext (hf.comp_lift hgf)]
    exact hg
  exact hcomp.of_comp hn (hf.contMDiff_lift hg.contMDiff hgf) hf.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.isSmoothEmbedding_lift then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.isSmoothEmbedding_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.isSmoothEmbedding_lift ``Submission.Manifold.IsSmoothEmbedding.isSmoothEmbedding_lift

end Manifold
