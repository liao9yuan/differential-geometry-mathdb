import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Set
open scoped _root_.Manifold

universe u uE uH uM uF uV uI

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type uV} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable {n : WithTop ℕ∞}

structure IsSubbundleFrameOn
    (S : ∀ x, Submodule 𝕜 (V x))
    {ι : Type uI} (s : ι → (x : M) → V x) (U : Set M) : Prop where
  linearIndependent {x : M} (hx : x ∈ U) : LinearIndependent 𝕜 (s · x)
  spans {x : M} (hx : x ∈ U) : Submodule.span 𝕜 (Set.range (s · x)) = S x
  contMDiffOn (i : ι) : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
    (fun x => TotalSpace.mk' F x (s i x)) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn ``Submission.IsSubbundleFrameOn

structure ContMDiffVectorSubbundle
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] where
  fiber : ∀ x, Submodule 𝕜 (V x)
  rank : ℕ
  exists_isSubbundleFrameOn (x : M) :
    ∃ (U : Set M) (s : Fin rank → (y : M) → V y),
      IsOpen U ∧ x ∈ U ∧ IsSubbundleFrameOn (I := I) (F := F) (n := n) fiber s U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle ``Submission.ContMDiffVectorSubbundle
