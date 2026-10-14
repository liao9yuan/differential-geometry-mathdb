import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Module _root_.Set
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

namespace IsSubbundleFrameOn

variable {S : ∀ x, Submodule 𝕜 (V x)}
variable {ι : Type uI} {s : ι → (x : M) → V x} {U U' : Set M}

theorem mem_fiber (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U)
    {x : M} (hx : x ∈ U) (i : ι) : s i x ∈ S x := by
  rw [← hs.spans hx]
  exact Submodule.subset_span (Set.mem_range_self i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.mem_fiber then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.mem_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.mem_fiber ``Submission.IsSubbundleFrameOn.mem_fiber

theorem mono (hs : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U)
    (hU : U' ⊆ U) : IsSubbundleFrameOn (I := I) (F := F) (n := n) S s U' where
  linearIndependent hx := hs.linearIndependent (hU hx)
  spans hx := hs.spans (hU hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsSubbundleFrameOn.mono then
    throwError "Refusing to shadow existing declaration IsSubbundleFrameOn.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `IsSubbundleFrameOn.mono ``Submission.IsSubbundleFrameOn.mono

end IsSubbundleFrameOn

namespace ContMDiffVectorSubbundle

variable [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]

theorem exists_frame (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (x : M) :
    ∃ (U : Set M) (s : Fin S.rank → (y : M) → V y),
      IsOpen U ∧ x ∈ U ∧ IsSubbundleFrameOn (I := I) (F := F) (n := n) S.fiber s U :=
  S.exists_isSubbundleFrameOn x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.exists_frame then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.exists_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.exists_frame ``Submission.ContMDiffVectorSubbundle.exists_frame

theorem finrank_fiber (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (x : M) : Module.finrank 𝕜 (S.fiber x) = S.rank := by
  obtain ⟨U, s, hU, hx, hs⟩ := S.exists_frame x
  let t : Fin S.rank → S.fiber x := fun i => ⟨s i x, hs.mem_fiber hx i⟩
  have htli : LinearIndependent 𝕜 t := by
    apply LinearIndependent.of_comp (S.fiber x).subtype
    have hcomp : (S.fiber x).subtype ∘ t = fun i => s i x := by
      funext i
      rfl
    rw [hcomp]
    exact hs.linearIndependent hx
  have htspan : Submodule.span 𝕜 (Set.range t) = ⊤ := by
    apply (Submodule.map_injective_of_injective (S.fiber x).injective_subtype)
    have hrange : (S.fiber x).subtype '' Set.range t = Set.range (fun i => s i x) := by
      ext v
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨t i, ⟨i, rfl⟩, rfl⟩
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, hrange, hs.spans hx]
  let b : _root_.Module.Basis (Fin S.rank) 𝕜 (S.fiber x) := Basis.mk htli (by rw [htspan])
  simpa using Module.finrank_eq_card_basis b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.finrank_fiber then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.finrank_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.finrank_fiber ``Submission.ContMDiffVectorSubbundle.finrank_fiber

end ContMDiffVectorSubbundle
