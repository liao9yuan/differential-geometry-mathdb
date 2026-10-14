import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

open _root_.PartialDiffeomorph in
noncomputable def disjointUnion (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    PartialDiffeomorph I J M N n := by
  classical
  refine { e.toOpenPartialHomeomorph.disjointUnion f.toOpenPartialHomeomorph hs ht with
    contMDiffOn_toFun := ?_, contMDiffOn_invFun := ?_ }
  · apply ContMDiffOn.union_of_isOpen ?_ ?_ e.open_source f.open_source
    · exact e.contMDiffOn.congr (fun x hx => if_pos hx)
    · exact f.contMDiffOn.congr (fun x hx =>
        if_neg (fun he => disjoint_left.mp hs he hx))
  · apply ContMDiffOn.union_of_isOpen ?_ ?_ e.open_target f.open_target
    · exact e.symm.contMDiffOn.congr (fun x hx => if_pos hx)
    · exact f.symm.contMDiffOn.congr (fun x hx =>
        if_neg (fun he => disjoint_left.mp ht he hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion ``Submission.PartialDiffeomorph.disjointUnion

open _root_.PartialDiffeomorph in
@[simp] theorem disjointUnion_source (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    (e.disjointUnion f hs ht).source = e.source ∪ f.source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_source ``Submission.PartialDiffeomorph.disjointUnion_source

open _root_.PartialDiffeomorph in
@[simp] theorem disjointUnion_target (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target) :
    (e.disjointUnion f hs ht).target = e.target ∪ f.target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_target ``Submission.PartialDiffeomorph.disjointUnion_target

open _root_.PartialDiffeomorph in
theorem disjointUnion_apply_of_mem_left (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : M} (hx : x ∈ e.source) : e.disjointUnion f hs ht x = e x := by
  classical
  exact if_pos hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_apply_of_mem_left then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_apply_of_mem_left"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_apply_of_mem_left ``Submission.PartialDiffeomorph.disjointUnion_apply_of_mem_left

open _root_.PartialDiffeomorph in
theorem disjointUnion_apply_of_mem_right (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : M} (hx : x ∈ f.source) : e.disjointUnion f hs ht x = f x := by
  classical
  exact if_neg (fun he => disjoint_left.mp hs he hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_apply_of_mem_right then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_apply_of_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_apply_of_mem_right ``Submission.PartialDiffeomorph.disjointUnion_apply_of_mem_right

open _root_.PartialDiffeomorph in
theorem disjointUnion_symm_apply_of_mem_left (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : N} (hx : x ∈ e.target) : (e.disjointUnion f hs ht).symm x = e.symm x := by
  classical
  exact if_pos hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_symm_apply_of_mem_left then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_symm_apply_of_mem_left"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_symm_apply_of_mem_left ``Submission.PartialDiffeomorph.disjointUnion_symm_apply_of_mem_left

open _root_.PartialDiffeomorph in
theorem disjointUnion_symm_apply_of_mem_right (e f : PartialDiffeomorph I J M N n)
    (hs : Disjoint e.source f.source) (ht : Disjoint e.target f.target)
    {x : N} (hx : x ∈ f.target) : (e.disjointUnion f hs ht).symm x = f.symm x := by
  classical
  exact if_neg (fun he => disjoint_left.mp ht he hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.disjointUnion_symm_apply_of_mem_right then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.disjointUnion_symm_apply_of_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.disjointUnion_symm_apply_of_mem_right ``Submission.PartialDiffeomorph.disjointUnion_symm_apply_of_mem_right

end PartialDiffeomorph
