import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Homeomorph.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace ContinuousMap
open _root_.ContinuousMap

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.ContinuousMap in
noncomputable def liftClosedCover (S : ι → Set X) (φ : ∀ i, C(S i, Y))
    (hφ : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
    (hcov : ⋃ i, S i = _root_.Set.univ) (hclosed : ∀ i, IsClosed (S i)) (hfinite : LocallyFinite S) :
    C(X, Y) :=
  _root_.ContinuousMap.mk (Set.liftCover S (fun i ↦ φ i) hφ hcov) <| hfinite.continuous hcov hclosed fun i ↦ by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe] using (φ i).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.liftClosedCover then
    throwError "Refusing to shadow existing declaration ContinuousMap.liftClosedCover"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.liftClosedCover ``Submission.ContinuousMap.liftClosedCover

variable {S : ι → Set X} {φ : ∀ i, C(S i, Y)}
    {hφ : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩}
    {hcov : ⋃ i, S i = univ} {hclosed : ∀ i, IsClosed (S i)} {hfinite : LocallyFinite S}

open _root_.ContinuousMap in
@[simp]
theorem liftClosedCover_coe {i : ι} (x : S i) :
    liftClosedCover S φ hφ hcov hclosed hfinite x = φ i x :=
  by
    change Set.liftCover S (fun i ↦ φ i) hφ hcov x = φ i x
    exact Set.liftCover_coe x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.liftClosedCover_coe then
    throwError "Refusing to shadow existing declaration ContinuousMap.liftClosedCover_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.liftClosedCover_coe ``Submission.ContinuousMap.liftClosedCover_coe

open _root_.ContinuousMap in
@[simp]
theorem liftClosedCover_restrict {i : ι} :
    (liftClosedCover S φ hφ hcov hclosed hfinite).restrict (S i) = φ i := by
  ext x
  simp only [_root_.ContinuousMap.restrict_apply, liftClosedCover_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.liftClosedCover_restrict then
    throwError "Refusing to shadow existing declaration ContinuousMap.liftClosedCover_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.liftClosedCover_restrict ``Submission.ContinuousMap.liftClosedCover_restrict

end ContinuousMap

namespace Homeomorph
open _root_.Homeomorph

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.Homeomorph in
noncomputable def liftClosedCover (S : ι → Set X) (T : ι → Set Y)
    (e : ∀ i, S i ≃ₜ T i)
    (he : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      (e i ⟨x, hxi⟩ : Y) = e j ⟨x, hxj⟩)
    (he' : ∀ (i j) (y : Y) (hyi : y ∈ T i) (hyj : y ∈ T j),
      ((e i).symm ⟨y, hyi⟩ : X) = (e j).symm ⟨y, hyj⟩)
    (hS : ⋃ i, S i = _root_.Set.univ) (hSc : ∀ i, IsClosed (S i)) (hSf : LocallyFinite S)
    (hT : ⋃ i, T i = _root_.Set.univ) (hTc : ∀ i, IsClosed (T i)) (hTf : LocallyFinite T) :
    X ≃ₜ Y := by
  let f : C(X, Y) := ContinuousMap.liftClosedCover S
    (fun i => ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
    he hS hSc hSf
  let g : C(Y, X) := ContinuousMap.liftClosedCover T
    (fun i => ⟨fun y => ((e i).symm y : X),
      continuous_subtype_val.comp (e i).symm.continuous⟩)
    he' hT hTc hTf
  have hf (i : ι) (x : S i) : f x = (e i x : Y) := by
    exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
      ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
      (hφ := he) (hcov := hS) (hclosed := hSc) (hfinite := hSf) x
  have hg (i : ι) (y : T i) : g y = ((e i).symm y : X) := by
    exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
      ⟨fun y => ((e i).symm y : X), continuous_subtype_val.comp (e i).symm.continuous⟩)
      (hφ := he') (hcov := hT) (hclosed := hTc) (hfinite := hTf) y
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  · intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hS.symm ▸ _root_.Set.mem_univ x)
    rw [hf i ⟨x, hxi⟩, hg i (e i ⟨x, hxi⟩), _root_.Homeomorph.symm_apply_apply]
  · intro y
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hT.symm ▸ _root_.Set.mem_univ y)
    rw [hg i ⟨y, hyi⟩, hf i ((e i).symm ⟨y, hyi⟩), _root_.Homeomorph.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.liftClosedCover then
    throwError "Refusing to shadow existing declaration Homeomorph.liftClosedCover"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.liftClosedCover ``Submission.Homeomorph.liftClosedCover

variable {S : ι → Set X} {T : ι → Set Y} {e : ∀ i, S i ≃ₜ T i}
    {he : ∀ (i j) (x : X) (hxi : x ∈ S i) (hxj : x ∈ S j),
      (e i ⟨x, hxi⟩ : Y) = e j ⟨x, hxj⟩}
    {he' : ∀ (i j) (y : Y) (hyi : y ∈ T i) (hyj : y ∈ T j),
      ((e i).symm ⟨y, hyi⟩ : X) = (e j).symm ⟨y, hyj⟩}
    {hS : ⋃ i, S i = univ} {hSc : ∀ i, IsClosed (S i)} {hSf : LocallyFinite S}
    {hT : ⋃ i, T i = univ} {hTc : ∀ i, IsClosed (T i)} {hTf : LocallyFinite T}

open _root_.Homeomorph in
@[simp]
theorem liftClosedCover_coe {i : ι} (x : S i) :
    liftClosedCover S T e he he' hS hSc hSf hT hTc hTf x = e i x := by
  exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
    ⟨fun x => (e i x : Y), continuous_subtype_val.comp (e i).continuous⟩)
      (hφ := he) (hcov := hS) (hclosed := hSc) (hfinite := hSf) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.liftClosedCover_coe then
    throwError "Refusing to shadow existing declaration Homeomorph.liftClosedCover_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.liftClosedCover_coe ``Submission.Homeomorph.liftClosedCover_coe

open _root_.Homeomorph in
@[simp]
theorem liftClosedCover_symm_coe {i : ι} (y : T i) :
    (liftClosedCover S T e he he' hS hSc hSf hT hTc hTf).symm y = (e i).symm y := by
  exact ContinuousMap.liftClosedCover_coe (φ := fun i =>
    ⟨fun y => ((e i).symm y : X), continuous_subtype_val.comp (e i).symm.continuous⟩)
      (hφ := he') (hcov := hT) (hclosed := hTc) (hfinite := hTf) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.liftClosedCover_symm_coe then
    throwError "Refusing to shadow existing declaration Homeomorph.liftClosedCover_symm_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.liftClosedCover_symm_coe ``Submission.Homeomorph.liftClosedCover_symm_coe

end Homeomorph
