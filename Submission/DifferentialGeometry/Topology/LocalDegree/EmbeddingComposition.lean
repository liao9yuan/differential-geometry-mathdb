/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.OpenDomain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Set

namespace DifferentialGeometry.LocalDegree

open _root_.Submission.DifferentialGeometry.Homology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Z" => ModuleCat.of ℤ ℤ

theorem euclideanLocalDegree_sub_comp_of_injOn
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : ContinuousOn f U) (hfi : _root_.Set.InjOn f U)
    (hg : ContinuousOn g V) (hgi : _root_.Set.InjOn g V) (hm : _root_.Set.MapsTo f U V)
    {x : E} (hx : x ∈ U) :
    euclideanLocalDegree (fun z => g (f z) - g (f x)) x
        (isolatedZero_sub_of_injOn hU (hg.comp hf hm) (hgi.comp hfi hm) hx) =
      euclideanLocalDegree (fun z => f z - f x) x
          (isolatedZero_sub_of_injOn hU hf hfi hx) *
        euclideanLocalDegree (fun z => g z - g (f x)) (f x)
          (isolatedZero_sub_of_injOn hV hg hgi (hm hx)) := by
  let F : TopCat.of U ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun z => ⟨f z, hm z.2⟩, hf.domRestrict.subtype_mk _⟩
  let G : TopCat.of V ⟶ TopCat.of (_root_.Set.univ : Set E) :=
    TopCat.ofHom ⟨fun z => ⟨g z, _root_.Set.mem_univ _⟩, hg.domRestrict.subtype_mk _⟩
  have hFp : _root_.Set.MapsTo F ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    exact hfi z.2 hx (congrArg (fun a : V => (a : E)) heq)
  have hGp : _root_.Set.MapsTo G ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V)
      ({(⟨g (f x), _root_.Set.mem_univ _⟩ : (_root_.Set.univ : Set E))}ᶜ : Set (_root_.Set.univ : Set E)) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    exact hgi z.2 (hm hx) (congrArg (fun a : (_root_.Set.univ : Set E) => (a : E)) heq)
  have hFdeg := euclideanLocalDegree_open_relativeHomology hU hV hf hfi hm hx
    F (fun _ => rfl) hFp
  have hGdeg := euclideanLocalDegree_open_relativeHomology hV isOpen_univ hg hgi
    (_root_.Set.mapsTo_univ g V) (hm hx) G (fun _ => rfl) hGp
  have hGFdeg := euclideanLocalDegree_open_relativeHomology hU isOpen_univ
    (hg.comp hf hm) (hgi.comp hfi hm) (_root_.Set.mapsTo_univ (g ∘ f) U) hx
    (F ≫ G) (fun _ => rfl) (hGp.comp hFp)
  have hcomp := relativeHomologyMap_comp Z F hFp G hGp (d + 1)
  have h := congrArg (fun q => q (euclideanOpenLocalGenerator hU x hx)) hcomp
  change relativeHomologyMap Z (F ≫ G) (hGp.comp hFp) (d + 1)
    (euclideanOpenLocalGenerator hU x hx) =
      relativeHomologyMap Z G hGp (d + 1)
        (relativeHomologyMap Z F hFp (d + 1) (euclideanOpenLocalGenerator hU x hx)) at h
  rw [hGFdeg, hFdeg, map_zsmul, hGdeg, smul_smul] at h
  exact euclideanOpenLocalGenerator_smul_injective isOpen_univ
    (g (f x)) (_root_.Set.mem_univ _) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_comp_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_comp_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_comp_of_injOn ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_sub_comp_of_injOn

end DifferentialGeometry.LocalDegree
