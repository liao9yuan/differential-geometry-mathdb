import Submission.DifferentialGeometry.Topology.Homology.RelativeCochainMayerVietoris

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem homology_biprod_decomposition (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (x : (A ⊞ B).homology n) :
    (HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom
        ((HomologicalComplex.homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom x) +
      (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom
        ((HomologicalComplex.homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom x) = x := by
  have h := congrArg (fun f : A ⊞ B ⟶ A ⊞ B =>
    (HomologicalComplex.homologyMap f n).hom x) (biprod.total (X := A) (Y := B))
  simpa only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_biprod_decomposition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_biprod_decomposition target :: scope.openDecls } }

private theorem homology_interSum_inl (n : ℕ) (A B : Set X)
    (a : integralRelativeCohomology n A) :
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      ((HomologicalComplex.homologyMap
        (biprod.inl : integralRelativeCochains A ⟶
          integralRelativeCochains A ⊞ integralRelativeCochains B) n).hom a) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a := by
  have h := congrArg (fun f : integralRelativeCochains A ⟶ integralRelativeCochains (A ∩ B) =>
    (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_desc
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from _root_.Set.inter_subset_left))
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from _root_.Set.inter_subset_right)))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_interSum_inl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_interSum_inl target :: scope.openDecls } }

private theorem homology_interSum_inr (n : ℕ) (A B : Set X)
    (b : integralRelativeCohomology n B) :
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom
      ((HomologicalComplex.homologyMap
        (biprod.inr : integralRelativeCochains B ⟶
          integralRelativeCochains A ⊞ integralRelativeCochains B) n).hom b) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b := by
  have h := congrArg (fun f : integralRelativeCochains B ⟶ integralRelativeCochains (A ∩ B) =>
    (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_desc
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ A from _root_.Set.inter_subset_left))
      (integralRelativeCochainMap (ContinuousMap.id X) (show A ∩ B ⊆ B from _root_.Set.inter_subset_right)))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_interSum_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_interSum_inr target :: scope.openDecls } }

private theorem integralRelativeCochainInterSum_homology_image_iff (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∩ B)) :
    (∃ y : (integralRelativeCochains A ⊞ integralRelativeCochains B).homology n,
      (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y = x) ↔
    ∃ a : integralRelativeCohomology n A, ∃ b : integralRelativeCohomology n B,
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b = x := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(HomologicalComplex.homologyMap
      (biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ _) n).hom y,
      (HomologicalComplex.homologyMap
      (biprod.snd : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶ _) n).hom y, ?_⟩
    erw [← homology_interSum_inl n A B, ← homology_interSum_inr n A B, ← map_add,
      homology_biprod_decomposition]
    rfl
  · rintro ⟨a, b, hab⟩
    refine ⟨(HomologicalComplex.homologyMap
      (biprod.inl : integralRelativeCochains A ⟶ integralRelativeCochains A ⊞
        integralRelativeCochains B) n).hom a +
      (HomologicalComplex.homologyMap
      (biprod.inr : integralRelativeCochains B ⟶ integralRelativeCochains A ⊞
        integralRelativeCochains B) n).hom b, ?_⟩
    rw [map_add, homology_interSum_inl, homology_interSum_inr]
    exact hab

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCochainInterSum_homology_image_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCochainInterSum_homology_image_iff target :: scope.openDecls } }

private theorem homology_unionDifference_fst (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap
      (biprod.fst : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
        integralRelativeCochains A) n).hom
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x) =
    integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show _root_.Set.MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) x := by
  have h := congrArg (fun f : integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains A =>
    (HomologicalComplex.homologyMap f n).hom x)
    (biprod.lift_fst
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
      (-(integralRelativeCochainMap (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx))))
  rw [HomologicalComplex.homologyMap_comp] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_unionDifference_fst
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_unionDifference_fst target :: scope.openDecls } }

private theorem homology_unionDifference_snd (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap
      (biprod.snd : integralRelativeCochains A ⊞ integralRelativeCochains B ⟶
        integralRelativeCochains B) n).hom
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x) =
    -integralRelativeCohomologyMap n (ContinuousMap.id X)
      (show _root_.Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) x := by
  have h := congrArg (fun f : integralRelativeCochains (A ∪ B) ⟶ integralRelativeCochains B =>
    (HomologicalComplex.homologyMap f n).hom x)
    (biprod.lift_snd
      (integralRelativeCochainMap (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx))
      (-(integralRelativeCochainMap (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx))))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_neg] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_unionDifference_snd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_unionDifference_snd target :: scope.openDecls } }

private theorem integralRelativeCochainUnionDifference_homology_eq_zero_iff (n : ℕ) (A B : Set X)
    (x : integralRelativeCohomology n (A ∪ B)) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x = 0 ↔
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) x = 0 ∧
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) x = 0 := by
  constructor
  · intro hx
    have hA := homology_unionDifference_fst n A B x
    have hB := homology_unionDifference_snd n A B x
    rw [hx, map_zero] at hA hB
    exact ⟨hA.symm, neg_eq_zero.mp hB.symm⟩
  · rintro ⟨hA, hB⟩
    have h := homology_biprod_decomposition n (integralRelativeCochains A)
      (integralRelativeCochains B)
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom x)
    erw [homology_unionDifference_fst, homology_unionDifference_snd, hA, hB,
      neg_zero, map_zero, map_zero, add_zero] at h
    exact h.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeCochainUnionDifference_homology_eq_zero_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeCochainUnionDifference_homology_eq_zero_iff target :: scope.openDecls } }


private theorem homology_biprod_fst_add (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (a : A.homology n) (b : B.homology n) :
    (HomologicalComplex.homologyMap (biprod.fst : A ⊞ B ⟶ A) n).hom
      ((HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom a +
        (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom b) = a := by
  have ha := congrArg (fun f : A ⟶ A => (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_fst (X := A) (Y := B))
  have hb := congrArg (fun f : B ⟶ A => (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_fst (X := A) (Y := B))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at ha
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] at hb
  rw [map_add]
  exact (congrArg₂ (fun x y : A.homology n => x + y) ha hb).trans (add_zero a)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_biprod_fst_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_biprod_fst_add target :: scope.openDecls } }

private theorem homology_biprod_snd_add (n : ℕ)
    (A B : CochainComplex (ModuleCat.{u} ℤ) ℕ) (a : A.homology n) (b : B.homology n) :
    (HomologicalComplex.homologyMap (biprod.snd : A ⊞ B ⟶ B) n).hom
      ((HomologicalComplex.homologyMap (biprod.inl : A ⟶ A ⊞ B) n).hom a +
        (HomologicalComplex.homologyMap (biprod.inr : B ⟶ A ⊞ B) n).hom b) = b := by
  have ha := congrArg (fun f : A ⟶ B => (HomologicalComplex.homologyMap f n).hom a)
    (biprod.inl_snd (X := A) (Y := B))
  have hb := congrArg (fun f : B ⟶ B => (HomologicalComplex.homologyMap f n).hom b)
    (biprod.inr_snd (X := A) (Y := B))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] at ha
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at hb
  rw [map_add]
  exact (congrArg₂ (fun x y : B.homology n => x + y) ha hb).trans (zero_add b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.homology_biprod_snd_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.homology_biprod_snd_add target :: scope.openDecls } }

private theorem integralRelativeMayerVietoris_middle_exact_elementwise (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B)
    (a : integralRelativeCohomology n A) (b : integralRelativeCohomology n B) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b = 0 ↔
    ∃ γ : integralRelativeCohomology n (A ∪ B),
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) A (A ∪ B) from fun _ hx => Or.inl hx) γ = a ∧
      -integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) B (A ∪ B) from fun _ hx => Or.inr hx) γ = b := by
  let y := (HomologicalComplex.homologyMap
    (biprod.inl : integralRelativeCochains A ⟶ integralRelativeCochains A ⊞
      integralRelativeCochains B) n).hom a +
    (HomologicalComplex.homologyMap
    (biprod.inr : integralRelativeCochains B ⟶ integralRelativeCochains A ⊞
      integralRelativeCochains B) n).hom b
  have hy : (HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) A from fun _ hx => hx.1) a +
        integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (A ∩ B) B from fun _ hx => hx.2) b := by
    dsimp only [y]
    rw [map_add, homology_interSum_inl, homology_interSum_inr]
    rfl
  have hF := homology_biprod_fst_add n (integralRelativeCochains A)
    (integralRelativeCochains B) a b
  have hS := homology_biprod_snd_add n (integralRelativeCochains A)
    (integralRelativeCochains B) a b
  erw [← hy, (integralRelativeCohomology_mayerVietoris_exact_biprod n A B hA hB) y]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, ?_⟩
    · have h := homology_unionDifference_fst n A B γ
      rw [hγ] at h
      exact h.symm.trans hF
    · have h := homology_unionDifference_snd n A B γ
      rw [hγ] at h
      exact h.symm.trans hS
  · rintro ⟨γ, hγA, hγB⟩
    refine ⟨γ, ?_⟩
    have h := homology_biprod_decomposition n (integralRelativeCochains A)
      (integralRelativeCochains B)
      ((HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom γ)
    erw [homology_unionDifference_fst, homology_unionDifference_snd, hγA, hγB] at h
    exact h.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralRelativeMayerVietoris_middle_exact_elementwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralRelativeMayerVietoris_middle_exact_elementwise target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

private theorem exact_transport_middle_right
    {M N N' P P' : ModuleCat.{u} ℤ} (eN : N' = N) (eP : P = P')
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (h : Function.Exact f g) :
    Function.Exact ((_root_.CategoryTheory.eqToHom eN.symm).hom.comp f)
      ((_root_.CategoryTheory.eqToHom eP).hom.comp (g.comp (_root_.CategoryTheory.eqToHom eN).hom)) := by
  subst N'
  subst P'
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exact_transport_middle_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exact_transport_middle_right target :: scope.openDecls } }

private theorem exact_transport_left_middle
    {M M' N N' P : ModuleCat.{u} ℤ} (eM : M' = M) (eN : N = N')
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (h : Function.Exact f g) :
    Function.Exact ((_root_.CategoryTheory.eqToHom eN).hom.comp (f.comp (_root_.CategoryTheory.eqToHom eM).hom))
      (g.comp (_root_.CategoryTheory.eqToHom eN.symm).hom) := by
  subst M'
  subst N'
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.exact_transport_left_middle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.exact_transport_left_middle target :: scope.openDecls } }

variable {X : Type u} [TopologicalSpace X]

private def supportSum (n : ℕ) (K L : Set X) :
    (integralRelativeCochains Kᶜ ⊞ integralRelativeCochains Lᶜ).homology n →ₗ[ℤ]
      integralRelativeCohomology n (K ∪ L)ᶜ :=
  (_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) (_root_.Set.compl_union K L).symm)).hom.comp
    (HomologicalComplex.homologyMap (integralRelativeCochainInterSum Kᶜ Lᶜ) n).hom

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.supportSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.supportSum target :: scope.openDecls } }

private def supportDifference (n : ℕ) (K L : Set X) :
    integralRelativeCohomology n (K ∩ L)ᶜ →ₗ[ℤ]
      (integralRelativeCochains Kᶜ ⊞ integralRelativeCochains Lᶜ).homology n :=
  (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference Kᶜ Lᶜ) n).hom.comp
    (_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) (_root_.Set.compl_inter K L))).hom

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.supportDifference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.supportDifference target :: scope.openDecls } }

private theorem support_exact_union (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    Function.Exact (supportSum n K L)
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL) :=
  exact_transport_middle_right
    (congrArg (integralRelativeCohomology n) (_root_.Set.compl_union K L))
    (congrArg (integralRelativeCohomology (n + 1)) (_root_.Set.compl_inter K L).symm)
    _ _ (integralRelativeCohomology_mayerVietoris_exact_inter n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.support_exact_union
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.support_exact_union target :: scope.openDecls } }

private theorem support_exact_inter (n : ℕ) (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) :
    Function.Exact (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL)
      (supportDifference (n + 1) K L) :=
  exact_transport_left_middle
    (congrArg (integralRelativeCohomology n) (_root_.Set.compl_union K L))
    (congrArg (integralRelativeCohomology (n + 1)) (_root_.Set.compl_inter K L).symm)
    _ _ (integralRelativeCohomology_mayerVietoris_exact_union n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.support_exact_inter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.support_exact_inter target :: scope.openDecls } }

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem relative_sum_image_cast (n : ℕ) (A B C : Set X)
    (e : C = A ∩ B) (hA : _root_.Set.MapsTo (ContinuousMap.id X) C A)
    (hB : _root_.Set.MapsTo (ContinuousMap.id X) C B) (x : integralRelativeCohomology n C) :
    (∃ y : (integralRelativeCochains A ⊞ integralRelativeCochains B).homology n,
      (_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) e.symm)).hom
        ((HomologicalComplex.homologyMap (integralRelativeCochainInterSum A B) n).hom y) = x) ↔
    ∃ a : integralRelativeCohomology n A, ∃ b : integralRelativeCohomology n B,
      integralRelativeCohomologyMap n (ContinuousMap.id X) hA a +
        integralRelativeCohomologyMap n (ContinuousMap.id X) hB b = x := by
  subst C
  exact integralRelativeCochainInterSum_homology_image_iff n A B x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_sum_image_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_sum_image_cast target :: scope.openDecls } }

theorem integralCohomologyWithSupport_mayerVietoris_exact_union
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (x : integralRelativeCohomology n (K ∪ L)ᶜ) :
    integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL x = 0 ↔
      ∃ a : integralRelativeCohomology n Kᶜ, ∃ b : integralRelativeCohomology n Lᶜ,
        integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show _root_.Set.MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Kᶜ from
              compl_subset_compl.mpr _root_.Set.subset_union_left) a +
          integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show _root_.Set.MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Lᶜ from
              compl_subset_compl.mpr _root_.Set.subset_union_right) b = x := by
  rw [support_exact_union n K L hK hL x]
  exact relative_sum_image_cast n Kᶜ Lᶜ (K ∪ L)ᶜ (_root_.Set.compl_union K L) _ _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_union ``Submission.DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_union

end DifferentialGeometry.Topology

end

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem relative_difference_kernel_cast (n : ℕ) (A B C : Set X)
    (e : C = A ∪ B) (hA : _root_.Set.MapsTo (ContinuousMap.id X) A C)
    (hB : _root_.Set.MapsTo (ContinuousMap.id X) B C) (x : integralRelativeCohomology n C) :
    (HomologicalComplex.homologyMap (integralRelativeCochainUnionDifference A B) n).hom
      ((_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) e)).hom x) = 0 ↔
      integralRelativeCohomologyMap n (ContinuousMap.id X) hA x = 0 ∧
        integralRelativeCohomologyMap n (ContinuousMap.id X) hB x = 0 := by
  subst C
  exact integralRelativeCochainUnionDifference_homology_eq_zero_iff n A B x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_difference_kernel_cast
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_difference_kernel_cast target :: scope.openDecls } }

theorem integralCohomologyWithSupport_mayerVietoris_exact_inter
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (x : integralRelativeCohomology (n + 1) (K ∩ L)ᶜ) :
    (integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ from
          compl_subset_compl.mpr _root_.Set.inter_subset_left) x = 0 ∧
      integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) Lᶜ (K ∩ L)ᶜ from
          compl_subset_compl.mpr _root_.Set.inter_subset_right) x = 0) ↔
      ∃ y : integralRelativeCohomology n (K ∪ L)ᶜ,
        integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL y = x := by
  rw [← relative_difference_kernel_cast (n + 1) Kᶜ Lᶜ (K ∩ L)ᶜ (_root_.Set.compl_inter K L)]
  exact support_exact_inter n K L hK hL x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_inter ``Submission.DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_exact_inter

end DifferentialGeometry.Topology

end

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set
universe u
namespace DifferentialGeometry.Topology
variable {X : Type u} [TopologicalSpace X]

theorem integralCohomologyWithSupport_mayerVietoris_middle_exact
    (n : ℕ) (K L : Set X) (hK : IsClosed K) (hL : IsClosed L)
    (a : integralRelativeCohomology n Kᶜ) (b : integralRelativeCohomology n Lᶜ) :
    integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Kᶜ from
          compl_subset_compl.mpr _root_.Set.subset_union_left) a +
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (K ∪ L)ᶜ Lᶜ from
          compl_subset_compl.mpr _root_.Set.subset_union_right) b = 0 ↔
    ∃ γ : integralRelativeCohomology n (K ∩ L)ᶜ,
      integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) Kᶜ (K ∩ L)ᶜ from
            compl_subset_compl.mpr _root_.Set.inter_subset_left) γ = a ∧
      -integralRelativeCohomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) Lᶜ (K ∩ L)ᶜ from
            compl_subset_compl.mpr _root_.Set.inter_subset_right) γ = b := by
  have aux (C D : Set X) (eC : C = Kᶜ ∩ Lᶜ) (eD : D = Kᶜ ∪ Lᶜ)
      (hCK : _root_.Set.MapsTo (ContinuousMap.id X) C Kᶜ)
      (hCL : _root_.Set.MapsTo (ContinuousMap.id X) C Lᶜ)
      (hKD : _root_.Set.MapsTo (ContinuousMap.id X) Kᶜ D)
      (hLD : _root_.Set.MapsTo (ContinuousMap.id X) Lᶜ D) :
      integralRelativeCohomologyMap n (ContinuousMap.id X) hCK a +
        integralRelativeCohomologyMap n (ContinuousMap.id X) hCL b = 0 ↔
      ∃ γ : integralRelativeCohomology n D,
        integralRelativeCohomologyMap n (ContinuousMap.id X) hKD γ = a ∧
          -integralRelativeCohomologyMap n (ContinuousMap.id X) hLD γ = b := by
    subst C
    subst D
    exact integralRelativeMayerVietoris_middle_exact_elementwise n Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl a b
  exact aux (K ∪ L)ᶜ (K ∩ L)ᶜ (_root_.Set.compl_union K L) (_root_.Set.compl_inter K L) _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_middle_exact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_middle_exact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_middle_exact ``Submission.DifferentialGeometry.Topology.integralCohomologyWithSupport_mayerVietoris_middle_exact

end DifferentialGeometry.Topology
end

noncomputable section

open _root_.CategoryTheory _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem relative_cohomology_map_eqToHom
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (f : ContinuousMap X Y)
    {A A' : Set X} {B B' : Set Y} (eA : A = A') (eB : B = B')
    (hf : _root_.Set.MapsTo f A B) (hf' : _root_.Set.MapsTo f A' B') :
    (_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) eA)).hom.comp
        (integralRelativeCohomologyMap n f hf) =
      (integralRelativeCohomologyMap n f hf').comp
        (_root_.CategoryTheory.eqToHom (congrArg (integralRelativeCohomology n) eB)).hom := by
  subst A'
  subst B'
  ext α
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relative_cohomology_map_eqToHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relative_cohomology_map_eqToHom target :: scope.openDecls } }

theorem integralCohomologyWithSupportMayerVietorisConnecting_map (n : ℕ)
    (f : ContinuousMap X Y) (K L : Set X) (P Q : Set Y)
    (hK : IsClosed K) (hL : IsClosed L) (hP : IsClosed P) (hQ : IsClosed Q)
    (hfK : _root_.Set.MapsTo f Kᶜ Pᶜ) (hfL : _root_.Set.MapsTo f Lᶜ Qᶜ) :
    (integralRelativeCohomologyMap (n + 1) f
      (show _root_.Set.MapsTo f (K ∩ L)ᶜ (P ∩ Q)ᶜ from by
        simpa only [_root_.Set.compl_inter] using hfK.union_union hfL)).comp
      (integralCohomologyWithSupportMayerVietorisConnecting n P Q hP hQ) =
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL).comp
        (integralRelativeCohomologyMap n f
          (show _root_.Set.MapsTo f (K ∪ L)ᶜ (P ∪ Q)ᶜ from by
            simpa only [_root_.Set.compl_union] using hfK.inter_inter hfL)) := by
  have h := integralRelativeMayerVietorisConnecting_natural n f
    hK.isOpen_compl hL.isOpen_compl hP.isOpen_compl hQ.isOpen_compl hfK hfL
  have hOut := relative_cohomology_map_eqToHom (n + 1) f
    (_root_.Set.compl_inter K L).symm (_root_.Set.compl_inter P Q).symm
    (hfK.union_union hfL)
    (show _root_.Set.MapsTo f (K ∩ L)ᶜ (P ∩ Q)ᶜ from by
      simpa only [_root_.Set.compl_inter] using hfK.union_union hfL)
  have hIn := relative_cohomology_map_eqToHom n f
    (_root_.Set.compl_union K L) (_root_.Set.compl_union P Q)
    (show _root_.Set.MapsTo f (K ∪ L)ᶜ (P ∪ Q)ᶜ from by
      simpa only [_root_.Set.compl_union] using hfK.inter_inter hfL)
    (hfK.inter_inter hfL)
  unfold integralCohomologyWithSupportMayerVietorisConnecting
  ext α
  simp only [LinearMap.comp_apply]
  exact (LinearMap.congr_fun hOut _).symm.trans
    ((congrArg _ (LinearMap.congr_fun h _)).trans
      (congrArg _ (congrArg
        (integralRelativeMayerVietorisConnecting n Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl)
        (LinearMap.congr_fun hIn α).symm)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_map ``Submission.DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_map

end DifferentialGeometry.Topology

end

noncomputable section
open _root_.CategoryTheory _root_.Set
universe u
namespace DifferentialGeometry.Topology
variable {X : Type u} [TopologicalSpace X]

theorem integralCohomologyWithSupportMayerVietorisConnecting_natural
    (n : ℕ) (K L K' L' : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (hK' : IsClosed K') (hL' : IsClosed L')
    (hKK' : K ⊆ K') (hLL' : L ⊆ L') :
    (integralRelativeCohomologyMap (n + 1) (ContinuousMap.id X)
      (show _root_.Set.MapsTo (ContinuousMap.id X) (K' ∩ L')ᶜ (K ∩ L)ᶜ from
        fun _ hx => compl_subset_compl.mpr (_root_.Set.inter_subset_inter hKK' hLL') hx)).comp
      (integralCohomologyWithSupportMayerVietorisConnecting n K L hK hL) =
      (integralCohomologyWithSupportMayerVietorisConnecting n K' L' hK' hL').comp
      (integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (K' ∪ L')ᶜ (K ∪ L)ᶜ from
          fun _ hx => compl_subset_compl.mpr (_root_.Set.union_subset_union hKK' hLL') hx)) := by
  exact integralCohomologyWithSupportMayerVietorisConnecting_map n (ContinuousMap.id X)
    K' L' K L hK' hL' hK hL
    (show _root_.Set.MapsTo (ContinuousMap.id X) K'ᶜ Kᶜ from fun _ hx => compl_subset_compl.mpr hKK' hx)
    (show _root_.Set.MapsTo (ContinuousMap.id X) L'ᶜ Lᶜ from fun _ hx => compl_subset_compl.mpr hLL' hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_natural ``Submission.DifferentialGeometry.Topology.integralCohomologyWithSupportMayerVietorisConnecting_natural

end DifferentialGeometry.Topology
end
