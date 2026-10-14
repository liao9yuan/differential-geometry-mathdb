import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RfsTopologyFrontier
import Submission.DifferentialGeometry.Topology.VanKampen.HomotopyRetract
import Submission.DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.VanKampen

universe u v

private theorem pathConnectedSpace_of_homeomorph_aux {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hA : PathConnectedSpace A) : PathConnectedSpace B := by
  have h : IsPathConnected (_root_.Set.univ : Set A) := pathConnectedSpace_iff_univ.mp hA
  have h2 : IsPathConnected (_root_.Set.univ : Set B) := by
    have h3 := h.image e.continuous
    rwa [Set.image_univ, e.surjective.range_eq] at h3
  exact pathConnectedSpace_iff_univ.mpr h2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_of_homeomorph_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_of_homeomorph_aux target :: scope.openDecls } }

private noncomputable def subtypePreimageHomeomorph_aux {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) : {x : ↥B // x.1 ∈ A} ≃ₜ ↥A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.subtypePreimageHomeomorph_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.subtypePreimageHomeomorph_aux target :: scope.openDecls } }

private theorem pathConnectedSpace_of_subtypePreimage_aux {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hA : PathConnectedSpace ↥A) :
    PathConnectedSpace {x : ↥B // x.1 ∈ A} :=
  pathConnectedSpace_of_homeomorph_aux (subtypePreimageHomeomorph_aux hAB).symm hA

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_of_subtypePreimage_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_of_subtypePreimage_aux target :: scope.openDecls } }

private theorem simplyConnectedSpace_of_subtypePreimage_aux {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hA : SimplyConnectedSpace ↥A) :
    SimplyConnectedSpace {x : ↥B // x.1 ∈ A} :=
  ((subtypePreimageHomeomorph_aux hAB).symm.toHomotopyEquiv.simplyConnectedSpace_iff).mp hA

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_subtypePreimage_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_subtypePreimage_aux target :: scope.openDecls } }

private theorem simplyConnectedSpace_of_set_eq_aux {X : Type u} [TopologicalSpace X]
    {A B : Set X} (h : A = B) (hB : SimplyConnectedSpace ↥B) : SimplyConnectedSpace ↥A :=
  ((Homeomorph.setCongr h).toHomotopyEquiv.simplyConnectedSpace_iff).mpr hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_set_eq_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_set_eq_aux target :: scope.openDecls } }

private theorem finCastSucc_ne_last_aux {n : ℕ} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.finCastSucc_ne_last_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.finCastSucc_ne_last_aux target :: scope.openDecls } }

private theorem pathConnectedSpace_union_iUnion_of_meets {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : Set X) (W : ι → Set X) (hU : PathConnectedSpace ↥U)
    (hW : ∀ i, PathConnectedSpace ↥(W i)) (hmeet : ∀ i, (U ∩ W i).Nonempty) :
    PathConnectedSpace ↥(U ∪ ⋃ i, W i) := by
  have hUsub : U ⊆ U ∪ ⋃ i, W i := fun x hx => Or.inl hx
  have hWsub : ∀ i, W i ⊆ U ∪ ⋃ i, W i := fun i x hx =>
    Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)
  choose b hbU hbW using hmeet
  have key₁ : ∀ a : X, a ∈ U → ∀ c : X, c ∈ U ∪ ⋃ i, W i →
      JoinedIn (U ∪ ⋃ i, W i) a c := by
    intro a ha c hc
    rcases hc with hc | hc
    · exact JoinedIn.mono ((joinedIn_iff_joined ha hc).mpr
        (hU.joined ⟨a, ha⟩ ⟨c, hc⟩)) hUsub
    · obtain ⟨i, hci⟩ := Set.mem_iUnion.mp hc
      exact (JoinedIn.mono ((joinedIn_iff_joined ha (hbU i)).mpr
          (hU.joined ⟨a, ha⟩ ⟨b i, hbU i⟩)) hUsub).trans
        (JoinedIn.mono ((joinedIn_iff_joined (hbW i) hci).mpr
          ((hW i).joined ⟨b i, hbW i⟩ ⟨c, hci⟩)) (hWsub i))
  have key₂ : ∀ a : X, a ∈ U ∪ ⋃ i, W i → ∀ c : X, c ∈ U ∪ ⋃ i, W i →
      JoinedIn (U ∪ ⋃ i, W i) a c := by
    intro a ha c hc
    rcases ha with ha | ha
    · exact key₁ a ha c hc
    · obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
      exact (JoinedIn.mono ((joinedIn_iff_joined hai (hbW i)).mpr
        ((hW i).joined ⟨a, hai⟩ ⟨b i, hbW i⟩)) (hWsub i)).trans (key₁ (b i) (hbU i) c hc)
  refine ⟨hU.nonempty.map (Subtype.map id hUsub), ?_⟩
  rintro ⟨a, ha⟩ ⟨c, hc⟩
  exact (key₂ a ha c hc).joined_subtype

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_union_iUnion_of_meets
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.pathConnectedSpace_union_iUnion_of_meets target :: scope.openDecls } }

private theorem simplyConnected_coverMembers_aux {X : Type u} [TopologicalSpace X] (n : ℕ)
    (U : Set X) (V : Fin n → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hUpc : PathConnectedSpace ↥U) (hVpc : ∀ i, PathConnectedSpace ↥(V i))
    (hunion : SimplyConnectedSpace ↥(U ∪ ⋃ i, V i))
    (hinter : ∀ i, SimplyConnectedSpace ↥(U ∩ V i)) :
    SimplyConnectedSpace ↥U ∧ ∀ i, SimplyConnectedSpace ↥(V i) := by
  classical
  induction n with
  | zero =>
    have hUeq : U ∪ ⋃ i : Fin 0, V i = U := by simp
    exact ⟨simplyConnectedSpace_of_set_eq_aux hUeq.symm hunion, fun i => i.elim0⟩
  | succ n ih =>
    let W : Fin n → Set X := fun i => V i.castSucc
    let Y : Set X := V (Fin.last n)
    have hWopen : ∀ i, IsOpen (W i) := fun i => hV i.castSucc
    have hWpc : ∀ i, PathConnectedSpace ↥(W i) := fun i => hVpc i.castSucc
    have hYpc : PathConnectedSpace ↥Y := hVpc (Fin.last n)
    have hWdisj : Pairwise fun i j => Disjoint (W i) (W j) :=
      fun i j hij => hdisj fun h => hij (Fin.castSucc_inj.mp h)
    have hWint : ∀ i, SimplyConnectedSpace ↥(U ∩ W i) := fun i => hinter i.castSucc
    have hYint : SimplyConnectedSpace ↥(U ∩ Y) := hinter (Fin.last n)
    have hdisjY : ∀ i : Fin n, Disjoint (W i) Y := fun i =>
      hdisj (finCastSucc_ne_last_aux i)
    have hunion' : SimplyConnectedSpace ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y) := by
      have h : U ∪ ⋃ i : Fin (n + 1), V i = (U ∪ ⋃ i : Fin n, W i) ∪ Y := by
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
        ext x
        simp only [Set.mem_union, Set.mem_iUnion]
        tauto
      rwa [h] at hunion
    let B : Set X := (U ∪ ⋃ i : Fin n, W i) ∪ Y
    have hAZ : (U ∪ ⋃ i : Fin n, W i) ⊆ B := Set.subset_union_left
    have hYZ : Y ⊆ B := Set.subset_union_right
    have hIntEq : (U ∪ ⋃ i : Fin n, W i) ∩ Y = U ∩ Y := by
      ext x
      constructor
      · rintro ⟨hx, hxY⟩
        rcases hx with hx | hx
        · exact ⟨hx, hxY⟩
        · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
          exact absurd hxY (Set.disjoint_left.mp (hdisjY i) hxi)
      · rintro ⟨hx, hxY⟩
        exact ⟨Or.inl hx, hxY⟩
    have hApc : PathConnectedSpace ↥(U ∪ ⋃ i : Fin n, W i) :=
      pathConnectedSpace_union_iUnion_of_meets U W hUpc hWpc
        (fun i => show (U ∩ W i).Nonempty from Set.nonempty_coe_sort.mp
          ((inferInstance : PathConnectedSpace ↥(U ∩ W i))).nonempty)
    let A' : Set ↥B := {x | x.1 ∈ U ∪ ⋃ i : Fin n, W i}
    let Y' : Set ↥B := {x | x.1 ∈ Y}
    have hA'pc : PathConnectedSpace ↥A' := pathConnectedSpace_of_subtypePreimage_aux hAZ hApc
    have hY'pc : PathConnectedSpace ↥Y' := pathConnectedSpace_of_subtypePreimage_aux hYZ hYpc
    have hIntSC : SimplyConnectedSpace ↥{x : ↥B | x.1 ∈ U ∩ Y} :=
      simplyConnectedSpace_of_subtypePreimage_aux (fun x hx => Or.inl (Or.inl hx.1)) hYint
    have hIntSC' : SimplyConnectedSpace ↥(A' ∩ Y') := by
      have hset : A' ∩ Y' = {x : ↥B | x.1 ∈ U ∩ Y} := by
        rw [show A' ∩ Y' = {x : ↥B | x.1 ∈ (U ∪ ⋃ i : Fin n, W i) ∩ Y} from rfl,
          hIntEq]
      exact simplyConnectedSpace_of_set_eq_aux hset hIntSC
    obtain ⟨z⟩ := (inferInstance : PathConnectedSpace ↥(U ∩ Y)).nonempty
    have hzA : z.1 ∈ U ∪ ⋃ i : Fin n, W i := Or.inl z.2.1
    have hzY : z.1 ∈ Y := z.2.2
    let x₀ : ↥B := ⟨z.1, hYZ hzY⟩
    have hx₀ : x₀ ∈ A' ∩ Y' := ⟨hzA, hzY⟩
    have hmain : SimplyConnectedSpace ↥A' ∧ SimplyConnectedSpace ↥Y' := by
      let _ : PathConnectedSpace ↥A' := hA'pc
      let _ : PathConnectedSpace ↥Y' := hY'pc
      let _ : SimplyConnectedSpace ↥B := hunion'
      let _ : SimplyConnectedSpace ↥(A' ∩ Y') := hIntSC'
      exact DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_union
        A' Y'
        (IsOpen.preimage continuous_subtype_val (hU.union (isOpen_iUnion hWopen)))
        (IsOpen.preimage continuous_subtype_val (hV (Fin.last n)))
        (by
          refine Set.eq_univ_of_forall fun x => ?_
          rcases x.2 with h | h
          · exact Or.inl h
          · exact Or.inr h)
        x₀ hx₀
    have hAsc : SimplyConnectedSpace ↥(U ∪ ⋃ i : Fin n, W i) :=
      ((subtypePreimageHomeomorph_aux hAZ).toHomotopyEquiv.simplyConnectedSpace_iff).mp hmain.1
    have hYsc : SimplyConnectedSpace ↥Y :=
      ((subtypePreimageHomeomorph_aux hYZ).toHomotopyEquiv.simplyConnectedSpace_iff).mp hmain.2
    obtain ⟨hUsc, hWsc⟩ := ih W hWopen hWdisj hWpc hAsc hWint
    refine ⟨hUsc, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact hYsc
    | cast j => exact hWsc j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_aux target :: scope.openDecls } }

theorem simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (U : Set X) (V : Fin n → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hUpc : PathConnectedSpace ↥U) (hVpc : ∀ i, PathConnectedSpace ↥(V i))
    (hunion : SimplyConnectedSpace ↥(U ∪ ⋃ i, V i))
    (hinter : ∀ i, SimplyConnectedSpace ↥(U ∩ V i)) :
    SimplyConnectedSpace ↥U ∧ ∀ i, SimplyConnectedSpace ↥(V i) :=
  simplyConnected_coverMembers_aux n U V hU hV hdisj hUpc hVpc hunion hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint ``Submission.DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint

theorem simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hUpc : PathConnectedSpace ↥U) (hVpc : ∀ i, PathConnectedSpace ↥(V i))
    (hunion : SimplyConnectedSpace ↥(U ∪ ⋃ i, V i))
    (hinter : ∀ i, SimplyConnectedSpace ↥(U ∩ V i)) :
    SimplyConnectedSpace ↥U ∧ ∀ i, SimplyConnectedSpace ↥(V i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let V' : Fin (Fintype.card ι) → Set X := fun i => V (e.symm i)
  have hV' : ∀ i, IsOpen (V' i) := fun i => hV _
  have hdisj' : Pairwise fun i j => Disjoint (V' i) (V' j) :=
    fun i j hij => hdisj fun h => hij (e.symm.injective h)
  have hVpc' : ∀ i : Fin (Fintype.card ι), PathConnectedSpace ↥(V' i) :=
    fun i => hVpc (e.symm i)
  have hinter' : ∀ i : Fin (Fintype.card ι), SimplyConnectedSpace ↥(U ∩ V' i) :=
    fun i => hinter (e.symm i)
  have hunion' : SimplyConnectedSpace ↥(U ∪ ⋃ i : Fin (Fintype.card ι), V' i) := by
    have h : (⋃ i : Fin (Fintype.card ι), V' i) = ⋃ i : ι, V i := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨e.symm i, hxi⟩
      · intro hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨e i, by simpa [V', e.symm_apply_apply] using hxi⟩
    rw [h]
    exact hunion
  obtain ⟨h1, h2⟩ := simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint
    U V' hU hV' hdisj' hUpc hVpc' hunion' hinter'
  exact ⟨h1, fun i => e.symm_apply_apply i ▸ h2 (e i)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype ``Submission.DifferentialGeometry.Topology.VanKampen.simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype

end DifferentialGeometry.Topology.VanKampen

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

private theorem pathConnectedSpace_of_homotopyEquiv_aux {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X] (e : X ≃ₕ Y) :
    PathConnectedSpace Y := by
  constructor
  · exact ⟨e (Classical.choice (inferInstance : Nonempty X))⟩
  · intro y₀ y₁
    obtain ⟨H⟩ := e.right_inv
    have h₀ : Joined y₀ (e (e.symm y₀)) := ⟨(H.evalAt y₀).symm⟩
    have hmid : Joined (e (e.symm y₀)) (e (e.symm y₁)) :=
      (PathConnectedSpace.joined (e.symm y₀) (e.symm y₁)).map e.continuous
    have h₁ : Joined (e (e.symm y₁)) y₁ := ⟨H.evalAt y₁⟩
    exact h₀.trans (hmid.trans h₁)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_of_homotopyEquiv_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_of_homotopyEquiv_aux target :: scope.openDecls } }

theorem pathConnectedSpace_componentCarrier_of_locallyPathConnected {Y : Type u}
    [TopologicalSpace Y] [LocallyPathConnectedSpace Y] (c : ConnectedComponents Y) :
    PathConnectedSpace (ComponentCarrier c) := by
  obtain ⟨x₀, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : ({y : Y | ConnectedComponents.mk y = ConnectedComponents.mk x₀} : Set Y) =
      connectedComponent x₀ := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  change PathConnectedSpace ↥({y : Y | ConnectedComponents.mk y = ConnectedComponents.mk x₀})
  rw [hset, ← pathComponent_eq_connectedComponent x₀]
  exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponent (x := x₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_componentCarrier_of_locallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_componentCarrier_of_locallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_componentCarrier_of_locallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.pathConnectedSpace_componentCarrier_of_locallyPathConnected

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem pathConnectedSpace_childCore (c : ConnectedComponents Q.Carrier) :
    PathConnectedSpace (E.ChildCore c) := by
  let _ : LocallyPathConnectedSpace (EuclideanHalfSpace 3) :=
    (EuclideanHalfSpace.convex (n := 3)).locallyPathConnectedSpace
  let _ : ChartedSpace (EuclideanHalfSpace 3) ↥E.trace.tubes.core := E.coreCharts
  let _ : LocallyPathConnectedSpace ↥E.trace.tubes.core :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanHalfSpace 3) ↥E.trace.tubes.core
  exact pathConnectedSpace_componentCarrier_of_locallyPathConnected (E.childCoreComponent c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pathConnectedSpace_childCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pathConnectedSpace_childCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pathConnectedSpace_childCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.pathConnectedSpace_childCore

open _root_.Submission.DifferentialGeometry.Topology.VanKampen in
theorem childCore_simplyConnected_of_childCarrierSimplyConnected
    (c : ConnectedComponents Q.Carrier) (d : E.ChildCarrierCollaredStarCover c)
    (h : SimplyConnectedSpace (E.ChildCarrier c)) :
    SimplyConnectedSpace (E.ChildCore c) := by
  let _ : PathConnectedSpace (E.ChildCore c) := E.pathConnectedSpace_childCore c
  let _ : PathConnectedSpace ThreeBall := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : ThreeSpace) 1).isPathConnected ⟨0, by simp⟩)
  let e := homotopyEquiv_of_retraction (E.childCoreInclusionRestrict c d.core_subset_U) d.retraction
    d.retraction_comp_inclusion d.inclusion_comp_retraction_homotopic
  have hUpc : PathConnectedSpace ↥d.U := pathConnectedSpace_of_homotopyEquiv_aux e
  have hVpc : ∀ b, PathConnectedSpace ↥(d.V b) := fun b =>
    pathConnectedSpace_of_homotopyEquiv_aux (Classical.choice (d.ball_homotopy_V b)).symm
  have hcov : SimplyConnectedSpace ↥(d.U ∪ ⋃ b, d.V b) :=
    d.cover.symm ▸
      (Homeomorph.Set.univ (E.ChildCarrier c)).toHomotopyEquiv.simplyConnectedSpace_iff.mpr h
  exact e.simplyConnectedSpace_iff.mpr
    (simplyConnected_coverMembers_of_open_cover_of_pairwise_disjoint_of_fintype d.U d.V
      d.isOpen_U d.isOpen_V d.disjoint_V hUpc hVpc hcov
      (fun b => d.simplyConnectedSpace_inter b)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_of_childCarrierSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_of_childCarrierSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_of_childCarrierSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_of_childCarrierSimplyConnected

theorem childCore_simplyConnected_iff_childCarrier_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    SimplyConnectedSpace (E.ChildCore c) ↔ SimplyConnectedSpace (E.ChildCarrier c) :=
  (E.childCoreHomeomorphOfIsEmptyChildCapBoundary c).toHomotopyEquiv.simplyConnectedSpace_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_iff_childCarrier_of_isEmpty_childCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_iff_childCarrier_of_isEmpty_childCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_iff_childCarrier_of_isEmpty_childCapBoundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCore_simplyConnected_iff_childCarrier_of_isEmpty_childCapBoundary

theorem childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier
    (hcover : E.childCollaredStarCoverProducer)
    (hchild : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        SimplyConnectedSpace (E.ChildCarrier c)) :
    E.childCoreSimplyConnectedOfParent :=
  fun c hpar => E.childCore_simplyConnected_of_childCarrierSimplyConnected c
    (hcover c hpar).some (hchild c hpar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier

theorem componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer
    (hcover : E.childCollaredStarCoverProducer)
    (hchild : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        SimplyConnectedSpace (E.ChildCarrier c)) :
    E.ComponentwisePuncturedCoreOfParent :=
  (E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mpr
    (E.childCoreSimplyConnectedOfParent_of_childCollaredStarCover_of_childCarrier hcover hchild)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer

theorem childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_childCarrier :
    ChildSimplicityFrontier E ↔
      E.childCollaredStarCoverProducer ∧
        ∀ c : ConnectedComponents Q.Carrier,
          SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
            SimplyConnectedSpace (E.ChildCarrier c) :=
  ⟨fun h => ⟨h.1, fun c _ => E.child_simplyConnected_of_childSimplicityFrontier h c⟩,
    fun h => ⟨h.1,
      E.componentwisePuncturedCoreOfParent_of_childCollaredStarCoverProducer h.1 h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_childCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_childCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_childCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childSimplicityFrontier_iff_childCollaredStarCoverProducer_and_childCarrier

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
