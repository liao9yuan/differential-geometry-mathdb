import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M M' : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [TopologicalSpace M'] [ChartedSpace ThreeSpace M']
  [IsManifold ThreeModel ∞ M']

omit [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ M'] in
private theorem extend_sumInl (p x : M) :
    ((chartAt ThreeSpace (Sum.inl p : M ⊕ M')).extend ThreeModel) ∘
        ((chartAt ThreeSpace (Sum.inl x : M ⊕ M')).extend ThreeModel).symm =
      ((chartAt ThreeSpace p).extend ThreeModel) ∘
        ((chartAt ThreeSpace x).extend ThreeModel).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInl target :: scope.openDecls } }

omit [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ M'] in
private theorem extend_sumInr (p x : M') :
    ((chartAt ThreeSpace (Sum.inr p : M ⊕ M')).extend ThreeModel) ∘
        ((chartAt ThreeSpace (Sum.inr x : M ⊕ M')).extend ThreeModel).symm =
      ((chartAt ThreeSpace p).extend ThreeModel) ∘
        ((chartAt ThreeSpace x).extend ThreeModel).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInr target :: scope.openDecls } }

omit [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ M'] in
private theorem extend_sumInl_apply (x : M) :
    ((chartAt ThreeSpace (Sum.inl x : M ⊕ M')).extend ThreeModel) (Sum.inl x) =
      ((chartAt ThreeSpace x).extend ThreeModel) x := by
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    ChartedSpace.sum_chartAt_inl, OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInl_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInl_apply target :: scope.openDecls } }

omit [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ M'] in
private theorem extend_sumInr_apply (x : M') :
    ((chartAt ThreeSpace (Sum.inr x : M ⊕ M')).extend ThreeModel) (Sum.inr x) =
      ((chartAt ThreeSpace x).extend ThreeModel) x := by
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    ChartedSpace.sum_chartAt_inr, OpenPartialHomeomorph.lift_openEmbedding_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInr_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extend_sumInr_apply target :: scope.openDecls } }

private theorem tangentChartEquiv_sumInl_apply (p x : M)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hx' : (Sum.inl x : M ⊕ M') ∈
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inl p)).baseSet)
    (v : TangentSpace ThreeModel x) :
    tangentChartEquiv (M ⊕ M') (Sum.inl p) (Sum.inl x) hx'
        (show TangentSpace ThreeModel (Sum.inl x) from v) =
      tangentChartEquiv M p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sumInl, extend_sumInl_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInl_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInl_apply target :: scope.openDecls } }

private theorem tangentChartEquiv_sumInr_apply (p x : M')
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hx' : (Sum.inr x : M ⊕ M') ∈
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inr p)).baseSet)
    (v : TangentSpace ThreeModel x) :
    tangentChartEquiv (M ⊕ M') (Sum.inr p) (Sum.inr x) hx'
        (show TangentSpace ThreeModel (Sum.inr x) from v) =
      tangentChartEquiv M' p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sumInr, extend_sumInr_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInr_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInr_apply target :: scope.openDecls } }

private theorem tangentChartEquiv_sumInl (p x : M)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hx' : (Sum.inl x : M ⊕ M') ∈
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inl p)).baseSet) :
    tangentChartEquiv (M ⊕ M') (Sum.inl p) (Sum.inl x) hx' =
      tangentChartEquiv M p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sumInl_apply p x hx hx' v

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInl target :: scope.openDecls } }

private theorem tangentChartEquiv_sumInr (p x : M')
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hx' : (Sum.inr x : M ⊕ M') ∈
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inr p)).baseSet) :
    tangentChartEquiv (M ⊕ M') (Sum.inr p) (Sum.inr x) hx' =
      tangentChartEquiv M' p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sumInr_apply p x hx hx' v

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.tangentChartEquiv_sumInr target :: scope.openDecls } }

private theorem mem_trivializationAt_sumInl_iff (p y : M) :
    (Sum.inl y : M ⊕ M') ∈
        (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inl p)).baseSet ↔
      y ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_source, TangentBundle.trivializationAt_baseSet]
  exact ⟨fun ⟨z, hz, hzy⟩ => by rw [Sum.inl_injective hzy] at hz; exact hz,
    fun hy => ⟨y, hy, rfl⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_trivializationAt_sumInl_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_trivializationAt_sumInl_iff target :: scope.openDecls } }

private theorem mem_trivializationAt_sumInr_iff (p y : M') :
    (Sum.inr y : M ⊕ M') ∈
        (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inr p)).baseSet ↔
      y ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_source, TangentBundle.trivializationAt_baseSet]
  exact ⟨fun ⟨z, hz, hzy⟩ => by rw [Sum.inr_injective hzy] at hz; exact hz,
    fun hy => ⟨y, hy, rfl⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_trivializationAt_sumInr_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.mem_trivializationAt_sumInr_iff target :: scope.openDecls } }

private theorem not_mem_trivializationAt_sumInl_inr (p : M) (y : M') :
    (Sum.inr y : M ⊕ M') ∉
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inl p)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hz⟩
  exact Sum.inl_ne_inr hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_mem_trivializationAt_sumInl_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_mem_trivializationAt_sumInl_inr target :: scope.openDecls } }

private theorem not_mem_trivializationAt_sumInr_inl (p : M') (y : M) :
    (Sum.inl y : M ⊕ M') ∉
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) (Sum.inr p)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hz⟩
  exact Sum.inr_ne_inl hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_mem_trivializationAt_sumInr_inl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_mem_trivializationAt_sumInr_inl target :: scope.openDecls } }

def sumTangentOrientationSection (o : TangentOrientationSection M)
    (o' : TangentOrientationSection M') : TangentOrientationSection (M ⊕ M') where
  orientation := fun x => match x with
    | Sum.inl q => o.orientation q
    | Sum.inr d => o'.orientation d
  locally_constant := by
    intro p x hx
    rcases p with p | p
    · rcases x with x | x
      · obtain ⟨U, hUopen, hxU, hUsub, hUc⟩ :=
          o.locally_constant p x ((mem_trivializationAt_sumInl_iff p x).mp hx)
        have hU' : Sum.inl '' U ⊆
            (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel)
              (Sum.inl p : M ⊕ M')).baseSet := by
          rintro _ ⟨y, hy, rfl⟩
          exact (mem_trivializationAt_sumInl_iff p y).mpr (hUsub hy)
        refine ⟨Sum.inl '' U, isOpenMap_inl U hUopen, ⟨x, hxU, rfl⟩, hU', ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        rw [tangentChartEquiv_sumInl (M' := M') p y (hUsub hy) (hU' ⟨y, hy, rfl⟩),
          tangentChartEquiv_sumInl (M' := M') p x ((mem_trivializationAt_sumInl_iff p x).mp hx) hx]
        exact hUc y hy
      · exact absurd hx (not_mem_trivializationAt_sumInl_inr p x)
    · rcases x with x | x
      · exact absurd hx (not_mem_trivializationAt_sumInr_inl p x)
      · obtain ⟨U, hUopen, hxU, hUsub, hUc⟩ :=
          o'.locally_constant p x ((mem_trivializationAt_sumInr_iff p x).mp hx)
        have hU' : Sum.inr '' U ⊆
            (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel)
              (Sum.inr p : M ⊕ M')).baseSet := by
          rintro _ ⟨y, hy, rfl⟩
          exact (mem_trivializationAt_sumInr_iff p y).mpr (hUsub hy)
        refine ⟨Sum.inr '' U, isOpenMap_inr U hUopen, ⟨x, hxU, rfl⟩, hU', ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        rw [tangentChartEquiv_sumInr (M := M) p y (hUsub hy) (hU' ⟨y, hy, rfl⟩),
          tangentChartEquiv_sumInr (M := M) p x ((mem_trivializationAt_sumInr_iff p x).mp hx) hx]
        exact hUc y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection

@[simp] theorem sumTangentOrientationSection_inl (o : TangentOrientationSection M)
    (o' : TangentOrientationSection M') (q : M) :
    (sumTangentOrientationSection o o').orientation (Sum.inl q) = o.orientation q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inl

@[simp] theorem sumTangentOrientationSection_inr (o : TangentOrientationSection M)
    (o' : TangentOrientationSection M') (d : M') :
    (sumTangentOrientationSection o o').orientation (Sum.inr d) = o'.orientation d := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inr ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumTangentOrientationSection_inr

def OrientedThreeStage.sum (Q D : OrientedThreeStage.{u}) : OrientedThreeStage.{u} where
  Carrier := Q.Carrier ⊕ D.Carrier
  orientation := sumTangentOrientationSection Q.orientation D.orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum

@[simp] theorem OrientedThreeStage.sum_carrier (Q D : OrientedThreeStage.{u}) :
    (Q.sum D).Carrier = (Q.Carrier ⊕ D.Carrier) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_carrier

@[simp] theorem OrientedThreeStage.sum_orientation_inl (Q D : OrientedThreeStage.{u})
    (q : Q.Carrier) :
    (Q.sum D).orientation.orientation (Sum.inl q) = Q.orientation.orientation q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inl

@[simp] theorem OrientedThreeStage.sum_orientation_inr (Q D : OrientedThreeStage.{u})
    (d : D.Carrier) :
    (Q.sum D).orientation.orientation (Sum.inr d) = D.orientation.orientation d := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inr ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_inr


theorem OrientedThreeStage.sum_orientation_apply (Q D : OrientedThreeStage.{u})
    (x : Q.Carrier ⊕ D.Carrier) :
    (Q.sum D).orientation.orientation x =
      match x with
      | Sum.inl q => Q.orientation.orientation q
      | Sum.inr d => D.orientation.orientation d := by
  cases x <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.sum_orientation_apply

theorem SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N) :
    PreservesTangentOrientation N.orientation
        (sumTangentOrientationSection Q.orientation D.orientation) X.presentation ↔
      ∀ x : N.Carrier,
        ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
          Orientation.map (Fin 3)
            (LinearEquiv.ofBijective
              (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
            (N.orientation.orientation x) =
            match X.presentation x with
            | Sum.inl q => Q.orientation.orientation q
            | Sum.inr d => D.orientation.orientation d := by
  constructor
  · intro h x
    obtain ⟨hf, hfx⟩ := h.2 x
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hfx
    rw [hfx]
    cases X.presentation x <;> rfl
  · intro h
    refine ⟨X.presentation.contMDiff_toFun, fun x => ?_⟩
    have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x) :=
      (X.presentation.mfderivToContinuousLinearEquiv (by simp) x).bijective
    obtain ⟨hf, hfx⟩ := h x
    rw [Subsingleton.elim hf hbij] at hfx
    refine ⟨hbij, ?_⟩
    unfold PreservesTangentOrientationAt
    refine hfx.trans ?_
    cases X.presentation x <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation

theorem SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : PreservesTangentOrientation N.orientation
      (sumTangentOrientationSection Q.orientation D.orientation) X.presentation) :
    ∀ x : N.Carrier,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
        Orientation.map (Fin 3)
          (LinearEquiv.ofBijective
            (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
          (N.orientation.orientation x) =
          match X.presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d :=
  (SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation X).mp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation

theorem SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ x : N.Carrier,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x),
        Orientation.map (Fin 3)
          (LinearEquiv.ofBijective
            (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf)
          (N.orientation.orientation x) =
          match X.presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d) :
    PreservesTangentOrientation N.orientation
      (sumTangentOrientationSection Q.orientation D.orientation) X.presentation :=
  (SmoothCutCapTransition.presentation_positive_iff_preservesTangentOrientation X).mpr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.preservesTangentOrientation_of_presentation_positive

theorem CutCapTransitionData.presentation_positive_of_preservesTangentOrientation
    {P Q D N : OrientedThreeStage.{u}} (S : CutCapTransitionData P Q D N)
    (h : PreservesTangentOrientation N.orientation
      (sumTangentOrientationSection Q.orientation D.orientation) S.presentation) :
    ∀ x : N.Carrier,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel S.presentation x),
        Orientation.map (Fin 3)
          (LinearEquiv.ofBijective
            (mfderiv ThreeModel ThreeModel S.presentation x).toLinearMap hf)
          (N.orientation.orientation x) =
          match S.presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d :=
  SmoothCutCapTransition.presentation_positive_of_preservesTangentOrientation
    S.toSmoothCutCapTransition h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.presentation_positive_of_preservesTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.presentation_positive_of_preservesTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.presentation_positive_of_preservesTangentOrientation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTransitionData.presentation_positive_of_preservesTangentOrientation

theorem presentation_positive_self_sum (Q D : OrientedThreeStage.{u})
    (x : Q.Carrier ⊕ D.Carrier) :
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hf)
        ((Q.sum D).orientation.orientation x) =
        (Q.sum D).orientation.orientation x := by
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel
      (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x) := by
    rw [Diffeomorph.coe_refl, mfderiv_id]
    exact ⟨fun _ _ hab => hab, fun y => ⟨y, by simp⟩⟩
  refine ⟨hbij, ?_⟩
  have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
      (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hbij =
      LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.ofBijective_apply, Diffeomorph.coe_refl, mfderiv_id]
    simp
  rw [hlin]
  erw [Orientation.map_refl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_self_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_self_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_self_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_self_sum

theorem presentation_positive_refl_sum (Q D : OrientedThreeStage.{u})
    (x : Q.Carrier ⊕ D.Carrier) :
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Q.Carrier ⊕ D.Carrier) ∞) x).toLinearMap hf)
        ((Q.sum D).orientation.orientation x) =
        Sum.elim (fun q => Q.orientation.orientation q)
          (fun d => D.orientation.orientation d) x := by
  obtain ⟨hf, hfx⟩ := presentation_positive_self_sum Q D x
  refine ⟨hf, hfx.trans ?_⟩
  cases x <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_refl_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_refl_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_refl_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.presentation_positive_refl_sum

theorem sphereThreeStage_sum_nonempty : Nonempty (sphereThreeStage.sum sphereThreeStage).Carrier :=
  ⟨Sum.inl ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_sum_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_sum_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_sum_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_sum_nonempty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
