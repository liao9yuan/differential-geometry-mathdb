import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalRetainedMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialManifold
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionQuotient
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def quotientEqvGenHomeomorph {α : Type*} [TopologicalSpace α] (r : α → α → Prop) :
    Quot r ≃ₜ Quot (Relation.EqvGen r) where
  toFun := Quot.lift (fun a => Quot.mk (Relation.EqvGen r) a)
    (fun a b h => Quot.sound (Relation.EqvGen.rel a b h))
  invFun := Quot.lift (fun a => Quot.mk r a) (fun a b h => Quot.eq.mpr h)
  left_inv := by rintro q; induction q using Quot.induction_on with | _ a => rfl
  right_inv := by rintro q; induction q using Quot.induction_on with | _ a => rfl
  continuous_toFun := continuous_quot_lift _ continuous_quot_mk
  continuous_invFun := continuous_quot_lift _ continuous_quot_mk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientEqvGenHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientEqvGenHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientEqvGenHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientEqvGenHomeomorph

private def sumHomeomorphCongr {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') : X ⊕ Y ≃ₜ X' ⊕ Y' where
  toFun := Sum.map e₁ e₂
  invFun := Sum.map e₁.symm e₂.symm
  left_inv := by rintro (_ | _) <;> simp
  right_inv := by rintro (_ | _) <;> simp
  continuous_toFun := Continuous.sumMap e₁.continuous e₂.continuous
  continuous_invFun := Continuous.sumMap e₁.symm.continuous e₂.symm.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr target :: scope.openDecls } }

private def capOneHomeomorphThreeBall :
    {x : ThreeSpace // ‖x‖ ≤ 1} ≃ₜ ThreeBall where
  toFun := fun x => ⟨x.1, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact x.2⟩
  invFun := fun y => ⟨y.1, by
    have h := y.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val
    (fun x => by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact x.2)
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val
    (fun y => by
      have h := y.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphThreeBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphThreeBall target :: scope.openDecls } }

private def staticCapGluingEquiv (δ : ℝ) :
    {x : ThreeSpace // ‖x‖ ≤ 1} ⊕ (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)) ≃ₜ
      neckRetainedCollar δ ⊕ ThreeBall :=
  (Homeomorph.sumComm _ _).trans
    (sumHomeomorphCongr (neckRetainedCollarHomeomorph δ).symm capOneHomeomorphThreeBall)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv target :: scope.openDecls } }

@[simp] private theorem staticCapGluingEquiv_inl (δ : ℝ)
    (b : {x : ThreeSpace // ‖x‖ ≤ 1}) :
    staticCapGluingEquiv δ (Sum.inl b) = Sum.inr (capOneHomeomorphThreeBall b) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv_inl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv_inl target :: scope.openDecls } }

@[simp] private theorem staticCapGluingEquiv_inr (δ : ℝ)
    (r : Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)) :
    staticCapGluingEquiv δ (Sum.inr r) = Sum.inl ((neckRetainedCollarHomeomorph δ).symm r) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingEquiv_inr target :: scope.openDecls } }

private theorem capOneHomeomorphThreeBall_radialCapBoundary (z : Sphere 2) :
    capOneHomeomorphThreeBall (radialCapBoundary (L := 1) one_pos z) =
      sphereToThreeBall z := by
  apply Subtype.ext
  simp [capOneHomeomorphThreeBall, radialCapBoundary, sphereToThreeBall, one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphThreeBall_radialCapBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphThreeBall_radialCapBoundary target :: scope.openDecls } }

private theorem neckRetainedCollarHomeomorph_symm_retainedBoundary (δ : ℝ) (hδ : 0 < δ)
    (z : Sphere 2) :
    (neckRetainedCollarHomeomorph δ).symm
      (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ) z) =
      (⟨(z, 0), le_rfl, inv_pos.mpr hδ⟩ : neckRetainedCollar δ) := by
  apply Subtype.ext
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph_symm_retainedBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph_symm_retainedBoundary target :: scope.openDecls } }

private theorem eqvGen_comp_of_eqvGen {α β : Type*} {r : β → β → Prop} (f : α → β)
    {x y : α}
    (h : Relation.EqvGen (fun a b => Relation.EqvGen r (f a) (f b)) x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact Relation.EqvGen.refl (f a)
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eqvGen_comp_of_eqvGen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eqvGen_comp_of_eqvGen target :: scope.openDecls } }

private theorem eqvGen_adjunction_iff_staticCapGluing (δ : ℝ) (hδ : 0 < δ) :
    ∀ u v : {x : ThreeSpace // ‖x‖ ≤ 1} ⊕ (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)),
      Relation.EqvGen (adjunctionRel (radialCapBoundary (L := 1) one_pos)
          (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))) u v ↔
        Relation.EqvGen (staticCapGluingRel δ (Homeomorph.refl (Sphere 2)))
          (staticCapGluingEquiv δ u) (staticCapGluingEquiv δ v) := by
  set i := radialCapBoundary (L := 1) one_pos with hi
  set φ := retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ) with hφ
  set sc := staticCapGluingRel δ (Homeomorph.refl (Sphere 2)) with hsc
  set e := staticCapGluingEquiv δ with he
  have hz : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hinl : ∀ b : {x : ThreeSpace // ‖x‖ ≤ 1},
      e (Sum.inl b) = Sum.inr (capOneHomeomorphThreeBall b) := fun b => rfl
  have hinr : ∀ r : Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹),
      e (Sum.inr r) = Sum.inl ((neckRetainedCollarHomeomorph δ).symm r) := fun r => rfl
  have hball : ∀ z : Sphere 2, capOneHomeomorphThreeBall (i z) = sphereToThreeBall z :=
    fun z => capOneHomeomorphThreeBall_radialCapBoundary z
  have hret : ∀ z : Sphere 2, (neckRetainedCollarHomeomorph δ).symm (φ z) =
      (⟨(z, 0), le_rfl, hz⟩ : neckRetainedCollar δ) :=
    fun z => neckRetainedCollarHomeomorph_symm_retainedBoundary δ hδ z
  have hrefl : ∀ z : Sphere 2, (Homeomorph.refl (Sphere 2)) z = z := fun _ => rfl
  have step_fwd : ∀ u v, adjunctionRel i φ u v → Relation.EqvGen sc (e u) (e v) := by
    rintro u v ⟨z, h | h⟩
    · obtain ⟨rfl, rfl⟩ := h
      refine Relation.EqvGen.rel _ _ ⟨z, hz, ?_, ?_⟩
      · rw [hinl, hball]
      · rw [hinr, hret, hrefl]
    · obtain ⟨rfl, rfl⟩ := h
      refine Relation.EqvGen.symm _ _ ?_
      refine Relation.EqvGen.rel _ _ ⟨z, hz, ?_, ?_⟩
      · rw [hinl, hball]
      · rw [hinr, hret, hrefl]
  have step_bwd : ∀ u v, sc (e u) (e v) → Relation.EqvGen (adjunctionRel i φ) u v := by
    rintro u v ⟨z, hz', h1, h2⟩
    rcases u with b | r
    · rw [hinl] at h1
      have hb : capOneHomeomorphThreeBall b = sphereToThreeBall z := Sum.inr.inj h1
      have hbz : b = i z := by
        have hb' : b = capOneHomeomorphThreeBall.symm (sphereToThreeBall z) := by
          rw [← hb, Homeomorph.symm_apply_apply]
        rw [hb', ← hball z, Homeomorph.symm_apply_apply]
      rcases v with b' | r
      · rw [hinl] at h2
        exact absurd h2.symm (by simp)
      · rw [hinr] at h2
        have hr : (neckRetainedCollarHomeomorph δ).symm r =
            (⟨(z, 0), le_rfl, hz'⟩ : neckRetainedCollar δ) := Sum.inl.inj h2
        have hrz : r = φ z := by
          have h1' : r =
              neckRetainedCollarHomeomorph δ (⟨(z, 0), le_rfl, hz'⟩ : neckRetainedCollar δ) := by
            rw [← hr, Homeomorph.apply_symm_apply]
          have h2' : φ z =
              neckRetainedCollarHomeomorph δ (⟨(z, 0), le_rfl, hz'⟩ : neckRetainedCollar δ) := by
            rw [← Homeomorph.apply_symm_apply (neckRetainedCollarHomeomorph δ) (φ z), hret z]
          rw [h1', h2']
        rw [hbz, hrz]
        exact Relation.EqvGen.rel _ _ ⟨z, Or.inl ⟨rfl, rfl⟩⟩
    · rw [hinr] at h1
      exact absurd h1 (by simp)
  have step_bwd_symm : ∀ a b, sc a b →
      Relation.EqvGen (adjunctionRel i φ) (e.symm a) (e.symm b) := by
    intro a b hab
    refine step_bwd (e.symm a) (e.symm b) ?_
    simpa using hab
  intro u v
  constructor
  · intro h
    have hrp : adjunctionRel i φ ≤ fun a b => Relation.EqvGen sc (e a) (e b) :=
      fun a b hab => step_fwd a b hab
    exact eqvGen_comp_of_eqvGen e (Relation.EqvGen.mono hrp u v h)
  · intro h
    have hrp : sc ≤ fun a b => Relation.EqvGen (adjunctionRel i φ) (e.symm a) (e.symm b) :=
      fun a b hab => step_bwd_symm a b hab
    have := eqvGen_comp_of_eqvGen e.symm (Relation.EqvGen.mono hrp (e u) (e v) h)
    simpa using this

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eqvGen_adjunction_iff_staticCapGluing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eqvGen_adjunction_iff_staticCapGluing target :: scope.openDecls } }

def staticCapQuotientHomeomorphAdjunction (δ : ℝ) (hδ : 0 < δ) :
    StaticCapQuotient δ (Homeomorph.refl (Sphere 2)) ≃ₜ
      DifferentialGeometry.Topology.AdjunctionSpace (radialCapBoundary (L := 1) one_pos)
        (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ)) :=
  (Homeomorph.Quot.congr (staticCapGluingEquiv δ)
      (eqvGen_adjunction_iff_staticCapGluing δ hδ)).symm.trans
    (quotientEqvGenHomeomorph
      (adjunctionRel (radialCapBoundary (L := 1) one_pos)
        (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ)))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphAdjunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphAdjunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphAdjunction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphAdjunction


@[instance_reducible] def staticCapQuotientChartedSpace (δ : ℝ) (hδ : 0 < δ) :
    ChartedSpace ThreeSpace (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) :=
  @DifferentialGeometry.Topology.Handle.chartedSpaceOfHomeomorph ThreeSpace _
    (DifferentialGeometry.Topology.AdjunctionSpace (radialCapBoundary (L := 1) one_pos)
      (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))) _
    (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) _
    (staticCapQuotientHomeomorphAdjunction δ hδ)
    (radialCapAttachmentChartedSpace (L := 1) (B := δ⁻¹) one_pos (inv_pos.mpr hδ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientChartedSpace

theorem staticCapQuotient_isManifold (δ : ℝ) (hδ : 0 < δ) :
    @IsManifold ℝ _ ThreeSpace _ _ ThreeSpace _ ThreeModel ∞
      (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) _
      (staticCapQuotientChartedSpace δ hδ) :=
  @DifferentialGeometry.Topology.Handle.isManifoldOfHomeomorph ℝ _ ThreeSpace ThreeSpace _ _ _
    ThreeModel
    (DifferentialGeometry.Topology.AdjunctionSpace (radialCapBoundary (L := 1) one_pos)
      (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))) _
    (radialCapAttachmentChartedSpace (L := 1) (B := δ⁻¹) one_pos (inv_pos.mpr hδ))
    ∞ (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) _
    (staticCapQuotientHomeomorphAdjunction δ hδ)
    (radialCapAttachment_isManifold (L := 1) (B := δ⁻¹) one_pos (inv_pos.mpr hδ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_isManifold

theorem staticCapQuotient_t2Space (δ : ℝ) (hδ : 0 < δ) :
    T2Space (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) := by
  have hunit : T2Space
      (DifferentialGeometry.Topology.AdjunctionSpace (radialCapBoundary (L := 1) one_pos)
        (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))) :=
    radialCapAttachment_t2Space (L := 1) (B := δ⁻¹) one_pos (inv_pos.mpr hδ)
  exact (staticCapQuotientHomeomorphAdjunction δ hδ).symm.t2Space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_t2Space ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_t2Space

theorem staticCapQuotient_secondCountableTopology (δ : ℝ) (hδ : 0 < δ) :
    SecondCountableTopology (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) := by
  have hunit : SecondCountableTopology
      (DifferentialGeometry.Topology.AdjunctionSpace (radialCapBoundary (L := 1) one_pos)
        (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))) :=
    radialCapAttachment_secondCountableTopology (L := 1) (B := δ⁻¹) one_pos
      (inv_pos.mpr hδ)
  exact (staticCapQuotientHomeomorphAdjunction δ hδ).secondCountableTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_secondCountableTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_secondCountableTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_secondCountableTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotient_secondCountableTopology

private theorem norm_smul_transitionEnd_le {x : ThreeSpace} (hx : ‖x‖ ≤ 1) :
    ‖StandardCap.transitionEnd • x‖ ≤ StandardCap.transitionEnd := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos StandardCap.transitionEnd_pos]
  nlinarith [hx, StandardCap.transitionEnd_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.norm_smul_transitionEnd_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.norm_smul_transitionEnd_le target :: scope.openDecls } }

private theorem norm_smul_transitionEndInv_le {y : ThreeSpace}
    (hy : ‖y‖ ≤ StandardCap.transitionEnd) :
    ‖StandardCap.transitionEnd⁻¹ • y‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr StandardCap.transitionEnd_pos)]
  have h := mul_le_mul_of_nonneg_left hy (le_of_lt (inv_pos.mpr StandardCap.transitionEnd_pos))
  rwa [inv_mul_cancel₀ (ne_of_gt StandardCap.transitionEnd_pos)] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.norm_smul_transitionEndInv_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.norm_smul_transitionEndInv_le target :: scope.openDecls } }

private def capOneHomeomorphCapTransitionEnd :
    {x : ThreeSpace // ‖x‖ ≤ 1} ≃ₜ
      {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} where
  toFun := fun x => ⟨StandardCap.transitionEnd • x.1, norm_smul_transitionEnd_le x.2⟩
  invFun := fun y => ⟨StandardCap.transitionEnd⁻¹ • y.1, norm_smul_transitionEndInv_le y.2⟩
  left_inv := fun x => Subtype.ext (by
    change StandardCap.transitionEnd⁻¹ • (StandardCap.transitionEnd • (x.1 : ThreeSpace))
      = x.1
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt StandardCap.transitionEnd_pos), one_smul])
  right_inv := fun y => Subtype.ext (by
    change StandardCap.transitionEnd • (StandardCap.transitionEnd⁻¹ • (y.1 : ThreeSpace))
      = y.1
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt StandardCap.transitionEnd_pos), one_smul])
  continuous_toFun := by
    have hc : Continuous (fun _ : {x : ThreeSpace // ‖x‖ ≤ 1} => StandardCap.transitionEnd) :=
      continuous_const
    have hcont : Continuous (fun x : {x : ThreeSpace // ‖x‖ ≤ 1} =>
        StandardCap.transitionEnd • (x.1 : ThreeSpace)) := hc.smul continuous_subtype_val
    exact Continuous.subtype_mk hcont (fun x => norm_smul_transitionEnd_le x.2)
  continuous_invFun := by
    have hc : Continuous (fun _ : {y : ThreeSpace // ‖y‖ ≤ StandardCap.transitionEnd} =>
        StandardCap.transitionEnd⁻¹) := continuous_const
    have hcont : Continuous (fun y : {y : ThreeSpace // ‖y‖ ≤ StandardCap.transitionEnd} =>
        StandardCap.transitionEnd⁻¹ • (y.1 : ThreeSpace)) := hc.smul continuous_subtype_val
    exact Continuous.subtype_mk hcont (fun y => norm_smul_transitionEndInv_le y.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphCapTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphCapTransitionEnd target :: scope.openDecls } }

@[simp] private theorem sumHomeomorphCongr_inl {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (b : X) :
    sumHomeomorphCongr e₁ e₂ (Sum.inl b) = Sum.inl (e₁ b) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_inl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_inl target :: scope.openDecls } }

@[simp] private theorem sumHomeomorphCongr_inr {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (r : Y) :
    sumHomeomorphCongr e₁ e₂ (Sum.inr r) = Sum.inr (e₂ r) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_inr target :: scope.openDecls } }

@[simp] private theorem sumHomeomorphCongr_symm_inl {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (b : X') :
    (sumHomeomorphCongr e₁ e₂).symm (Sum.inl b) = Sum.inl (e₁.symm b) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_symm_inl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_symm_inl target :: scope.openDecls } }

@[simp] private theorem sumHomeomorphCongr_symm_inr {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (r : Y') :
    (sumHomeomorphCongr e₁ e₂).symm (Sum.inr r) = Sum.inr (e₂.symm r) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_symm_inr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sumHomeomorphCongr_symm_inr target :: scope.openDecls } }

private theorem capOneHomeomorphCapTransitionEnd_radialCapBoundary (z : Sphere 2) :
    capOneHomeomorphCapTransitionEnd (radialCapBoundary (L := 1) one_pos z) =
      radialCapBoundary (L := StandardCap.transitionEnd) StandardCap.transitionEnd_pos z := by
  apply Subtype.ext
  simp [capOneHomeomorphCapTransitionEnd, radialCapBoundary, one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphCapTransitionEnd_radialCapBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.capOneHomeomorphCapTransitionEnd_radialCapBoundary target :: scope.openDecls } }

private theorem adjunctionRel_capOne_iff (δ : ℝ) (hδ : 0 < δ) :
    ∀ u v : {x : ThreeSpace // ‖x‖ ≤ 1} ⊕ (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)),
      adjunctionRel (radialCapBoundary (L := 1) one_pos)
          (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ)) u v ↔
        adjunctionRel (radialCapBoundary (L := StandardCap.transitionEnd)
            StandardCap.transitionEnd_pos) (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ))
          (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd (Homeomorph.refl _) u)
          (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd (Homeomorph.refl _) v) := by
  intro u v
  constructor
  · rintro ⟨z, h | h⟩
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨z, Or.inl ⟨?_, ?_⟩⟩
      · rw [sumHomeomorphCongr_inl, capOneHomeomorphCapTransitionEnd_radialCapBoundary]
      · rfl
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨z, Or.inr ⟨?_, ?_⟩⟩
      · rw [sumHomeomorphCongr_inl, capOneHomeomorphCapTransitionEnd_radialCapBoundary]
      · rfl
  · rintro ⟨z, h | h⟩
    · obtain ⟨h1, h2⟩ := h
      have hb : capOneHomeomorphCapTransitionEnd.symm
          (radialCapBoundary (L := StandardCap.transitionEnd) StandardCap.transitionEnd_pos z) =
          radialCapBoundary (L := 1) one_pos z := by
        rw [← capOneHomeomorphCapTransitionEnd_radialCapBoundary z, Homeomorph.symm_apply_apply]
      have h2' : v = Sum.inr (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ) z) := by
        have h := Homeomorph.symm_apply_apply (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd
          (Homeomorph.refl (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)))) v
        rw [← h, h2, sumHomeomorphCongr_symm_inr, Homeomorph.refl_symm,
          Homeomorph.refl_apply, id_eq]
      have h1' : u = Sum.inl (radialCapBoundary (L := 1) one_pos z) := by
        have h := Homeomorph.symm_apply_apply (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd
          (Homeomorph.refl (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)))) u
        rw [← h, h1, sumHomeomorphCongr_symm_inl, hb]
      rw [h1', h2']
      exact ⟨z, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨h1, h2⟩ := h
      have hb : capOneHomeomorphCapTransitionEnd.symm
          (radialCapBoundary (L := StandardCap.transitionEnd) StandardCap.transitionEnd_pos z) =
          radialCapBoundary (L := 1) one_pos z := by
        rw [← capOneHomeomorphCapTransitionEnd_radialCapBoundary z, Homeomorph.symm_apply_apply]
      have h2' : u = Sum.inr (retainedBoundary (B := δ⁻¹) (inv_pos.mpr hδ) z) := by
        have h := Homeomorph.symm_apply_apply (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd
          (Homeomorph.refl (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)))) u
        rw [← h, h2, sumHomeomorphCongr_symm_inr, Homeomorph.refl_symm,
          Homeomorph.refl_apply, id_eq]
      have h1' : v = Sum.inl (radialCapBoundary (L := 1) one_pos z) := by
        have h := Homeomorph.symm_apply_apply (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd
          (Homeomorph.refl (Sphere 2 × ↥(Set.Ico (0 : ℝ) δ⁻¹)))) v
        rw [← h, h1, sumHomeomorphCongr_symm_inl, hb]
      rw [h1', h2']
      exact ⟨z, Or.inr ⟨rfl, rfl⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.adjunctionRel_capOne_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.adjunctionRel_capOne_iff target :: scope.openDecls } }

def staticCapQuotientHomeomorphInsertionQuotient (δ : ℝ) (hδ : 0 < δ) :
    StaticCapQuotient δ (Homeomorph.refl (Sphere 2)) ≃ₜ
      StandardCap.InsertionQuotient (inv_pos.mpr hδ) :=
  (staticCapQuotientHomeomorphAdjunction δ hδ).trans
    (Homeomorph.Quot.congr (sumHomeomorphCongr capOneHomeomorphCapTransitionEnd
        (Homeomorph.refl _)) (adjunctionRel_capOne_iff δ hδ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphInsertionQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphInsertionQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphInsertionQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientHomeomorphInsertionQuotient

theorem PresentedStaticCap.exists_attaching_diffeomorph {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ}
    {b : (H.event i).RetainedBoundaryIndex} (S : PresentedStaticCap H i fixed D m η b) :
    ∃ γ : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2,
      (γ : Sphere 2 → Sphere 2) = (H.event i).transition.trace.capping.attaching b.1 :=
  ⟨S.witness.attaching, S.attaching_eq⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PresentedStaticCap
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PresentedStaticCap.exists_attaching_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PresentedStaticCap.exists_attaching_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PresentedStaticCap.exists_attaching_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PresentedStaticCap.exists_attaching_diffeomorph

theorem not_nonempty_presentedStaticCap_of_attaching_not_diffeomorph {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {η : ℝ}
    {b : (H.event i).RetainedBoundaryIndex}
    (h : ∀ γ : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2,
      (γ : Sphere 2 → Sphere 2) ≠ (H.event i).transition.trace.capping.attaching b.1) :
    IsEmpty (PresentedStaticCap H i fixed D m η b) :=
  ⟨fun S => (PresentedStaticCap.exists_attaching_diffeomorph S).elim fun γ hγ => h γ hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_presentedStaticCap_of_attaching_not_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_presentedStaticCap_of_attaching_not_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_presentedStaticCap_of_attaching_not_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_nonempty_presentedStaticCap_of_attaching_not_diffeomorph

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology.Handle

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (StandardCap.InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace StandardCap.transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (StandardCap.InsertionQuotient hB) :=
  radialCapAttachment_isManifold StandardCap.transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.quotientIsManifold target :: scope.openDecls } }

@[instance_reducible] def staticCapInsertionQuotientChartedSpace {δ : ℝ} (hδ : 0 < δ) :
    ChartedSpace ThreeSpace (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) :=
  chartedSpaceOfHomeomorph (staticCapQuotientHomeomorphInsertionQuotient δ hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotientChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotientChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotientChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotientChartedSpace

theorem staticCapInsertionQuotient_isManifold {δ : ℝ} (hδ : 0 < δ) :
    letI := staticCapInsertionQuotientChartedSpace hδ
    IsManifold ThreeModel ∞ (StaticCapQuotient δ (Homeomorph.refl (Sphere 2))) :=
  isManifoldOfHomeomorph ThreeModel (staticCapQuotientHomeomorphInsertionQuotient δ hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotient_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotient_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotient_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapInsertionQuotient_isManifold

def staticCapQuotientDiffeomorphInsertionQuotient {δ : ℝ} (hδ : 0 < δ) :
    letI := staticCapInsertionQuotientChartedSpace hδ
    StaticCapQuotient δ (Homeomorph.refl (Sphere 2)) ≃ₘ⟮ThreeModel, ThreeModel⟯
      StandardCap.InsertionQuotient (inv_pos.mpr hδ) := by
  letI := staticCapInsertionQuotientChartedSpace hδ
  exact
    { toEquiv := (staticCapQuotientHomeomorphInsertionQuotient δ hδ).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (staticCapQuotientHomeomorphInsertionQuotient δ hδ) ThreeModel ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (staticCapQuotientHomeomorphInsertionQuotient δ hδ) ThreeModel ∞ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient

theorem staticCapQuotientDiffeomorphInsertionQuotient_retained {δ : ℝ} (hδ : 0 < δ)
    (x : neckRetainedCollar δ) :
    letI := staticCapInsertionQuotientChartedSpace hδ
    staticCapQuotientDiffeomorphInsertionQuotient hδ (Quotient.mk _ (Sum.inl x)) =
      adjunctionLower (i := radialCapBoundary StandardCap.transitionEnd_pos)
        (retainedBoundary (inv_pos.mpr hδ)) (neckRetainedCollarHomeomorph δ x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_retained

theorem staticCapQuotientDiffeomorphInsertionQuotient_cap {δ : ℝ} (hδ : 0 < δ)
    (x : ThreeBall) :
    letI := staticCapInsertionQuotientChartedSpace hδ
    staticCapQuotientDiffeomorphInsertionQuotient hδ (Quotient.mk _ (Sum.inr x)) =
      adjunctionCell (radialCapBoundary StandardCap.transitionEnd_pos)
        (retainedBoundary (inv_pos.mpr hδ))
        ⟨StandardCap.transitionEnd • x.val, by
          have hx : ‖x.val‖ ≤ 1 := by
            simpa only [ThreeBall, Metric.mem_closedBall, dist_zero_right] using x.property
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos StandardCap.transitionEnd_pos]
          nlinarith [StandardCap.transitionEnd_pos]⟩ := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientDiffeomorphInsertionQuotient_cap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
