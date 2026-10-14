import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CommonScaleHornReparametrization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InwardDatumChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckRetention
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab {D : OneStepIncoming.{u}} : SigmaCompactSpace D.slab.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel D.slab.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierStageMemOpensTerminalRegularOpenSlab target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ) :
    Finite P.HornCutIndex := by
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFiniteHornCutIndex target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2+1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

theorem exists_common_scale_oriented_horn_necks_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ} (_ : ε ≤ δ) (hδ1 : δ < 1), δ⁻¹+2 < ε⁻¹ →
        ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (hδ : ∀ c e, δ₀ c e ≤ δ)
            (a : ∀ c, P.hornIndex c → ℝ)
            (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            let N' := fun j : P'.HornCutIndex => (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
            P'.core = P.core ∧
            (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y,t c e) ∧
              (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e) ∧
            ∃ (e : P'.HornCutIndex → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
              (he : ∀ j, sphereDiffeo (n := 2) (e j) spherePoint = (N' j).sphereMark)
              (side : P'.HornCutIndex → Bool)
              (ν : P'.HornCutIndex → Sphere 2 ≃ Sphere 2),
              let d := fun j => (N' j).rotatedDatum (e j) (he j) (side j)
              (∀ j, LinearMap.det (e j).toLinearMap = 1) ∧
              (∀ c e, δ⁻¹+1 < a c e) ∧
              (∀ j (q : bufferedCylinder δ),
                (d j).oriented.map q = P'.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2)) ∧
              let f := fun j => neckAmbientMap D.slab.terminalRegularOpen (d j).oriented
              ∃ (hf : ∀ j, _root_.Topology.IsOpenEmbedding (f j))
                (hd : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))),
                (∀ j side, cuttingSphereComponent (fun j => (d j).precision_pos) f hf hd (j,side) ∈
                  scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f (P'.coreRadius^2)⁻¹ ↔
                  side = _root_.Bool.true) ∧
                _root_.Set.MapsTo (Subtype.val : cutCore f → D.stage.Carrier)
                  (retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric f
                    (P'.coreRadius^2)⁻¹)) D.slab.terminalRegularOpen := by
  obtain ⟨eta,heta,hmatching⟩ := exists_common_scale_reparametrized_horn_necks_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hεδ hδ1 hfit
  have hδpos : 0 < δ := P.epsilon_pos.trans_le hεδ
  let δw := (δ⁻¹+1)⁻¹
  have hδw : 0 < δw := inv_pos.mpr (by positivity)
  have hδwi : δw⁻¹ = δ⁻¹+1 := inv_inv _
  have hfitw : δw⁻¹+1 < ε⁻¹ := by rw [hδwi]; linarith
  obtain ⟨Q₀,hQ₀,hfamily⟩ := hmatching P hε hδw hfitw
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ y
  obtain ⟨t,δ₀,k,N,a,β,γ,F,K,hK,hfix,hF,hcore,hdata⟩ := hfamily Q hQ y
  let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
  let hδ : ∀ c e, δ₀ c e ≤ δ := fun c e => (hdata c e).2.2.2.1.trans hεδ
  let N' := fun j : P'.HornCutIndex => (N j.1.val j.2).monoDelta (hδ j.1.val j.2) hδ1
  have hγ (j : P'.HornCutIndex) : γ j.1.val j.2 = 1 ∨ γ j.1.val j.2 = -1 :=
    (hdata j.1.val j.2).2.2.2.2.2.2.2.1
  choose side hside using fun j : P'.HornCutIndex => NormalizedNeck.exists_side_of_axial_sign
    (γ j.1.val j.2) (sq_eq_one_iff.mpr (hγ j))
  have hrotation (j : P'.HornCutIndex) : ∃ e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace,
      LinearMap.det e.toLinearMap = 1 ∧ sphereDiffeo (n := 2) e spherePoint = (N' j).sphereMark := by
    obtain ⟨e,hdet,he,_⟩ := (N' j).exists_rotatedDatum (side j)
    exact ⟨e,hdet,he⟩
  choose e hdet he using hrotation
  let d := fun j : P'.HornCutIndex => (N' j).rotatedDatum (e j) (he j) (side j)
  let ν := fun j : P'.HornCutIndex =>
    ((sphereDiffeo (n := 2) (e j)).toEquiv.trans (β j.1.val j.2).toEquiv.symm)
  have ham (c) (e : P'.hornIndex c) : δ⁻¹+1 < a c e := by
    have hh := (hdata c e).2.2.2.2.2.1
    rw [hδwi] at hh
    have hp := (P.hornCollar c e).radius_pos
    linarith
  have hm (j : P'.HornCutIndex) (q : bufferedCylinder δ) :
      (d j).oriented.map q = P'.horn j.1.val j.2 (ν j q.val.1, a j.1.val j.2 - q.val.2) := by
    have hwidth : |q.val.2| ≤ δw⁻¹ := by
      rw [hδwi]
      exact abs_le.mpr ⟨by linarith [q.property.1],q.property.2.le⟩
    obtain ⟨hmem,hmap⟩ := (hdata j.1.val j.2).2.2.2.2.2.2.2.2.2
      (ν j q.val.1) q.val.2 hwidth
    rw [hmap,normalizedDatum.oriented_map,NormalizedNeck.rotatedDatum_map]
    change (N j.1.val j.2).chart _ = _
    apply congrArg (N j.1.val j.2).chart
    apply Subtype.ext
    change (bufferedCylinderRotation δ (e j)
      (bufferedCylinderOrientation δ (d j).retainedSign (d j).retainedSign_sq q)).val =
      (β j.1.val j.2 (ν j q.val.1),γ j.1.val j.2*q.val.2)
    rw [bufferedCylinderRotation_apply,bufferedCylinderOrientation_apply]
    have hs : (d j).retainedSign = γ j.1.val j.2 := hside j
    rw [hs]
    exact Prod.ext ((β j.1.val j.2).apply_symm_apply _).symm rfl
  refine ⟨t,δ₀,k,N,hδ,a,F,K,hK,hfix,hF,hcore,?_,e,he,side,ν,hdet,ham,hm,?_⟩
  · intro c e
    exact ⟨(hdata c e).1,(hdata c e).2.1,(hdata c e).2.2.1,(hdata c e).2.2.2.1,(hdata c e).2.2.2.2.1⟩
  · exact P'.retained_oriented_neck_family_of_horn_matching hδpos hδ1 a ham _ _ d ν hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_oriented_horn_necks_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_oriented_horn_necks_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_oriented_horn_necks_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_oriented_horn_necks_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
