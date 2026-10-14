import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalDiffeomorphism
import Submission.DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.S2 target :: scope.openDecls } }
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.CI
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ConnectedSumQuotient.CI target :: scope.openDecls } }

universe u v

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {N : ConnectedClosedOrientedManifold.{v} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)

def connectingCylinder (q : S2 × unitInterval) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  collarMap c.toBallChart d.toBallChart a.val
    (q.1, ⟨(1 - 2 * q.2.val) / 4, by
      constructor <;> linarith [q.2.property.1, q.2.property.2]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder

theorem continuous_connectingCylinder : Continuous (connectingCylinder c d a) := by
  apply (continuous_collarMap c.toBallChart d.toBallChart a.val).comp
  exact continuous_fst.prodMk
    ((by fun_prop : Continuous (fun q : S2 × unitInterval => (1 - 2 * q.2.val) / 4)).subtype_mk _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_connectingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_connectingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_connectingCylinder ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.continuous_connectingCylinder

theorem connectingCylinder_injective : _root_.Function.Injective (connectingCylinder c d a) := by
  intro p q hpq
  have he := congrArg (collarInv c.toBallChart d.toBallChart a.val) hpq
  rw [connectingCylinder, connectingCylinder, collarInv_collarMap, collarInv_collarMap] at he
  apply Prod.ext
  · exact congrArg (fun q : CollarDomain => q.1) he
  · apply Subtype.ext
    have ht := congrArg (fun q : CollarDomain => q.2.val) he
    change (1 - 2 * p.2.val) / 4 = (1 - 2 * q.2.val) / 4 at ht
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_injective ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_injective

theorem isClosedEmbedding_connectingCylinder :
    _root_.Topology.IsClosedEmbedding (connectingCylinder c d a) :=
  (continuous_connectingCylinder c d a).isClosedEmbedding (connectingCylinder_injective c d a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isClosedEmbedding_connectingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isClosedEmbedding_connectingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isClosedEmbedding_connectingCylinder ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isClosedEmbedding_connectingCylinder

theorem connectingCylinder_zero (z : S2) :
    connectingCylinder c d a (z, 0) =
      inl c.toBallChart d.toBallChart a.val.toHomeomorph
        (c.toBallChart.radialMap z (5 / 4) (by constructor <;> norm_num)) := by
  unfold connectingCylinder
  rw [collarMap_of_nonneg _ _ _ _ (by norm_num)]
  apply congrArg (inl c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change c.chart ((1 + (1 - 2 * (0 : ℝ)) / 4) • z.val) = _
  congr 2
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_zero ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_zero

theorem connectingCylinder_one (z : S2) :
    connectingCylinder c d a (z, 1) =
      inr c.toBallChart d.toBallChart a.val.toHomeomorph
        (d.toBallChart.radialMap (a.val z) (5 / 4) (by constructor <;> norm_num)) := by
  unfold connectingCylinder
  rw [collarMap_of_neg _ _ _ _ (by norm_num)]
  apply congrArg (inr c.toBallChart d.toBallChart a.val.toHomeomorph)
  apply Subtype.ext
  change d.chart ((1 - (1 - 2 * (1 : ℝ)) / 4) • (a.val z).val) = _
  congr 2
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_one ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_one

theorem connectingCylinder_half (z : S2) :
    connectingCylinder c d a (z, ⟨1 / 2, by constructor <;> norm_num⟩) =
      inl c.toBallChart d.toBallChart a.val.toHomeomorph (c.toBallChart.boundaryMap z) := by
  have heq : (⟨(1 - 2 * (1 / 2 : ℝ)) / 4, by constructor <;> norm_num⟩ : collarInterval) =
      ⟨0, by constructor <;> norm_num [collarInterval]⟩ := Subtype.ext (by norm_num)
  change collarMap c.toBallChart d.toBallChart a.val (z, _) = _
  rw [heq]
  exact collarMap_zero_left _ _ _ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_half ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinder_half

def connectingCylinderDomain : TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨univ ×ˢ _root_.Set.Ioo (-(1 / 2 : ℝ)) (3 / 2), isOpen_univ.prod isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderDomain ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderDomain

def connectingCylinderOpen (q : connectingCylinderDomain) :
    (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.Carrier :=
  collarMap c.toBallChart d.toBallChart a.val
    (q.val.1, ⟨(1 - 2 * q.val.2) / 4, by
      constructor <;> linarith [q.property.2.1, q.property.2.2]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen

theorem isLocalDiffeomorph_connectingCylinderOpen :
    IsLocalDiffeomorph CI (𝓡 3) ∞ (connectingCylinderOpen c d a) := by
  let Q := (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold
  let F : (S2 × ℝ) ≃ₘ⟮CI, CI⟯ (S2 × ℝ) :=
    Diffeomorph.fiberwiseAffine (fun _ => (1 / 4 : ℝ)) (fun _ => (-(1 / 2) : ℝ))
      contMDiff_const contMDiff_const (by intro; norm_num)
  have hF (q : S2 × ℝ) : F q = (q.1, (1 - 2 * q.2) / 4) := by
    change (q.1, 1 / 4 + -(1 / 2) * q.2) = _
    congr 1
    ring
  let phi : connectingCylinderDomain → CollarDomain := fun q =>
    (q.val.1, ⟨(1 - 2 * q.val.2) / 4, by
      constructor <;> linarith [q.property.2.1, q.property.2.2]⟩)
  let U : TopologicalSpace.Opens (S2 × ℝ) :=
    ⟨univ ×ˢ (collarInterval : Set ℝ), isOpen_univ.prod collarInterval.isOpen⟩
  have hloc : IsLocalDiffeomorph CI CI ∞ (fun q : connectingCylinderDomain => F q.val) := by
    intro q
    exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val connectingCylinderDomain q).comp
      CI (S2 × ℝ) (F.isLocalDiffeomorph q.val)
  have hmem : ∀ q : connectingCylinderDomain, F q.val ∈ U := by
    intro q
    rw [hF]
    exact ⟨mem_univ _, (phi q).2.property⟩
  have hlocU := fun q : connectingCylinderDomain =>
    DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem (hloc q)
  let e : U ≃ₘ⟮CI, CI⟯ CollarDomain :=
    { toFun q := (q.val.1, ⟨q.val.2, q.property.2⟩)
      invFun q := ⟨(q.1, q.2.val), _root_.Set.mem_univ _, q.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      contMDiff_toFun := by
        apply ContMDiff.prodMk
        · exact contMDiff_fst.comp contMDiff_subtype_val
        · apply (ContMDiff.subtypeVal_comp_iff collarInterval _).mp
          change ContMDiff CI 𝓘(ℝ) ∞ (fun q : U => q.val.2)
          exact contMDiff_snd.comp contMDiff_subtype_val
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff U _).mp
        exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd) }
  have hphi : IsLocalDiffeomorph CI CI ∞ phi := by
    intro q
    have h := (hlocU q).comp CI CollarDomain (e.isLocalDiffeomorph _)
    have heq : (fun q : connectingCylinderDomain => e ⟨F q.val, hmem q⟩) = phi := by
      funext q
      apply Prod.ext
      · change (F q.val).1 = q.val.1
        rw [hF]
      · apply Subtype.ext
        change (F q.val).2 = (1 - 2 * q.val.2) / 4
        rw [hF]
    exact heq ▸ h
  intro q
  exact (hphi q).comp (𝓡 3) Q.Carrier
    ((smoothConnectedSum M N c d a).collar_localDiffeomorph (phi q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.isLocalDiffeomorph_connectingCylinderOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.isLocalDiffeomorph_connectingCylinderOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.isLocalDiffeomorph_connectingCylinderOpen ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.isLocalDiffeomorph_connectingCylinderOpen

theorem connectingCylinderOpen_restrict (q : S2 × unitInterval) :
    connectingCylinderOpen c d a ⟨(q.1, q.2.val), _root_.Set.mem_univ _, by
      constructor <;> linarith [q.2.property.1, q.2.property.2]⟩ =
      connectingCylinder c d a q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen_restrict ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.connectingCylinderOpen_restrict


end DifferentialGeometry.Topology.ConnectedSumQuotient
