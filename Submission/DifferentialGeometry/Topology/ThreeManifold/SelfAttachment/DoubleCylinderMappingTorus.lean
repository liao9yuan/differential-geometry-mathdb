import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Defs
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusSmooth
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology
namespace DoubleCylinder

abbrev Cylinder := SphereTwo × _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.Cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.Cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.Cylinder ``Submission.DifferentialGeometry.Topology.DoubleCylinder.Cylinder

variable (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)

def attachingMap : Bool × SphereTwo → Cylinder
  | (_root_.Bool.false, z) => (z, ⟨0, by norm_num⟩)
  | (_root_.Bool.true, z) => (f.symm z, ⟨1, by norm_num⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.attachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.attachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.attachingMap ``Submission.DifferentialGeometry.Topology.DoubleCylinder.attachingMap

abbrev Space := AdjunctionSpace (SelfAttachment.boundaryInclusion (n := 3)) (attachingMap f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.Space ``Submission.DifferentialGeometry.Topology.DoubleCylinder.Space

def core : Cylinder → Space f := adjunctionLower (attachingMap f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.core ``Submission.DifferentialGeometry.Topology.DoubleCylinder.core
def band : Cylinder → Space f := adjunctionCell SelfAttachment.boundaryInclusion (attachingMap f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.band ``Submission.DifferentialGeometry.Topology.DoubleCylinder.band

def coreToMappingTorus (p : Cylinder) : SphereMappingTorus f :=
  Quotient.mk _ (p.1, ⟨p.2.val / 2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.coreToMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.coreToMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.coreToMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.coreToMappingTorus

def bandToMappingTorus (p : Cylinder) : SphereMappingTorus f :=
  Quotient.mk _ (f.symm p.1,
    ⟨1 - p.2.val / 2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.bandToMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.bandToMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.bandToMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.bandToMappingTorus

theorem toMappingTorus_seam (q : Bool × SphereTwo) :
    bandToMappingTorus f (SelfAttachment.boundaryInclusion q) =
      coreToMappingTorus f (attachingMap f q) := by
  rcases q with ⟨b, z⟩
  cases b
  · apply Quotient.sound
    apply Relation.EqvGen.rel
    refine ⟨by norm_num [SelfAttachment.boundaryInclusion], by norm_num [attachingMap], ?_⟩
    exact (f.apply_symm_apply z).symm
  · change Quotient.mk (sphereMappingTorusSetoid f) (f.symm z, ⟨1 - 1 / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) (f.symm z, ⟨1 / 2, _⟩)
    congr 1
    exact Prod.ext rfl (Subtype.ext (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_seam ``Submission.DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_seam

def toMappingTorus : Space f → SphereMappingTorus f :=
  Quot.lift (Sum.elim (bandToMappingTorus f) (coreToMappingTorus f)) (by
    rintro _ _ ⟨q, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact toMappingTorus_seam f q
    · exact (toMappingTorus_seam f q).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus

theorem continuous_toMappingTorus : Continuous (toMappingTorus f) := by
  apply continuous_adjunction_lift
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_quotient_mk'.comp
      ((f.symm.continuous.comp continuous_fst).prodMk
        ((continuous_const.sub ((continuous_subtype_val.comp continuous_snd).div_const 2)).subtype_mk _))
  · exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (((continuous_subtype_val.comp continuous_snd).div_const 2).subtype_mk _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.continuous_toMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.continuous_toMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.continuous_toMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.continuous_toMappingTorus

private def coreClamp (p : Cylinder) : Cylinder :=
  (p.1, ⟨min 1 (2 * p.2.val), le_min (by norm_num) (by nlinarith [p.2.property.1]), min_le_left _ _⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.coreClamp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.coreClamp target :: scope.openDecls } }

private def bandClamp (p : Cylinder) : Cylinder :=
  (f p.1, ⟨min 1 (2 - 2 * p.2.val), le_min (by norm_num) (by nlinarith [p.2.property.2]),
    min_le_left _ _⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.bandClamp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.bandClamp target :: scope.openDecls } }

def fromRepresentative (p : Cylinder) : Space f :=
  if p.2.val ≤ 1 / 2 then core f (coreClamp p) else band f (bandClamp f p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative ``Submission.DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative

private theorem fromRepresentative_of_le (p : Cylinder) (hp : p.2.val ≤ 1 / 2) :
    fromRepresentative f p = core f (p.1, ⟨2 * p.2.val,
      by constructor <;> nlinarith [p.2.property.1]⟩) := by
  simp only [fromRepresentative, if_pos hp, coreClamp,
    min_eq_right (by linarith : 2 * p.2.val ≤ 1)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_of_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_of_le target :: scope.openDecls } }

private theorem fromRepresentative_of_gt (p : Cylinder) (hp : 1 / 2 < p.2.val) :
    fromRepresentative f p = band f (f p.1, ⟨2 - 2 * p.2.val,
      by constructor <;> nlinarith [p.2.property.2]⟩) := by
  simp only [fromRepresentative, if_neg (not_le.mpr hp), bandClamp,
    min_eq_right (by linarith : 2 - 2 * p.2.val ≤ 1)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_of_gt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_of_gt target :: scope.openDecls } }

theorem continuous_fromRepresentative : Continuous (fromRepresentative f) := by
  have ht : Continuous (fun p : Cylinder => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous coreClamp :=
    continuous_fst.prodMk ((continuous_const.min (continuous_const.mul ht)).subtype_mk _)
  have hb : Continuous (bandClamp f) :=
    (f.continuous.comp continuous_fst).prodMk
      ((continuous_const.min (continuous_const.sub (continuous_const.mul ht))).subtype_mk _)
  apply continuous_if_le ht continuous_const
    ((continuous_adjunctionLower _ _).comp hc).continuousOn
    ((continuous_adjunctionCell _ _).comp hb).continuousOn
  intro p hp
  have hc1 : coreClamp p = (p.1, ⟨1, by norm_num⟩) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change _root_.Min.min 1 (2 * p.2.val) = 1
    rw [hp]
    norm_num
  have hb1 : bandClamp f p = (f p.1, ⟨1, by norm_num⟩) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change _root_.Min.min 1 (2 - 2 * p.2.val) = 1
    rw [hp]
    norm_num
  dsimp only [_root_.Function.comp_apply]
  rw [hc1, hb1]
  have h := (adjunction_coherence SelfAttachment.boundaryInclusion (attachingMap f) (_root_.Bool.true, f p.1)).symm
  simpa only [attachingMap, SelfAttachment.boundaryInclusion, f.symm_apply_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.continuous_fromRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.continuous_fromRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.continuous_fromRepresentative ``Submission.DifferentialGeometry.Topology.DoubleCylinder.continuous_fromRepresentative

theorem fromRepresentative_eq_of_rel {p q : Cylinder} (h : sphereMappingTorusRel f p q) :
    fromRepresentative f p = fromRepresentative f q := by
  obtain ⟨hp, hq, hz⟩ := h
  rw [fromRepresentative_of_gt f p (by rw [hp]; norm_num),
    fromRepresentative_of_le f q (by rw [hq]; norm_num)]
  have hpa : (f p.1, (⟨2 - 2 * p.2.val, by rw [hp]; norm_num⟩ : _root_.Set.Icc (0 : ℝ) 1)) =
      SelfAttachment.boundaryInclusion (_root_.Bool.false, f p.1) := by
    refine Prod.ext (by rfl) (Subtype.ext ?_)
    change 2 - 2 * p.2.val = 0
    rw [hp]
    norm_num
  have hqa : (q.1, (⟨2 * q.2.val, by rw [hq]; norm_num⟩ : _root_.Set.Icc (0 : ℝ) 1)) = attachingMap f (_root_.Bool.false, f p.1) := by
    refine Prod.ext hz (Subtype.ext ?_)
    change 2 * q.2.val = 0
    rw [hq, _root_.MulZeroClass.mul_zero]
  rw [hpa, hqa]
  exact adjunction_coherence _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_eq_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_eq_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_eq_of_rel ``Submission.DifferentialGeometry.Topology.DoubleCylinder.fromRepresentative_eq_of_rel

def fromMappingTorus : SphereMappingTorus f → Space f :=
  Quotient.lift (fromRepresentative f) (by
    intro p q h
    induction h with
    | rel _ _ h => exact fromRepresentative_eq_of_rel f h
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.fromMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.fromMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.fromMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.fromMappingTorus

theorem continuous_fromMappingTorus : Continuous (fromMappingTorus f) :=
  Continuous.quotient_lift (continuous_fromRepresentative f) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.continuous_fromMappingTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.continuous_fromMappingTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.continuous_fromMappingTorus ``Submission.DifferentialGeometry.Topology.DoubleCylinder.continuous_fromMappingTorus

theorem from_to_core (p : Cylinder) : fromMappingTorus f (toMappingTorus f (core f p)) = core f p := by
  change fromRepresentative f (p.1, ⟨p.2.val / 2, _⟩) = _
  rw [fromRepresentative_of_le f _ (by dsimp; linarith [p.2.property.2])]
  congr 1
  exact Prod.ext rfl (Subtype.ext (by dsimp; ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.from_to_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.from_to_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.from_to_core ``Submission.DifferentialGeometry.Topology.DoubleCylinder.from_to_core

theorem from_to_band (p : Cylinder) : fromMappingTorus f (toMappingTorus f (band f p)) = band f p := by
  change fromRepresentative f (f.symm p.1, ⟨1 - p.2.val / 2, _⟩) = _
  by_cases hp : p.2.val = 1
  · rw [fromRepresentative_of_le f _ (by dsimp; rw [hp]; norm_num)]
    have hq : (f.symm p.1, (⟨2 * (1 - p.2.val / 2), by rw [hp]; norm_num⟩ : _root_.Set.Icc (0 : ℝ) 1)) =
        attachingMap f (_root_.Bool.true, p.1) := by
      refine Prod.ext (by rfl) (Subtype.ext ?_)
      change 2 * (1 - p.2.val / 2) = 1
      rw [hp]
      norm_num
    have he : SelfAttachment.boundaryInclusion (_root_.Bool.true, p.1) = p := by
      exact Prod.ext rfl (Subtype.ext hp.symm)
    rw [hq, ← he]
    exact (adjunction_coherence _ _ _).symm
  · have hplt : p.2.val < 1 := lt_of_le_of_ne p.2.property.2 hp
    rw [fromRepresentative_of_gt f _ (by dsimp; linarith), f.apply_symm_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp; ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.from_to_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.from_to_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.from_to_band ``Submission.DifferentialGeometry.Topology.DoubleCylinder.from_to_band

theorem from_to (q : Space f) : fromMappingTorus f (toMappingTorus f q) = q := by
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl x => exact from_to_band f x
    | inr x => exact from_to_core f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.from_to then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.from_to"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.from_to ``Submission.DifferentialGeometry.Topology.DoubleCylinder.from_to

theorem to_from (q : SphereMappingTorus f) : toMappingTorus f (fromMappingTorus f q) = q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change toMappingTorus f (fromRepresentative f p) = _
    by_cases hp : p.2.val ≤ 1 / 2
    · rw [fromRepresentative_of_le f p hp]
      change Quotient.mk (sphereMappingTorusSetoid f) (p.1, ⟨(2 * p.2.val) / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) p
      congr 1
      exact Prod.ext rfl (Subtype.ext (by ring))
    · rw [fromRepresentative_of_gt f p (not_le.mp hp)]
      change Quotient.mk (sphereMappingTorusSetoid f) (f.symm (f p.1), ⟨1 - (2 - 2 * p.2.val) / 2, _⟩) = Quotient.mk (sphereMappingTorusSetoid f) p
      rw [f.symm_apply_apply]
      congr 1
      exact Prod.ext rfl (Subtype.ext (by ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.to_from then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.to_from"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.to_from ``Submission.DifferentialGeometry.Topology.DoubleCylinder.to_from

def mappingTorusHomeomorph : Space f ≃ₜ SphereMappingTorus f where
  toFun := toMappingTorus f
  invFun := fromMappingTorus f
  left_inv := from_to f
  right_inv := to_from f
  continuous_toFun := continuous_toMappingTorus f
  continuous_invFun := continuous_fromMappingTorus f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.mappingTorusHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.mappingTorusHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.mappingTorusHomeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.mappingTorusHomeomorph


private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.IC target :: scope.openDecls } }

def seamDomain : TopologicalSpace.Opens (SphereTwo × ℝ) :=
  ⟨univ ×ˢ _root_.Set.Ioo (-(1 / 4 : ℝ)) (1 / 4), isOpen_univ.prod isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.seamDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.seamDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.seamDomain ``Submission.DifferentialGeometry.Topology.DoubleCylinder.seamDomain

def lowerSeam (p : seamDomain) : Space f :=
  if ht : 0 ≤ p.val.2 then
    core f (p.val.1, ⟨p.val.2, ht, by linarith [p.property.2.2]⟩)
  else band f (p.val.1, ⟨-p.val.2, by constructor <;> linarith [not_le.mp ht, p.property.2.1]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.lowerSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.lowerSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.lowerSeam ``Submission.DifferentialGeometry.Topology.DoubleCylinder.lowerSeam

def upperSeam (p : seamDomain) : Space f :=
  if ht : 0 ≤ p.val.2 then
    band f (f p.val.1, ⟨1 - p.val.2, by constructor <;> linarith [p.property.2.2]⟩)
  else core f (p.val.1, ⟨1 + p.val.2, by constructor <;> linarith [not_le.mp ht, p.property.2.1]⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.upperSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.upperSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.upperSeam ``Submission.DifferentialGeometry.Topology.DoubleCylinder.upperSeam

private def halfSeam (p : seamDomain) : sphereMappingTorusSeamDomain :=
  ⟨(p.val.1, p.val.2 / 2), _root_.Set.mem_univ _, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.halfSeam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.halfSeam target :: scope.openDecls } }

private def middleSeam (p : seamDomain) : sphereMappingTorusInteriorDomain :=
  ⟨(p.val.1, (1 + p.val.2) / 2), _root_.Set.mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.middleSeam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.middleSeam target :: scope.openDecls } }

theorem toMappingTorus_lowerSeam (p : seamDomain) :
    toMappingTorus f (lowerSeam f p) = sphereMappingTorusSeam f (halfSeam p) := by
  unfold lowerSeam
  split_ifs with ht
  · change Quotient.mk (sphereMappingTorusSetoid f) (p.val.1, ⟨p.val.2 / 2, _⟩) = _
    rw [sphereMappingTorusSeam, dif_pos (by change 0 ≤ p.val.2 / 2; linarith)]
    rfl
  · change Quotient.mk (sphereMappingTorusSetoid f) (f.symm p.val.1, ⟨1 - -p.val.2 / 2, _⟩) = _
    rw [sphereMappingTorusSeam, dif_neg (by change ¬ 0 ≤ p.val.2 / 2; linarith)]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp [halfSeam]; ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_lowerSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_lowerSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_lowerSeam ``Submission.DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_lowerSeam

theorem toMappingTorus_upperSeam (p : seamDomain) :
    toMappingTorus f (upperSeam f p) = sphereMappingTorusInterior f (middleSeam p) := by
  unfold upperSeam
  split_ifs with ht
  · change Quotient.mk (sphereMappingTorusSetoid f)
      (f.symm (f p.val.1), ⟨1 - (1 - p.val.2) / 2, _⟩) = _
    rw [f.symm_apply_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by dsimp [middleSeam]; ring))
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_upperSeam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_upperSeam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_upperSeam ``Submission.DifferentialGeometry.Topology.DoubleCylinder.toMappingTorus_upperSeam

private def axialAffine (c : ℝ) : Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (p.1, (c + p.2) / 2)
  invFun p := (p.1, 2 * p.2 - c)
  left_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  contMDiff_toFun := contMDiff_fst.prodMk ((contMDiff_const.add contMDiff_snd).div_const 2)
  contMDiff_invFun := contMDiff_fst.prodMk ((contMDiff_const.mul contMDiff_snd).sub contMDiff_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.DoubleCylinder.axialAffine
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.DoubleCylinder.axialAffine target :: scope.openDecls } }

theorem lowerSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
      (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (lowerSeam D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ)
    (mappingTorusHomeomorph D.target)
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open seamDomain
    ((axialAffine 0).isLocalDiffeomorph.isLocalDiffeomorphOn seamDomain)
  have hseam := sphereMappingTorusSeam_isLocalDiffeomorph D
  have hh : IsLocalDiffeomorph IC IC ∞ (halfSeam : seamDomain → sphereMappingTorusSeamDomain) := by
    intro p
    have hx := hloc p
    have hmem : ∀ q : seamDomain, (axialAffine 0) q.val ∈ sphereMappingTorusSeamDomain := by
      intro q
      change (q.val.1, (0 + q.val.2) / 2) ∈ _
      simpa only [halfSeam, zero_add] using (halfSeam q).property
    have h := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem hx
    have heq : (fun y : seamDomain => (⟨(axialAffine 0) y.val, hmem y⟩ : sphereMappingTorusSeamDomain)) =
        halfSeam := by
      funext y
      apply Subtype.ext
      change (y.val.1, (0 + y.val.2) / 2) = (y.val.1, y.val.2 / 2)
      rw [zero_add]
    rw [heq] at h
    exact h
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp hseam hh)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusSeam D.target ∘ halfSeam) = lowerSeam D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    exact (toMappingTorus_lowerSeam D.target p).symm
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.lowerSeam_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.lowerSeam_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.lowerSeam_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.lowerSeam_isLocalDiffeomorph


theorem upperSeam_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (upperSeam D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open seamDomain
    ((axialAffine 1).isLocalDiffeomorph.isLocalDiffeomorphOn seamDomain)
  have hseam := sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
    (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi)
  have hh : IsLocalDiffeomorph IC IC ∞ (middleSeam : seamDomain → sphereMappingTorusInteriorDomain) := by
    intro p
    have hx := hloc p
    have hmem : ∀ q : seamDomain, (axialAffine 1) q.val ∈ sphereMappingTorusInteriorDomain := by
      intro q
      change q.val.1 ∈ _root_.Set.univ ∧ (1 + q.val.2) / 2 ∈ _root_.Set.Ioo (0 : ℝ) 1
      exact (middleSeam q).property
    have h := DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem hx
    have heq : (fun y : seamDomain => (⟨(axialAffine 1) y.val, hmem y⟩ : sphereMappingTorusInteriorDomain)) =
        middleSeam := by
      funext y
      exact Subtype.ext rfl
    rw [heq] at h
    exact h
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp hseam hh)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ middleSeam) = upperSeam D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    exact (toMappingTorus_upperSeam D.target p).symm
  rw [heq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.DoubleCylinder.upperSeam_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.DoubleCylinder.upperSeam_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.DoubleCylinder.upperSeam_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.DoubleCylinder.upperSeam_isLocalDiffeomorph

end DoubleCylinder
end DifferentialGeometry.Topology
