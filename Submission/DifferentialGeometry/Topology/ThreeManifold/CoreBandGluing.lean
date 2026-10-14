import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCoreTubeGluing
import Submission.DifferentialGeometry.Topology.Attachment.Union

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Band" => S2 × _root_.Set.Icc (-1 : ℝ) 1
local notation "Tube" => S2 × _root_.Set.Icc (-2 : ℝ) 2

local instance _root_.Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.instFactLtRealNegOfNat

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

private def bandInclusion (q : Band) : Tube :=
  (q.1, ⟨q.2.val, by constructor <;> linarith [q.2.property.1, q.2.property.2]⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion target :: scope.openDecls } }

private theorem bandInclusion_injective : _root_.Function.Injective bandInclusion := by
  intro q q' h
  exact Prod.ext (congrArg (fun q : Tube => q.1) h)
    (Subtype.ext (congrArg (fun q : Tube => q.2.val) h))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion_injective target :: scope.openDecls } }

private theorem continuous_bandInclusion : Continuous bandInclusion :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.continuous_bandInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.continuous_bandInclusion target :: scope.openDecls } }

private def bandEndLevel (side : Bool) : _root_.Set.Icc (-1 : ℝ) 1 :=
  if side then ⟨1, by norm_num⟩ else ⟨-1, by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.bandEndLevel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.bandEndLevel target :: scope.openDecls } }

private theorem bandInclusion_end (side : Bool) (z : S2) :
    bandInclusion (z, bandEndLevel side) = (z, boundaryLevel side) := by
  cases side <;> rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion_end
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.bandInclusion_end target :: scope.openDecls } }

def coreBandBoundaryInclusion (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → (Σ _a : S, Band) :=
  fun q => ⟨q.1, q.2.2, bandEndLevel q.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandBoundaryInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandBoundaryInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandBoundaryInclusion ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandBoundaryInclusion

def coreBandAttachingMap (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → T.core :=
  fun q => T.coreBoundarySphere (q.1.val, q.2.1) q.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandAttachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandAttachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandAttachingMap ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandAttachingMap

def coreBandMap (S : Finset T.Index) : C((Σ _a : S, Band), M.Carrier) where
  toFun q := T.tube q.1.val (bandInclusion q.2)
  continuous_toFun := continuous_sigma fun a =>
    (T.tube a.val).continuous.comp continuous_bandInclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap

theorem coreBandMap_boundary (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    T.coreBandMap S (T.coreBandBoundaryInclusion S q) = (T.coreBandAttachingMap S q).val := by
  change T.tube q.1.val (bandInclusion (q.2.2, bandEndLevel q.2.1)) = _
  rw [bandInclusion_end]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_boundary ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_boundary

theorem coreBandMap_injective (S : Finset T.Index) : _root_.Function.Injective (T.coreBandMap S) := by
  rintro ⟨a, q⟩ ⟨a', q'⟩ h
  have haa : a = a' := by
    apply Subtype.ext
    by_contra hne
    exact (Set.disjoint_left.mp (T.disjoint hne) (_root_.Set.mem_range_self (bandInclusion q)))
      ⟨bandInclusion q', h.symm⟩
  subst a'
  have hqq : q = q' := bandInclusion_injective ((T.smooth a.val).isEmbedding.injective h)
  cases hqq
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_injective ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_injective

theorem range_coreBandMap (S : Finset T.Index) :
    range (T.coreBandMap S) = ⋃ a ∈ S, T.band a := by
  ext x
  constructor
  · rintro ⟨⟨a, q⟩, rfl⟩
    exact mem_iUnion.mpr ⟨a.val, mem_iUnion.mpr ⟨a.property,
      ⟨bandInclusion q, q.2.property, rfl⟩⟩⟩
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    obtain ⟨haS, q, hq, rfl⟩ := mem_iUnion.mp ha
    refine ⟨⟨⟨a, haS⟩, q.1, ⟨q.2.val, hq⟩⟩, ?_⟩
    apply congrArg (T.tube a)
    exact Prod.ext rfl (Subtype.ext rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.range_coreBandMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.range_coreBandMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.range_coreBandMap ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.range_coreBandMap

theorem coreBandMap_mem_core_iff (S : Finset T.Index) (q : Σ _a : S, Band) :
    T.coreBandMap S q ∈ T.core ↔ q ∈ _root_.Set.range (T.coreBandBoundaryInclusion S) := by
  constructor
  · intro hq
    have hband : -1 ≤ ((bandInclusion q.2).2 : ℝ) ∧
        ((bandInclusion q.2).2 : ℝ) ≤ 1 := q.2.2.property
    rcases T.eq_boundaryLevel_of_mem_band_of_mem_core hband hq with h | h
    · refine ⟨⟨q.1, _root_.Bool.false, q.2.1⟩, ?_⟩
      exact congrArg (fun t : _root_.Set.Icc (-1 : ℝ) 1 =>
        (⟨q.1, q.2.1, t⟩ : Σ _a : S, Band)) (Subtype.ext h.symm)
    · refine ⟨⟨q.1, _root_.Bool.true, q.2.1⟩, ?_⟩
      exact congrArg (fun t : _root_.Set.Icc (-1 : ℝ) 1 =>
        (⟨q.1, q.2.1, t⟩ : Σ _a : S, Band)) (Subtype.ext h.symm)
  · rintro ⟨b, rfl⟩
    rw [T.coreBandMap_boundary]
    exact (T.coreBandAttachingMap S b).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_mem_core_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_mem_core_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_mem_core_iff ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandMap_mem_core_iff

abbrev CoreBandGluing (S : Finset T.Index) :=
  AdjunctionSpace (T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.CoreBandGluing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.CoreBandGluing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.CoreBandGluing ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.CoreBandGluing

noncomputable def coreBandHomeomorph (S : Finset T.Index) :
    T.CoreBandGluing S ≃ₜ (T.core ∪ ⋃ a ∈ S, T.band a : Set M.Carrier) :=
  (adjunctionHomeomorphUnionImage (T.coreBandBoundaryInclusion S)
    (T.coreBandAttachingMap S) (T.coreBandMap S)
    (fun q => (T.coreBandMap_boundary S q).symm)
    (T.coreBandMap_injective S) (T.coreBandMap S).continuous
    (fun q hq => (T.coreBandMap_mem_core_iff S q).mp hq)
    (isOpen_iUnion T.removedBand_isOpen).isClosed_compl).trans
    (Homeomorph.setCongr (by rw [T.range_coreBandMap]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph

theorem coreBandHomeomorph_core (S : Finset T.Index) (x : T.core) :
    (T.coreBandHomeomorph S (adjunctionLower (i := T.coreBandBoundaryInclusion S)
      (T.coreBandAttachingMap S) x)).val = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_core ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_core

theorem coreBandHomeomorph_band (S : Finset T.Index) (q : Σ _a : S, Band) :
    (T.coreBandHomeomorph S (adjunctionCell (T.coreBandBoundaryInclusion S)
      (T.coreBandAttachingMap S) q)).val = T.coreBandMap S q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_band ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorph_band

theorem coreBandGluing_seam (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    adjunctionCell (T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)
        (T.coreBandBoundaryInclusion S q) =
      adjunctionLower (i := T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)
        (T.coreBandAttachingMap S q) :=
  adjunction_coherence _ _ q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam

theorem coreBandGluing_seam_insert [DecidableEq T.Index] (S : Finset T.Index)
    (e a : T.Index) (ha : a ∈ S) (b : Bool) (z : S2) :
    adjunctionCell (T.coreBandBoundaryInclusion (_root_.Insert.insert e S))
        (T.coreBandAttachingMap (_root_.Insert.insert e S))
        (T.coreBandBoundaryInclusion (_root_.Insert.insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩) =
      adjunctionLower (i := T.coreBandBoundaryInclusion (_root_.Insert.insert e S))
        (T.coreBandAttachingMap (_root_.Insert.insert e S))
        (T.coreBoundarySphere (a, b) z) :=
  T.coreBandGluing_seam (_root_.Insert.insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam_insert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam_insert ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandGluing_seam_insert

noncomputable def coreBandHomeomorphSource : T.CoreBandGluing Finset.univ ≃ₜ M.Carrier :=
  (T.coreBandHomeomorph Finset.univ).trans
    ((Homeomorph.setCongr (by simpa only [Set.iUnion_true, Finset.mem_univ, bandRange] using T.core_union_bandRange)).trans
      (Homeomorph.Set.univ M.Carrier))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource

theorem coreBandHomeomorphSource_core (x : T.core) :
    T.coreBandHomeomorphSource (adjunctionLower (i := T.coreBandBoundaryInclusion Finset.univ)
      (T.coreBandAttachingMap Finset.univ) x) = x.val :=
  T.coreBandHomeomorph_core Finset.univ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_core ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_core

theorem coreBandHomeomorphSource_band (q : Σ _a : (Finset.univ : Finset T.Index), Band) :
    T.coreBandHomeomorphSource (adjunctionCell (T.coreBandBoundaryInclusion Finset.univ)
      (T.coreBandAttachingMap Finset.univ) q) = T.coreBandMap Finset.univ q :=
  T.coreBandHomeomorph_band Finset.univ q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_band ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.coreBandHomeomorphSource_band

end DifferentialGeometry.Topology.SphericalTubeSystem
