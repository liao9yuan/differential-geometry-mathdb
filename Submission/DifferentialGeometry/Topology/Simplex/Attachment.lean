import Submission.DifferentialGeometry.Topology.Category.TopCat.PushoutClosedEmbedding
import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.CompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology

universe u

namespace DifferentialGeometry.Simplex.Attachment

variable {I : Type u} [Fintype I] [Nonempty I]


def boundaryι : TopCat.of (boundary I) ⟶ TopCat.of (stdSimplex ℝ I) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.boundaryι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.boundaryι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.boundaryι ``Submission.DifferentialGeometry.Simplex.Attachment.boundaryι

omit [Nonempty I] in
theorem isClosedEmbedding_boundaryι : _root_.Topology.IsClosedEmbedding (boundaryι (I := I)) :=
  isClosed_boundary.isClosedEmbedding_subtypeVal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι ``Submission.DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι

variable {X P : TopCat.{u}} {g : TopCat.of (boundary I) ⟶ X}
  {r : TopCat.of (stdSimplex ℝ I) ⟶ P} {b : X ⟶ P}
  (h : IsPushout boundaryι g r b)


def puncturedNeighborhood : Set P := {p | p ≠ r stdSimplex.barycenter}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.puncturedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.puncturedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.puncturedNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.puncturedNeighborhood

include h


theorem inl_eq_barycenter_iff (d : stdSimplex ℝ I) :
    r d = r stdSimplex.barycenter ↔ d = stdSimplex.barycenter := by
  constructor
  · intro hd
    rcases (DifferentialGeometry.TopCat.Pushout.inl_eq_inl_iff h Subtype.val_injective
      d stdSimplex.barycenter).mp hd with hd | ⟨_, a, _, _, ha⟩
    · exact hd
    · exact (boundary_ne_barycenter a.property ha.symm).elim
  · rintro rfl
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.inl_eq_barycenter_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.inl_eq_barycenter_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.inl_eq_barycenter_iff ``Submission.DifferentialGeometry.Simplex.Attachment.inl_eq_barycenter_iff


theorem inr_ne_barycenter (x : X) : b x ≠ r stdSimplex.barycenter := by
  intro hx
  obtain ⟨a, ha, _⟩ := (DifferentialGeometry.TopCat.Pushout.inl_eq_inr_iff h Subtype.val_injective
    stdSimplex.barycenter x).mp hx.symm
  exact boundary_ne_barycenter a.property ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.inr_ne_barycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.inr_ne_barycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.inr_ne_barycenter ``Submission.DifferentialGeometry.Simplex.Attachment.inr_ne_barycenter


theorem preimage_inl_puncturedNeighborhood :
    r ⁻¹' puncturedNeighborhood (r := r) = punctured I := by
  ext d
  exact not_congr (inl_eq_barycenter_iff h d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.preimage_inl_puncturedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.preimage_inl_puncturedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.preimage_inl_puncturedNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.preimage_inl_puncturedNeighborhood


theorem preimage_inr_puncturedNeighborhood :
    b ⁻¹' puncturedNeighborhood (r := r) = Set.univ :=
  Set.eq_univ_of_forall (inr_ne_barycenter h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.preimage_inr_puncturedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.preimage_inr_puncturedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.preimage_inr_puncturedNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.preimage_inr_puncturedNeighborhood


theorem isOpen_puncturedNeighborhood : IsOpen (puncturedNeighborhood (r := r)) := by
  rw [DifferentialGeometry.TopCat.Pushout.isOpen_iff_preimages h,
    preimage_inl_puncturedNeighborhood h, preimage_inr_puncturedNeighborhood h]
  exact ⟨isOpen_punctured, isOpen_univ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.isOpen_puncturedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.isOpen_puncturedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.isOpen_puncturedNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.isOpen_puncturedNeighborhood


def cellToNeighborhood : C(punctured I, puncturedNeighborhood (r := r)) :=
  ⟨fun d ↦ ⟨r d.val, fun hd ↦ d.property ((inl_eq_barycenter_iff h d.val).mp hd)⟩,
    (r.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellToNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellToNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellToNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.cellToNeighborhood


def oldToNeighborhood : C(X, puncturedNeighborhood (r := r)) :=
  ⟨fun x ↦ ⟨b x, inr_ne_barycenter h x⟩, b.hom.continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.oldToNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.oldToNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.oldToNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.oldToNeighborhood

theorem isClosedEmbedding_oldToNeighborhood : _root_.Topology.IsClosedEmbedding (oldToNeighborhood h) := by
  have hb := DifferentialGeometry.TopCat.Pushout.isClosedEmbedding_inr h isClosedEmbedding_boundaryι
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap (oldToNeighborhood h).continuous
    (fun x y hxy ↦ hb.injective (congrArg Subtype.val hxy))
    (hb.isClosedMap.subtype_mk (inr_ne_barycenter h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_oldToNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_oldToNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_oldToNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_oldToNeighborhood

theorem range_oldToNeighborhood :
    Set.range (oldToNeighborhood h) =
      {p : puncturedNeighborhood (r := r) | p.val ∈ Set.range b} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.range_oldToNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.range_oldToNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.range_oldToNeighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.range_oldToNeighborhood


def neighborhoodQuotient : C(punctured I ⊕ X, puncturedNeighborhood (r := r)) :=
  ⟨Sum.elim (cellToNeighborhood h) (oldToNeighborhood h),
    (cellToNeighborhood h).continuous.sumElim (oldToNeighborhood h).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodQuotient ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodQuotient


theorem cellToNeighborhood_boundary (a : boundary I) :
    cellToNeighborhood h (boundaryInclusion a) = oldToNeighborhood h (g a) := by
  apply Subtype.ext
  change r a.val = b (g a)
  exact ConcreteCategory.congr_hom h.w a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellToNeighborhood_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellToNeighborhood_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellToNeighborhood_boundary ``Submission.DifferentialGeometry.Simplex.Attachment.cellToNeighborhood_boundary


theorem isQuotientMap_neighborhoodQuotient : _root_.Topology.IsQuotientMap (neighborhoodQuotient h) := by
  refine ⟨?_, ?_⟩
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro s
    constructor
    · intro hs
      have hparts := isOpen_sum_iff.mp hs
      apply (isOpen_puncturedNeighborhood h).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mpr
      apply (DifferentialGeometry.TopCat.Pushout.isOpen_iff_preimages h _).mpr
      constructor
      · have heq : r ⁻¹' (Subtype.val '' s) =
            Subtype.val '' ((cellToNeighborhood h) ⁻¹' s) := by
          ext d
          constructor
          · rintro ⟨p, hp, hpd⟩
            have hd : d ∈ punctured I := by
              intro he
              exact p.property (hpd.trans (congrArg r he))
            refine ⟨⟨d, hd⟩, ?_, rfl⟩
            have he : cellToNeighborhood h ⟨d, hd⟩ = p := Subtype.ext hpd.symm
            exact show cellToNeighborhood h ⟨d, hd⟩ ∈ s from he.symm ▸ hp
          · rintro ⟨d, hd, rfl⟩
            exact ⟨cellToNeighborhood h d, hd, rfl⟩
        rw [heq]
        exact isOpen_punctured.isOpenMap_subtype_val _ hparts.1
      · have heq : b ⁻¹' (Subtype.val '' s) = (oldToNeighborhood h) ⁻¹' s := by
          ext x
          constructor
          · rintro ⟨p, hp, hpx⟩
            have he : oldToNeighborhood h x = p := Subtype.ext hpx.symm
            exact show oldToNeighborhood h x ∈ s from he.symm ▸ hp
          · intro hx
            exact ⟨oldToNeighborhood h x, hx, rfl⟩
        rw [heq]
        exact hparts.2
    · exact fun hs ↦ hs.preimage (neighborhoodQuotient h).continuous
  · intro p
    rcases DifferentialGeometry.TopCat.Pushout.jointly_surjective h p.val with ⟨d, hd⟩ | ⟨x, hx⟩
    · have hdc : d ∈ punctured I := by
        intro he
        exact p.property (hd.symm.trans (congrArg r he))
      exact ⟨Sum.inl ⟨d, hdc⟩, Subtype.ext hd⟩
    · exact ⟨Sum.inr x, Subtype.ext hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.isQuotientMap_neighborhoodQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.isQuotientMap_neighborhoodQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.isQuotientMap_neighborhoodQuotient ``Submission.DifferentialGeometry.Simplex.Attachment.isQuotientMap_neighborhoodQuotient

private def retractionOnSum : C(punctured I ⊕ X, X) :=
  ⟨Sum.elim (fun d ↦ g (radialRetraction d)) id,
    (g.hom.continuous.comp radialRetraction.continuous).sumElim continuous_id⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.retractionOnSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.retractionOnSum target :: scope.openDecls } }

omit h in
private theorem retractionOnSum_boundary (a : boundary I) :
    retractionOnSum (g := g) (Sum.inl (boundaryInclusion a)) = g a := by
  change g (radialRetraction (boundaryInclusion a)) = g a
  rw [radialRetraction_boundary]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.retractionOnSum_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.retractionOnSum_boundary target :: scope.openDecls } }

private theorem retractionOnSum_fiber (z z' : punctured I ⊕ X)
    (hz : neighborhoodQuotient h z = neighborhoodQuotient h z') :
    retractionOnSum (g := g) z = retractionOnSum (g := g) z' := by
  have he := congrArg Subtype.val hz
  rcases z with d | x <;> rcases z' with e | y
  · rcases (DifferentialGeometry.TopCat.Pushout.inl_eq_inl_iff h Subtype.val_injective d.val e.val).mp he
      with hde | ⟨a, a', haa', ha, ha'⟩
    · exact congrArg (fun d ↦ retractionOnSum (g := g) (Sum.inl d)) (Subtype.ext hde)
    · have hd : d = boundaryInclusion a := Subtype.ext ha
      have he : e = boundaryInclusion a' := Subtype.ext ha'
      rw [hd, he, retractionOnSum_boundary, retractionOnSum_boundary]
      exact haa'
  · obtain ⟨a, ha, hax⟩ :=
      (DifferentialGeometry.TopCat.Pushout.inl_eq_inr_iff h Subtype.val_injective d.val y).mp he
    have hd : d = boundaryInclusion a := Subtype.ext ha.symm
    rw [hd, retractionOnSum_boundary]
    exact hax
  · obtain ⟨a, ha, hax⟩ :=
      (DifferentialGeometry.TopCat.Pushout.inl_eq_inr_iff h Subtype.val_injective e.val x).mp he.symm
    have he : e = boundaryInclusion a := Subtype.ext ha.symm
    rw [he, retractionOnSum_boundary]
    exact hax.symm
  · exact DifferentialGeometry.TopCat.Pushout.injective_inr h Subtype.val_injective he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.retractionOnSum_fiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.retractionOnSum_fiber target :: scope.openDecls } }

private def neighborhoodRetractionPoint (p : puncturedNeighborhood (r := r)) : X :=
  retractionOnSum (g := g)
    (Function.surjInv (isQuotientMap_neighborhoodQuotient h).surjective p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRetractionPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.neighborhoodRetractionPoint target :: scope.openDecls } }

private theorem neighborhoodRetractionPoint_quotient (z : punctured I ⊕ X) :
    neighborhoodRetractionPoint h (neighborhoodQuotient h z) = retractionOnSum (g := g) z :=
  retractionOnSum_fiber h _ _ (Function.surjInv_eq _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRetractionPoint_quotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.neighborhoodRetractionPoint_quotient target :: scope.openDecls } }

def neighborhoodRetraction : C(puncturedNeighborhood (r := r), X) :=
  ⟨neighborhoodRetractionPoint h, by
    apply (isQuotientMap_neighborhoodQuotient h).continuous_iff.mpr
    have he : neighborhoodRetractionPoint h ∘ neighborhoodQuotient h =
        retractionOnSum (g := g) := funext (neighborhoodRetractionPoint_quotient h)
    rw [he]
    exact (retractionOnSum (g := g)).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction

theorem neighborhoodRetraction_cell (d : punctured I) :
    neighborhoodRetraction h (cellToNeighborhood h d) = g (radialRetraction d) :=
  neighborhoodRetractionPoint_quotient h (Sum.inl d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_cell ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_cell


@[simp]
theorem neighborhoodRetraction_old (x : X) :
    neighborhoodRetraction h (oldToNeighborhood h x) = x :=
  neighborhoodRetractionPoint_quotient h (Sum.inr x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_old ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRetraction_old

private def deformationOnSum :
    C(unitInterval × (punctured I ⊕ X), puncturedNeighborhood (r := r)) :=
  ⟨fun tz ↦ Sum.elim
    (fun d ↦ cellToNeighborhood h (radialDeformation (tz.1, d)))
    (oldToNeighborhood h) tz.2, by
    have hc := ((cellToNeighborhood h).continuous.comp
      (radialDeformation (I := I)).continuous).sumElim ((oldToNeighborhood h).continuous.comp
        (continuous_snd : Continuous (Prod.snd : unitInterval × X → X)))
    convert hc.comp (Homeomorph.prodSumDistrib
      (X := unitInterval) (Y := punctured I) (Z := X)).continuous using 1
    funext tz
    rcases tz with ⟨t, d | x⟩ <;> rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.deformationOnSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.deformationOnSum target :: scope.openDecls } }

private theorem deformationOnSum_boundary (t : unitInterval) (a : boundary I) :
    deformationOnSum h (t, Sum.inl (boundaryInclusion a)) = oldToNeighborhood h (g a) := by
  change cellToNeighborhood h (radialDeformation (t, boundaryInclusion a)) = _
  have ha : radialDeformation (t, boundaryInclusion a) = boundaryInclusion a :=
    (radialDeformation (I := I)).prop' t (boundaryInclusion a) a.property
  rw [ha]
  exact cellToNeighborhood_boundary h a

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.deformationOnSum_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.deformationOnSum_boundary target :: scope.openDecls } }

private theorem deformationOnSum_fiber (t : unitInterval) (z z' : punctured I ⊕ X)
    (hz : neighborhoodQuotient h z = neighborhoodQuotient h z') :
    deformationOnSum h (t, z) = deformationOnSum h (t, z') := by
  have he := congrArg Subtype.val hz
  rcases z with d | x <;> rcases z' with e | y
  · rcases (DifferentialGeometry.TopCat.Pushout.inl_eq_inl_iff h Subtype.val_injective d.val e.val).mp he
      with hde | ⟨a, a', haa', ha, ha'⟩
    · exact congrArg (fun d ↦ deformationOnSum h (t, Sum.inl d)) (Subtype.ext hde)
    · have hd : d = boundaryInclusion a := Subtype.ext ha
      have he : e = boundaryInclusion a' := Subtype.ext ha'
      rw [hd, he, deformationOnSum_boundary, deformationOnSum_boundary, haa']
  · obtain ⟨a, ha, hax⟩ :=
      (DifferentialGeometry.TopCat.Pushout.inl_eq_inr_iff h Subtype.val_injective d.val y).mp he
    have hd : d = boundaryInclusion a := Subtype.ext ha.symm
    rw [hd, deformationOnSum_boundary, hax]
    rfl
  · obtain ⟨a, ha, hax⟩ :=
      (DifferentialGeometry.TopCat.Pushout.inl_eq_inr_iff h Subtype.val_injective e.val x).mp he.symm
    have he : e = boundaryInclusion a := Subtype.ext ha.symm
    rw [he, deformationOnSum_boundary, hax]
    rfl
  · exact hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.deformationOnSum_fiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.deformationOnSum_fiber target :: scope.openDecls } }

private def neighborhoodDeformationPoint
    (tp : unitInterval × puncturedNeighborhood (r := r)) : puncturedNeighborhood (r := r) :=
  deformationOnSum h (tp.1,
    Function.surjInv (isQuotientMap_neighborhoodQuotient h).surjective tp.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodDeformationPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformationPoint target :: scope.openDecls } }

private theorem neighborhoodDeformationPoint_quotient (t : unitInterval) (z : punctured I ⊕ X) :
    neighborhoodDeformationPoint h (t, neighborhoodQuotient h z) = deformationOnSum h (t, z) :=
  deformationOnSum_fiber h t _ _ (Function.surjInv_eq _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodDeformationPoint_quotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformationPoint_quotient target :: scope.openDecls } }

def neighborhoodDeformation : ContinuousMap.HomotopyRel
    (ContinuousMap.id (puncturedNeighborhood (r := r)))
    ((oldToNeighborhood h).comp (neighborhoodRetraction h)) (Set.range (oldToNeighborhood h)) where
  toFun := neighborhoodDeformationPoint h
  continuous_toFun := by
    apply (isQuotientMap_neighborhoodQuotient h).continuous_lift_prod_right
    have he : (fun tz : unitInterval × (punctured I ⊕ X) ↦
        neighborhoodDeformationPoint h (tz.1, neighborhoodQuotient h tz.2)) =
          deformationOnSum h :=
      funext (fun tz ↦ neighborhoodDeformationPoint_quotient h tz.1 tz.2)
    rw [he]
    exact (deformationOnSum h).continuous
  map_zero_left p := by
    obtain ⟨z, rfl⟩ := (isQuotientMap_neighborhoodQuotient h).surjective p
    rw [neighborhoodDeformationPoint_quotient]
    rcases z with d | x
    · exact congrArg (cellToNeighborhood h) ((radialDeformation (I := I)).map_zero_left d)
    · rfl
  map_one_left p := by
    obtain ⟨z, rfl⟩ := (isQuotientMap_neighborhoodQuotient h).surjective p
    rw [neighborhoodDeformationPoint_quotient]
    rcases z with d | x
    · change cellToNeighborhood h (radialDeformation (1, d)) =
        oldToNeighborhood h (neighborhoodRetraction h (cellToNeighborhood h d))
      rw [neighborhoodRetraction_cell]
      exact (congrArg (cellToNeighborhood h) ((radialDeformation (I := I)).map_one_left d)).trans
        (cellToNeighborhood_boundary h (radialRetraction d))
    · change oldToNeighborhood h x =
        oldToNeighborhood h (neighborhoodRetraction h (oldToNeighborhood h x))
      rw [neighborhoodRetraction_old]
  prop' t := by
    rintro p ⟨x, rfl⟩
    exact neighborhoodDeformationPoint_quotient h t (Sum.inr x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation

theorem neighborhoodDeformation_cell (t : unitInterval) (d : punctured I) :
    neighborhoodDeformation h (t, cellToNeighborhood h d) =
      cellToNeighborhood h (radialDeformation (t, d)) :=
  neighborhoodDeformationPoint_quotient h t (Sum.inl d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_cell ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_cell


@[simp]
theorem neighborhoodDeformation_old (t : unitInterval) (x : X) :
    neighborhoodDeformation h (t, oldToNeighborhood h x) = oldToNeighborhood h x :=
  neighborhoodDeformationPoint_quotient h t (Sum.inr x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_old ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodDeformation_old

def neighborhoodHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (puncturedNeighborhood (r := r)) X where
  toFun := neighborhoodRetraction h
  invFun := oldToNeighborhood h
  left_inv := ⟨(neighborhoodDeformation h).toHomotopy.symm⟩
  right_inv := by
    have he : (neighborhoodRetraction h).comp (oldToNeighborhood h) = ContinuousMap.id X := by
      apply ContinuousMap.ext
      intro x
      exact neighborhoodRetraction_old h x
    rw [he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodHomotopyEquiv ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodHomotopyEquiv

end DifferentialGeometry.Simplex.Attachment
