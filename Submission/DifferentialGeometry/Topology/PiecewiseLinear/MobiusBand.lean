import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OrientationParity
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def mobiusVertex (i : Fin 5) : Fin 5 → ℝ := Pi.single i (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex

theorem mobiusVertex_injective : Function.Injective mobiusVertex := stdVertex_injective 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_injective

def mobiusTriIdx (i : Fin 5) : Finset (Fin 5) := {i, i + 1, i + 2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx

def mobiusEdgeIdx (i : Fin 5) : Finset (Fin 5) := {i + 1, i + 2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx

noncomputable def mobiusTri (i : Fin 5) : Finset (Fin 5 → ℝ) :=
  (mobiusTriIdx i).image mobiusVertex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri

noncomputable def mobiusEdge (i : Fin 5) : Finset (Fin 5 → ℝ) :=
  (mobiusEdgeIdx i).image mobiusVertex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge

theorem mobiusTriIdx_card (i : Fin 5) : (mobiusTriIdx i).card = 3 := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_card

theorem mobiusEdgeIdx_card (i : Fin 5) : (mobiusEdgeIdx i).card = 2 := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_card

theorem mobiusTri_card (i : Fin 5) : (mobiusTri i).card = 3 := by
  rw [mobiusTri, Finset.card_image_of_injective _ mobiusVertex_injective, mobiusTriIdx_card]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_card

theorem mobiusEdge_card (i : Fin 5) : (mobiusEdge i).card = 2 := by
  rw [mobiusEdge, Finset.card_image_of_injective _ mobiusVertex_injective, mobiusEdgeIdx_card]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_card

theorem mobiusTri_nonempty (i : Fin 5) : (mobiusTri i).Nonempty :=
  Finset.card_pos.mp (by rw [mobiusTri_card]; norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_nonempty

theorem mobiusTri_subset_stdVertices (i : Fin 5) : mobiusTri i ⊆ stdVertices 3 := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_subset_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_subset_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_subset_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_subset_stdVertices

noncomputable def mobiusComplex : Geometry.SimplicialComplex ℝ (Fin 5 → ℝ) where
  faces := {s | s.Nonempty ∧ ∃ i, s ⊆ mobiusTri i}
  isRelLowerSet_faces := by
    rintro s ⟨hne, i, hsi⟩
    exact ⟨hne, fun t hts ht => ⟨ht, i, hts.trans hsi⟩⟩
  indep hs := affineIndependent_of_subset (stdVertices_affineIndependent 3)
    (hs.2.choose_spec.trans (mobiusTri_subset_stdVertices _))
  inter_subset_convexHull hs ht := convexHull_inter_subset_of_affineIndependent
    (stdVertices_affineIndependent 3)
    (hs.2.choose_spec.trans (mobiusTri_subset_stdVertices _))
    (ht.2.choose_spec.trans (mobiusTri_subset_stdVertices _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex

theorem mem_mobiusComplex_faces_iff {s : Finset (Fin 5 → ℝ)} :
    s ∈ mobiusComplex.faces ↔ s.Nonempty ∧ ∃ i, s ⊆ mobiusTri i := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusComplex_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusComplex_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusComplex_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusComplex_faces_iff

theorem mobiusTri_mem_faces (i : Fin 5) : mobiusTri i ∈ mobiusComplex.faces :=
  ⟨mobiusTri_nonempty i, i, Finset.Subset.rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_mem_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_mem_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_mem_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_mem_faces

theorem mobiusComplex_faces_finite : mobiusComplex.faces.Finite :=
  (Set.toFinite ((stdVertices 3).powerset : Set (Finset (Fin 5 → ℝ)))).subset fun _ hs =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr
      (hs.2.choose_spec.trans (mobiusTri_subset_stdVertices _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusComplex_faces_finite

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetForallFinOfNatNatRealFacesMobiusComplex : Finite mobiusComplex.faces := mobiusComplex_faces_finite.to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetForallFinOfNatNatRealFacesMobiusComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetForallFinOfNatNatRealFacesMobiusComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetForallFinOfNatNatRealFacesMobiusComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetForallFinOfNatNatRealFacesMobiusComplex

theorem facesOfCard_mobiusComplex_three :
    SimplicialComplex.facesOfCard mobiusComplex.toPreAbstractSimplicialComplex 3 =
      Finset.image mobiusTri Finset.univ := by
  ext s
  rw [SimplicialComplex.mem_facesOfCard, Finset.mem_image]
  constructor
  · rintro ⟨⟨-, i, hsi⟩, hcard⟩
    exact ⟨i, Finset.mem_univ i,
      (Finset.eq_of_subset_of_card_le hsi (by rw [hcard, mobiusTri_card])).symm⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨mobiusTri_mem_faces i, mobiusTri_card i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.facesOfCard_mobiusComplex_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.facesOfCard_mobiusComplex_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.facesOfCard_mobiusComplex_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.facesOfCard_mobiusComplex_three

theorem mem_mobiusTriIdx_self (i : Fin 5) : i ∈ mobiusTriIdx i := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_self

theorem mem_mobiusTriIdx_succ (i : Fin 5) : i + 3 ∈ mobiusTriIdx (i + 1) := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusTriIdx_succ

theorem mobiusTriIdx_erase_self (i : Fin 5) : (mobiusTriIdx i).erase i = mobiusEdgeIdx i := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_self

theorem mobiusTriIdx_erase_succ (i : Fin 5) :
    (mobiusTriIdx (i + 1)).erase (i + 3) = mobiusEdgeIdx i := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_succ

theorem mobiusTriIdx_erase_ne (i j v : Fin 5) (hj : j ≠ i) (hj' : j ≠ i + 1) :
    (mobiusTriIdx j).erase v ≠ mobiusEdgeIdx i := by
  revert i j v
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_ne ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_erase_ne

theorem mobiusEdgeIdx_subset (i : Fin 5) : mobiusEdgeIdx i ⊆ mobiusTriIdx i := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset

theorem mobiusVertex_mem_mobiusTri {i v : Fin 5} (hv : v ∈ mobiusTriIdx i) :
    mobiusVertex v ∈ mobiusTri i := Finset.mem_image.mpr ⟨v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_mem_mobiusTri then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_mem_mobiusTri"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_mem_mobiusTri ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_mem_mobiusTri

theorem mem_erase_mobiusTri (d : DecidableEq (Fin 5 → ℝ)) (i v : Fin 5) (x : Fin 5 → ℝ) :
    x ∈ @Finset.erase _ d (mobiusTri i) (mobiusVertex v) ↔
      ∃ w ∈ (mobiusTriIdx i).erase v, x = mobiusVertex w := by
  simp only [Finset.mem_erase, mobiusTri, Finset.mem_image]
  constructor
  · rintro ⟨hne, w, hw, rfl⟩
    exact ⟨w, ⟨fun h => hne (congrArg mobiusVertex h), hw⟩, rfl⟩
  · rintro ⟨w, ⟨hwv, hwi⟩, rfl⟩
    exact ⟨fun h => hwv (mobiusVertex_injective h), w, hwi, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_erase_mobiusTri then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_erase_mobiusTri"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_erase_mobiusTri ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_erase_mobiusTri

theorem mem_mobiusEdge (i : Fin 5) (x : Fin 5 → ℝ) :
    x ∈ mobiusEdge i ↔ ∃ w ∈ mobiusEdgeIdx i, x = mobiusVertex w := by
  simp only [mobiusEdge, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusEdge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusEdge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusEdge ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_mobiusEdge

theorem erase_mobiusTri_eq_mobiusEdge_iff (d : DecidableEq (Fin 5 → ℝ)) (i j v : Fin 5) :
    @Finset.erase _ d (mobiusTri j) (mobiusVertex v) = mobiusEdge i ↔
      (mobiusTriIdx j).erase v = mobiusEdgeIdx i := by
  rw [Finset.ext_iff, Finset.ext_iff]
  constructor
  · intro h w
    have hw := h (mobiusVertex w)
    rw [mem_erase_mobiusTri, mem_mobiusEdge] at hw
    constructor
    · intro hmem
      obtain ⟨w', hw', he⟩ := hw.mp ⟨w, hmem, rfl⟩
      rwa [mobiusVertex_injective he]
    · intro hmem
      obtain ⟨w', hw', he⟩ := hw.mpr ⟨w, hmem, rfl⟩
      rwa [mobiusVertex_injective he]
  · intro h x
    rw [mem_erase_mobiusTri, mem_mobiusEdge]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (h w).mp hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (h w).mpr hw, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.erase_mobiusTri_eq_mobiusEdge_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.erase_mobiusTri_eq_mobiusEdge_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.erase_mobiusTri_eq_mobiusEdge_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.erase_mobiusTri_eq_mobiusEdge_iff

theorem mobiusEdge_subset (i : Fin 5) : mobiusEdge i ⊆ mobiusTri i :=
  Finset.image_subset_image (mobiusEdgeIdx_subset i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset

theorem mobiusEdge_mem_faces (i : Fin 5) : mobiusEdge i ∈ mobiusComplex.faces :=
  ⟨Finset.card_pos.mp (by rw [mobiusEdge_card]; norm_num), i, mobiusEdge_subset i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_mem_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_mem_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_mem_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_mem_faces

theorem coef_mobius_self (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) :
    simplexBoundaryCoefficient r (mobiusTri i) (mobiusEdge i) =
      incidenceSign r (mobiusTri i) (mobiusVertex i) := by
  have herase : @Finset.erase _ r.toDecidableEq (mobiusTri i) (mobiusVertex i) = mobiusEdge i :=
    (erase_mobiusTri_eq_mobiusEdge_iff _ i i i).mpr (mobiusTriIdx_erase_self i)
  rw [← herase, simplexBoundaryCoefficient_erase r
    (mobiusVertex_mem_mobiusTri (mem_mobiusTriIdx_self i))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_self

theorem coef_mobius_succ (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) :
    simplexBoundaryCoefficient r (mobiusTri (i + 1)) (mobiusEdge i) =
      incidenceSign r (mobiusTri (i + 1)) (mobiusVertex (i + 3)) := by
  have herase : @Finset.erase _ r.toDecidableEq (mobiusTri (i + 1)) (mobiusVertex (i + 3)) =
      mobiusEdge i :=
    (erase_mobiusTri_eq_mobiusEdge_iff _ i (i + 1) (i + 3)).mpr (mobiusTriIdx_erase_succ i)
  rw [← herase, simplexBoundaryCoefficient_erase r
    (mobiusVertex_mem_mobiusTri (mem_mobiusTriIdx_succ i))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_succ

theorem coef_mobius_zero (r : LinearOrder (Fin 5 → ℝ)) {i j : Fin 5} (hj : j ≠ i)
    (hj' : j ≠ i + 1) : simplexBoundaryCoefficient r (mobiusTri j) (mobiusEdge i) = 0 := by
  rw [simplexBoundaryCoefficient]
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact if_neg fun h =>
    mobiusTriIdx_erase_ne i j v hj hj' ((erase_mobiusTri_eq_mobiusEdge_iff _ i j v).mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.coef_mobius_zero

theorem fin5_ne_succ : ∀ i : Fin 5, i ≠ i + 1 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_succ

theorem fin5_ne_add_two : ∀ i : Fin 5, i ≠ i + 2 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_ne_add_two

theorem fin5_succ_ne_add_two : ∀ i : Fin 5, i + 1 ≠ i + 2 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_ne_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_ne_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_ne_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_ne_add_two

theorem fin5_succ_succ : ∀ i : Fin 5, i + 1 + 1 = i + 2 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_succ

theorem fin5_succ_add_two : ∀ i : Fin 5, i + 1 + 2 = i + 3 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_succ_add_two

theorem mobiusTriIdx_inj : ∀ i j : Fin 5, mobiusTriIdx i = mobiusTriIdx j → i = j := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_inj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_inj ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTriIdx_inj

theorem mobiusTri_injective : Function.Injective mobiusTri := fun i j h =>
  mobiusTriIdx_inj i j (Finset.image_injective mobiusVertex_injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_injective

theorem mobiusVertex_ne {a b : Fin 5} (hab : a ≠ b) : mobiusVertex a ≠ mobiusVertex b :=
  fun h => hab (mobiusVertex_injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_ne ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusVertex_ne

theorem mobiusEdgeIdx_subset_succ (i : Fin 5) : mobiusEdgeIdx i ⊆ mobiusTriIdx (i + 1) := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdgeIdx_subset_succ

theorem mobiusEdge_subset_succ (i : Fin 5) : mobiusEdge i ⊆ mobiusTri (i + 1) :=
  Finset.image_subset_image (mobiusEdgeIdx_subset_succ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusEdge_subset_succ

theorem mobiusTri_eq_triple (i : Fin 5) :
    mobiusTri i = {mobiusVertex i, mobiusVertex (i + 1), mobiusVertex (i + 2)} := by
  rw [mobiusTri, mobiusTriIdx, Finset.image_insert, Finset.image_insert, Finset.image_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_eq_triple then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_eq_triple"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_eq_triple ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_eq_triple

theorem mobiusTri_ne_succ (i : Fin 5) : mobiusTri i ≠ mobiusTri (i + 1) :=
  fun h => fin5_ne_succ i (mobiusTri_injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_ne_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_ne_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_ne_succ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusTri_ne_succ

theorem fin5_notMem_pair : ∀ i : Fin 5, i ∉ ({i + 1, i + 2} : Finset (Fin 5)) := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_pair

theorem fin5_notMem_singleton : ∀ i : Fin 5, i + 1 ∉ ({i + 2} : Finset (Fin 5)) := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fin5_notMem_singleton

theorem mobius_incidence_product (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) :
    incidenceSign r (mobiusTri i) (mobiusVertex i) *
          incidenceSign r (mobiusTri i) (mobiusVertex (i + 1)) *
        incidenceSign r (mobiusTri i) (mobiusVertex (i + 2)) = -1 := by
  have hprod := prod_incidenceSign r (mobiusTri i)
  rw [mobiusTri_card] at hprod
  have himg : ∏ v ∈ mobiusTri i, incidenceSign r (mobiusTri i) v =
      ∏ w ∈ mobiusTriIdx i, incidenceSign r (mobiusTri i) (mobiusVertex w) :=
    Finset.prod_image fun a _ b _ h => mobiusVertex_injective h
  rw [himg, mobiusTriIdx, Finset.prod_insert (fin5_notMem_pair i),
    Finset.prod_insert (fin5_notMem_singleton i), Finset.prod_singleton] at hprod
  have h3 : (-1 : ℤ) ^ Nat.choose 3 2 = -1 := by norm_num
  rw [h3] at hprod
  rw [mul_assoc]
  exact hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobius_incidence_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobius_incidence_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobius_incidence_product ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobius_incidence_product

theorem card_faceCofaces_mobiusEdge_ne_one (i : Fin 5) :
    (faceCofaces mobiusComplex (mobiusEdge i) 3).card ≠ 1 := by
  have h1 : mobiusTri i ∈ faceCofaces mobiusComplex (mobiusEdge i) 3 :=
    (mem_faceCofaces _).mpr ⟨mobiusTri_mem_faces i, mobiusTri_card i, mobiusEdge_subset i⟩
  have h2 : mobiusTri (i + 1) ∈ faceCofaces mobiusComplex (mobiusEdge i) 3 :=
    (mem_faceCofaces _).mpr ⟨mobiusTri_mem_faces _, mobiusTri_card _, mobiusEdge_subset_succ i⟩
  intro hcard
  have hlt := Finset.one_lt_card.mpr ⟨_, h1, _, h2, mobiusTri_ne_succ i⟩
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.card_faceCofaces_mobiusEdge_ne_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.card_faceCofaces_mobiusEdge_ne_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.card_faceCofaces_mobiusEdge_ne_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.card_faceCofaces_mobiusEdge_ne_one

theorem orientedBoundary_mobiusEdge (r : LinearOrder (Fin 5 → ℝ))
    (c : Finset (Fin 5 → ℝ) → ℤ) (i : Fin 5) :
    orientedBoundary r mobiusComplex 2 c (mobiusEdge i) =
      c (mobiusTri i) * incidenceSign r (mobiusTri i) (mobiusVertex i) +
        c (mobiusTri (i + 1)) * incidenceSign r (mobiusTri (i + 1)) (mobiusVertex (i + 3)) := by
  classical
  rw [orientedBoundary, facesOfCard_mobiusComplex_three,
    Finset.sum_image fun a _ b _ h => mobiusTri_injective h]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin 5)), j ∉ ({i, i + 1} : Finset (Fin 5)) →
      c (mobiusTri j) * simplexBoundaryCoefficient r (mobiusTri j) (mobiusEdge i) = 0 := by
    intro j _ hj
    rw [coef_mobius_zero r (fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _))
      (fun h => hj (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))),
      _root_.MulZeroClass.mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, i + 1} : Finset (Fin 5))) hzero,
    Finset.sum_pair (fin5_ne_succ i), coef_mobius_self, coef_mobius_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.orientedBoundary_mobiusEdge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.orientedBoundary_mobiusEdge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.orientedBoundary_mobiusEdge ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.orientedBoundary_mobiusEdge

theorem incidenceIndex_split (r : LinearOrder (Fin 5 → ℝ)) {a b c : Fin 5 → ℝ}
    (hac : a ≠ c) (hbc : b ≠ c) :
    incidenceIndex r ({a, b, c} : Finset (Fin 5 → ℝ)) b =
      incidenceIndex r ({a, b} : Finset (Fin 5 → ℝ)) b +
        incidenceIndex r ({b, c} : Finset (Fin 5 → ℝ)) b := by
  have h1 : ({a, b, c} : Finset (Fin 5 → ℝ)) = ({a, b} : Finset (Fin 5 → ℝ)) ∪ {c} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  have h2 : ({b, c} : Finset (Fin 5 → ℝ)) = ({b} : Finset (Fin 5 → ℝ)) ∪ {c} := by
    ext x
    simp
  have hd1 : Disjoint ({a, b} : Finset (Fin 5 → ℝ)) ({c} : Finset (Fin 5 → ℝ)) :=
    Finset.disjoint_singleton_right.mpr (by simp [Ne.symm hac, Ne.symm hbc])
  have hd2 : Disjoint ({b} : Finset (Fin 5 → ℝ)) ({c} : Finset (Fin 5 → ℝ)) :=
    Finset.disjoint_singleton_right.mpr (by simp [Ne.symm hbc])
  rw [h1, incidenceIndex_union r hd1, h2, incidenceIndex_union r hd2,
    incidenceIndex_singleton_self]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_split ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_split

theorem incidenceIndex_pair_sum (r : LinearOrder (Fin 5 → ℝ)) {a b : Fin 5 → ℝ} (hab : a ≠ b) :
    incidenceIndex r ({a, b} : Finset (Fin 5 → ℝ)) a +
      incidenceIndex r ({a, b} : Finset (Fin 5 → ℝ)) b = 1 := by
  have h := sum_incidenceIndex r ({a, b} : Finset (Fin 5 → ℝ))
  rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton,
    Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at h
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_pair_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_pair_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_pair_sum ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_pair_sum

noncomputable def mobiusLowPair (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) : ℕ :=
  incidenceIndex r ({mobiusVertex i, mobiusVertex (i + 1)} : Finset (Fin 5 → ℝ))
    (mobiusVertex (i + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusLowPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusLowPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusLowPair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusLowPair

noncomputable def mobiusHighPair (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) : ℕ :=
  incidenceIndex r ({mobiusVertex (i + 1), mobiusVertex (i + 2)} : Finset (Fin 5 → ℝ))
    (mobiusVertex (i + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobiusHighPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobiusHighPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobiusHighPair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobiusHighPair

theorem incidenceIndex_mobius_middle (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) :
    incidenceIndex r (mobiusTri i) (mobiusVertex (i + 1)) =
      mobiusLowPair r i + mobiusHighPair r i := by
  rw [mobiusTri_eq_triple]
  exact incidenceIndex_split r (mobiusVertex_ne (fin5_ne_add_two i))
    (mobiusVertex_ne (fin5_succ_ne_add_two i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_mobius_middle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_mobius_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_mobius_middle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.incidenceIndex_mobius_middle

theorem mobius_pair_sum (r : LinearOrder (Fin 5 → ℝ)) (i : Fin 5) :
    mobiusHighPair r i + mobiusLowPair r (i + 1) = 1 := by
  have h := incidenceIndex_pair_sum r (mobiusVertex_ne (fin5_succ_ne_add_two i))
  simp only [mobiusHighPair, mobiusLowPair, fin5_succ_succ]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mobius_pair_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mobius_pair_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mobius_pair_sum ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mobius_pair_sum

theorem sum_incidenceIndex_mobius (r : LinearOrder (Fin 5 → ℝ)) :
    ∑ i : Fin 5, incidenceIndex r (mobiusTri i) (mobiusVertex (i + 1)) = 5 := by
  have hsplit : ∑ i : Fin 5, incidenceIndex r (mobiusTri i) (mobiusVertex (i + 1)) =
      (∑ i : Fin 5, mobiusLowPair r i) + ∑ i : Fin 5, mobiusHighPair r i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => incidenceIndex_mobius_middle r i
  have hsum1 : (∑ i : Fin 5, mobiusHighPair r i) + ∑ i : Fin 5, mobiusLowPair r (i + 1) = 5 := by
    rw [← Finset.sum_add_distrib]
    simp [mobius_pair_sum r]
  have hreindex : ∑ i : Fin 5, mobiusLowPair r (i + 1) = ∑ i : Fin 5, mobiusLowPair r i :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin 5)) _ _ fun _ => rfl
  rw [hreindex] at hsum1
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex_mobius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex_mobius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex_mobius ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sum_incidenceIndex_mobius

theorem prod_neg_fin_five (f : Fin 5 → ℤ) : ∏ i : Fin 5, (-(f i)) = -∏ i : Fin 5, f i := by
  have h : ∏ i : Fin 5, (-(f i)) = (∏ _i : Fin 5, (-1 : ℤ)) * ∏ i : Fin 5, f i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [h, Finset.prod_const]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prod_neg_fin_five then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prod_neg_fin_five"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prod_neg_fin_five ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prod_neg_fin_five

theorem not_isOrientable_mobiusComplex : ¬ IsOrientable 2 mobiusComplex := by
  rintro ⟨o⟩
  set r := o.vertexOrder with hrdef
  set c := o.sign with hcdef
  set A : Fin 5 → ℤ := fun i => incidenceSign r (mobiusTri i) (mobiusVertex i) with hAdef
  set B : Fin 5 → ℤ := fun i => incidenceSign r (mobiusTri i) (mobiusVertex (i + 2)) with hBdef
  set C : Fin 5 → ℤ := fun i => incidenceSign r (mobiusTri i) (mobiusVertex (i + 1)) with hCdef
  have hsq : ∀ (s : Finset (Fin 5 → ℝ)) (v : Fin 5 → ℝ),
      incidenceSign r s v * incidenceSign r s v = 1 := fun s v => incidenceSign_mul_self r s v
  have hrel : ∀ i : Fin 5, c (mobiusTri i) * A i + c (mobiusTri (i + 1)) * B (i + 1) = 0 := by
    intro i
    have h := o.coherent (mobiusEdge i) (mobiusEdge_mem_faces i) (mobiusEdge_card i)
      (card_faceCofaces_mobiusEdge_ne_one i)
    rw [orientedBoundary_mobiusEdge] at h
    simpa only [hAdef, hBdef, fin5_succ_add_two] using h
  have hP : (∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, c (mobiusTri i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases o.sign_top (mobiusTri i) (mobiusTri_mem_faces i) (mobiusTri_card i) with h | h <;>
      rw [hcdef, h] <;> norm_num
  have hprodf : (∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, A i =
      -((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, B i) := by
    calc (∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, A i
        = ∏ i : Fin 5, c (mobiusTri i) * A i := Finset.prod_mul_distrib.symm
      _ = ∏ i : Fin 5, -(c (mobiusTri (i + 1)) * B (i + 1)) :=
          Finset.prod_congr rfl fun i _ => by linarith [hrel i]
      _ = -∏ i : Fin 5, c (mobiusTri (i + 1)) * B (i + 1) := prod_neg_fin_five _
      _ = -∏ i : Fin 5, c (mobiusTri i) * B i := by
          congr 1
          exact Fintype.prod_equiv (Equiv.addRight (1 : Fin 5)) _ _ fun _ => rfl
      _ = -((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, B i) := by
          rw [Finset.prod_mul_distrib]
  have hAB : (∏ i : Fin 5, A i) = -∏ i : Fin 5, B i := by
    calc (∏ i : Fin 5, A i)
        = ((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, A i := by
          rw [hP, one_mul]
      _ = (∏ i : Fin 5, c (mobiusTri i)) *
            ((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, A i) := by ring
      _ = (∏ i : Fin 5, c (mobiusTri i)) *
            -((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, B i) := by rw [hprodf]
      _ = -(((∏ i : Fin 5, c (mobiusTri i)) * ∏ i : Fin 5, c (mobiusTri i)) *
            ∏ i : Fin 5, B i) := by ring
      _ = -∏ i : Fin 5, B i := by rw [hP, one_mul]
  have hBsq : (∏ i : Fin 5, B i) * ∏ i : Fin 5, B i = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => hsq _ _
  have hABprod : (∏ i : Fin 5, A i) * ∏ i : Fin 5, B i = -1 := by
    rw [hAB, neg_mul, hBsq]
  have hACB : ∀ i : Fin 5, A i * B i = -C i := by
    intro i
    have h := mobius_incidence_product r i
    have hC := hsq (mobiusTri i) (mobiusVertex (i + 1))
    have hstep : A i * B i = A i * C i * B i * C i := by
      simp only [hAdef, hBdef, hCdef]
      linear_combination (-(incidenceSign r (mobiusTri i) (mobiusVertex i) *
        incidenceSign r (mobiusTri i) (mobiusVertex (i + 2)))) * hC
    rw [hstep]
    simp only [hAdef, hBdef, hCdef]
    linear_combination incidenceSign r (mobiusTri i) (mobiusVertex (i + 1)) * h
  have hCprod : ∏ i : Fin 5, C i = 1 := by
    have h2 : ∏ i : Fin 5, (A i * B i) = ∏ i : Fin 5, -C i :=
      Finset.prod_congr rfl fun i _ => hACB i
    rw [Finset.prod_mul_distrib, hABprod, prod_neg_fin_five] at h2
    linarith
  have hCval : ∏ i : Fin 5, C i = -1 := by
    have h : ∏ i : Fin 5, C i =
        (-1 : ℤ) ^ ∑ i : Fin 5, incidenceIndex r (mobiusTri i) (mobiusVertex (i + 1)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun i _ => rfl
    rw [h, sum_incidenceIndex_mobius r]
    norm_num
  rw [hCval] at hCprod
  norm_num at hCprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.not_isOrientable_mobiusComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.not_isOrientable_mobiusComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.not_isOrientable_mobiusComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.not_isOrientable_mobiusComplex

end DifferentialGeometry.Topology.PiecewiseLinear
