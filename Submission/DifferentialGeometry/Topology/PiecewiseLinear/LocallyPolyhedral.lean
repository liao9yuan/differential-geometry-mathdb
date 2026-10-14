import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine
import Mathlib.Topology.LocallyFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsLocallyPolyhedral (S : Set E) : Prop :=
  ∀ x ∈ S, ∃ P : Set E, IsPolyhedron P ∧ P ⊆ S ∧ P ∈ 𝓝[S] x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral

theorem IsPolyhedron.isLocallyPolyhedral {S : Set E} (hS : IsPolyhedron S) :
    IsLocallyPolyhedral S :=
  fun _ _ => ⟨S, hS, Subset.rfl, self_mem_nhdsWithin⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.isLocallyPolyhedral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.isLocallyPolyhedral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.isLocallyPolyhedral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.isLocallyPolyhedral

theorem IsPiecewiseAffineOn.isLocallyPolyhedral {f : E → F} {S : Set E}
    (hf : IsPiecewiseAffineOn f S) : IsLocallyPolyhedral S := by
  intro x hx
  obtain ⟨ι, hι, C, _, hC, hnhds⟩ := hf x hx
  exact ⟨⋃ i, C i, ⟨ι, hι, C, fun i => (hC i).1, rfl⟩,
    _root_.Set.iUnion_subset fun i => (hC i).2.1, hnhds⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.isLocallyPolyhedral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.isLocallyPolyhedral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.isLocallyPolyhedral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.isLocallyPolyhedral

theorem IsLocallyPolyhedral.isPiecewiseAffineOn_id {S : Set E} (hS : IsLocallyPolyhedral S) :
    IsPiecewiseAffineOn (id : E → E) S := by
  intro x hx
  obtain ⟨P, ⟨ι, hι, C, hC, rfl⟩, hsub, hnhds⟩ := hS x hx
  exact ⟨ι, hι, C, fun _ => AffineMap.id ℝ E,
    fun i => ⟨hC i, (_root_.Set.subset_iUnion C i).trans hsub, fun _ _ => rfl⟩, hnhds⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPiecewiseAffineOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPiecewiseAffineOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPiecewiseAffineOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPiecewiseAffineOn_id

theorem isLocallyPolyhedral_iff_isPiecewiseAffineOn_id {S : Set E} :
    IsLocallyPolyhedral S ↔ IsPiecewiseAffineOn (id : E → E) S :=
  ⟨IsLocallyPolyhedral.isPiecewiseAffineOn_id, IsPiecewiseAffineOn.isLocallyPolyhedral⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_iff_isPiecewiseAffineOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_iff_isPiecewiseAffineOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_iff_isPiecewiseAffineOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_iff_isPiecewiseAffineOn_id

open _root_.Classical in
theorem IsLocallyPolyhedral.isPolyhedron_of_isCompact {S : Set E}
    (hS : IsLocallyPolyhedral S) (hcompact : IsCompact S) : IsPolyhedron S := by
  choose P hP hPS hPx using fun x : S => hS x x.property
  obtain ⟨t, hcover⟩ := hcompact.elim_nhdsWithin_subcover' (fun x hx => P ⟨x, hx⟩)
    (fun x hx => hPx ⟨x, hx⟩)
  have heq : S = ⋃ x : t, P x := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hcover hx)
      exact mem_iUnion.mpr ⟨⟨y, hyt⟩, hxy⟩
    · exact _root_.Set.iUnion_subset fun x => hPS x
  rw [heq]
  exact IsPolyhedron.iUnion fun x : t => hP x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPolyhedron_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPolyhedron_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPolyhedron_of_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.isPolyhedron_of_isCompact

theorem isPolyhedron_iff_isLocallyPolyhedral_and_isCompact {S : Set E} :
    IsPolyhedron S ↔ IsLocallyPolyhedral S ∧ IsCompact S :=
  ⟨fun h => ⟨h.isLocallyPolyhedral, h.isCompact⟩,
    fun h => h.1.isPolyhedron_of_isCompact h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_iff_isLocallyPolyhedral_and_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_iff_isLocallyPolyhedral_and_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_iff_isLocallyPolyhedral_and_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_iff_isLocallyPolyhedral_and_isCompact

namespace IsLocallyPolyhedral

variable {S T U : Set E}

theorem empty : IsLocallyPolyhedral (∅ : Set E) :=
  IsPolyhedron.empty.isLocallyPolyhedral

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.empty

open _root_.Classical in
theorem exists_isPolyhedron_neighborhood_of_isCompact (hS : IsLocallyPolyhedral S)
    {C : Set E} (hC : IsCompact C) (hCS : C ⊆ S) :
    ∃ P : Set E, IsPolyhedron P ∧ C ⊆ P ∧ P ⊆ S ∧ ∀ x ∈ C, P ∈ 𝓝[S] x := by
  choose P hP hPS hPx using fun x : C => hS x (hCS x.property)
  choose U hU using fun x : C => mem_nhdsWithin.mp (hPx x)
  have hcover : C ⊆ ⋃ x : C, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U (fun x => (hU x).1) hcover
  let Q := ⋃ x : t, P x
  have hQnhds : ∀ x ∈ C, Q ∈ 𝓝[S] x := by
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    have hPy : P y ∈ 𝓝[S] x :=
      mem_nhdsWithin.mpr ⟨U y, (hU y).1, hxy, (hU y).2.2⟩
    exact _root_.Filter.mem_of_superset hPy (_root_.Set.subset_iUnion (fun y : t => P y) ⟨y, hyt⟩)
  exact ⟨Q, IsPolyhedron.iUnion (fun x : t => hP x),
    fun x hx => mem_of_mem_nhdsWithin (hCS hx) (hQnhds x hx),
    _root_.Set.iUnion_subset (fun x : t => hPS x), hQnhds⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_neighborhood_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_neighborhood_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_neighborhood_of_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_neighborhood_of_isCompact

theorem inter (hS : IsLocallyPolyhedral S) (hT : IsLocallyPolyhedral T) :
    IsLocallyPolyhedral (S ∩ T) := by
  rintro x ⟨hxS, hxT⟩
  obtain ⟨P, hP, hPS, hPx⟩ := hS x hxS
  obtain ⟨Q, hQ, hQT, hQx⟩ := hT x hxT
  exact ⟨P ∩ Q, hP.inter hQ, _root_.Set.inter_subset_inter hPS hQT,
    _root_.Filter.inter_mem (nhdsWithin_mono x _root_.Set.inter_subset_left hPx)
      (nhdsWithin_mono x _root_.Set.inter_subset_right hQx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter

theorem exists_isPolyhedron_subset_mem_nhdsWithin [FiniteDimensional ℝ E]
    (hS : IsLocallyPolyhedral S) {x : E} (hx : x ∈ S) (hU : U ∈ 𝓝[S] x) :
    ∃ P : Set E, IsPolyhedron P ∧ P ⊆ S ∩ U ∧ P ∈ 𝓝[S] x := by
  obtain ⟨P, hP, hPS, hPx⟩ := hS x hx
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  obtain ⟨C, hC, hCV, hCx⟩ := exists_isHPolytope_subset_mem_nhds hV
  refine ⟨P ∩ C, hP.inter hC.isPolyhedron, ?_,
    _root_.Filter.inter_mem hPx (mem_nhdsWithin_of_mem_nhds hCx)⟩
  rintro y ⟨hyP, hyC⟩
  exact ⟨hPS hyP, hVU ⟨hCV hyC, hPS hyP⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin

theorem of_isOpen [FiniteDimensional ℝ E] (hS : IsOpen S) : IsLocallyPolyhedral S :=
  (PiecewiseLinear.isPiecewiseAffineOn_id hS).isLocallyPolyhedral

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen

theorem inter_isOpen [FiniteDimensional ℝ E] (hS : IsLocallyPolyhedral S) (hU : IsOpen U) :
    IsLocallyPolyhedral (S ∩ U) :=
  hS.inter (of_isOpen hU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter_isOpen ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.inter_isOpen

open _root_.Classical in
theorem of_isOpen_preimage [FiniteDimensional ℝ E] (hS : IsLocallyPolyhedral S)
    (hTS : T ⊆ S) (hT : IsOpen ((Subtype.val : S → E) ⁻¹' T)) :
    IsLocallyPolyhedral T := by
  obtain ⟨U, hU, hUT⟩ := isOpen_induced_iff.mp hT
  have heq : T = S ∩ U := by
    ext x
    constructor
    · intro hx
      exact ⟨hTS hx, (Set.ext_iff.mp hUT ⟨x, hTS hx⟩).mpr hx⟩
    · rintro ⟨hxS, hxU⟩
      exact (Set.ext_iff.mp hUT ⟨x, hxS⟩).mp hxU
  rw [heq]
  exact hS.inter_isOpen hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen_preimage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_isOpen_preimage

theorem sdiff_isClosed [FiniteDimensional ℝ E] (hS : IsLocallyPolyhedral S) (hT : IsClosed T) :
    IsLocallyPolyhedral (S \ T) :=
  hS.inter_isOpen hT.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.sdiff_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.sdiff_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.sdiff_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.sdiff_isClosed

theorem union (hS : IsLocallyPolyhedral S) (hT : IsLocallyPolyhedral T)
    (hSc : IsClosed ((Subtype.val : ↥(S ∪ T) → E) ⁻¹' S))
    (hTc : IsClosed ((Subtype.val : ↥(S ∪ T) → E) ⁻¹' T)) :
    IsLocallyPolyhedral (S ∪ T) := by
  intro x hx
  by_cases hxS : x ∈ S
  · obtain ⟨P, hP, hPS, hPx⟩ := hS x hxS
    by_cases hxT : x ∈ T
    · obtain ⟨Q, hQ, hQT, hQx⟩ := hT x hxT
      refine ⟨P ∪ Q, hP.union hQ, _root_.Set.union_subset_union hPS hQT, ?_⟩
      rw [nhdsWithin_union, Filter.mem_sup]
      exact ⟨mem_of_superset hPx _root_.Set.subset_union_left, _root_.Filter.mem_of_superset hQx subset_union_right⟩
    · have hxcl : x ∉ closure T := by
        intro hxcl
        apply hxT
        apply (isClosed_preimage_val.mp hTc)
        exact ⟨hx, by simpa only [inter_eq_right.mpr _root_.Set.subset_union_right] using hxcl⟩
      refine ⟨P, hP, hPS.trans _root_.Set.subset_union_left, ?_⟩
      rwa [nhdsWithin_union, notMem_closure_iff_nhdsWithin_eq_bot.mp hxcl, sup_bot_eq]
  · have hxT : x ∈ T := hx.resolve_left hxS
    obtain ⟨Q, hQ, hQT, hQx⟩ := hT x hxT
    have hxcl : x ∉ closure S := by
      intro hxcl
      apply hxS
      apply (isClosed_preimage_val.mp hSc)
      exact ⟨hx, by simpa only [inter_eq_right.mpr _root_.Set.subset_union_left] using hxcl⟩
    refine ⟨Q, hQ, hQT.trans _root_.Set.subset_union_right, ?_⟩
    rwa [nhdsWithin_union, notMem_closure_iff_nhdsWithin_eq_bot.mp hxcl, bot_sup_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union

theorem union_of_isClosed (hS : IsLocallyPolyhedral S) (hT : IsLocallyPolyhedral T)
    (hSc : IsClosed S) (hTc : IsClosed T) : IsLocallyPolyhedral (S ∪ T) :=
  hS.union hT (hSc.preimage continuous_subtype_val) (hTc.preimage continuous_subtype_val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.union_of_isClosed

open _root_.Classical in
theorem iUnion {ι : Type*} [Finite ι] {P : ι → Set E}
    (hP : ∀ i, IsLocallyPolyhedral (P i))
    (hclosed : ∀ i, IsClosed ((Subtype.val : (⋃ j, P j) → E) ⁻¹' P i)) :
    IsLocallyPolyhedral (⋃ i, P i) := by
  intro x hx
  have hlocal : ∀ i, ∃ Q : Set E, IsPolyhedron Q ∧ Q ⊆ P i ∧ Q ∈ 𝓝[P i] x := by
    intro i
    by_cases hxi : x ∈ P i
    · exact hP i x hxi
    · have hxcl : x ∉ closure (P i) := by
        intro hxcl
        apply hxi
        apply (isClosed_preimage_val.mp (hclosed i))
        exact ⟨hx, by simpa only [inter_eq_right.mpr (_root_.Set.subset_iUnion P i)] using hxcl⟩
      refine ⟨∅, IsPolyhedron.empty, _root_.Set.empty_subset _, ?_⟩
      rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hxcl]
      exact _root_.Filter.mem_bot
  choose Q hQ hQP hQx using hlocal
  refine ⟨⋃ i, Q i, IsPolyhedron.iUnion hQ, _root_.Set.iUnion_mono hQP, ?_⟩
  rw [nhdsWithin_iUnion, Filter.mem_iSup]
  exact fun i => _root_.Filter.mem_of_superset (hQx i) (_root_.Set.subset_iUnion Q i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion

theorem iUnion_of_isClosed {ι : Type*} [Finite ι] {P : ι → Set E}
    (hP : ∀ i, IsLocallyPolyhedral (P i)) (hclosed : ∀ i, IsClosed (P i)) :
    IsLocallyPolyhedral (⋃ i, P i) :=
  iUnion hP fun i => (hclosed i).preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iUnion_of_isClosed

open _root_.Classical in
theorem iff_forall_isPolyhedron_inter_of_isClosed
    (hS : IsLocallyPolyhedral S) (hTS : T ⊆ S)
    (hTc : IsClosed ((Subtype.val : S → E) ⁻¹' T)) :
    IsLocallyPolyhedral T ↔
      ∀ P : Set E, IsPolyhedron P → P ⊆ S → IsPolyhedron (T ∩ P) := by
  constructor
  · intro hT P hP hPS
    obtain ⟨C, hC, hCT⟩ := isClosed_induced_iff.mp hTc
    have heq : T ∩ P = P ∩ C := by
      ext x
      have hequiv : x ∈ P → (x ∈ C ↔ x ∈ T) :=
        fun hx => Set.ext_iff.mp hCT ⟨x, hPS hx⟩
      constructor
      · rintro ⟨hxT, hxP⟩
        exact ⟨hxP, (hequiv hxP).mpr hxT⟩
      · rintro ⟨hxP, hxC⟩
        exact ⟨(hequiv hxP).mp hxC, hxP⟩
    exact (hT.inter hP.isLocallyPolyhedral).isPolyhedron_of_isCompact
      (heq.symm ▸ hP.isCompact.inter_right hC)
  · intro h x hx
    obtain ⟨P, hP, hPS, hPx⟩ := hS x (hTS hx)
    exact ⟨T ∩ P, h P hP hPS, _root_.Set.inter_subset_left,
      _root_.Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_mono x hTS hPx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iff_forall_isPolyhedron_inter_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iff_forall_isPolyhedron_inter_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iff_forall_isPolyhedron_inter_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.iff_forall_isPolyhedron_inter_of_isClosed

open _root_.Classical in
theorem of_locallyFinite_cover {ι : Type*} {P : ι → Set E}
    (hP : ∀ i, IsPolyhedron (P i)) (hcover : ⋃ i, P i = S)
    (hloc : LocallyFinite (fun i => (Subtype.val : S → E) ⁻¹' P i)) :
    IsLocallyPolyhedral S := by
  intro x hx
  obtain ⟨U, hUx, hfin⟩ := hloc ⟨x, hx⟩
  rw [nhds_subtype_eq_comap_nhdsWithin] at hUx
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hUx
  let J := {i | ((Subtype.val : S → E) ⁻¹' P i ∩ U).Nonempty}
  let _ : Finite J := hfin.to_subtype
  refine ⟨⋃ i : J, P i, IsPolyhedron.iUnion fun i => hP i, ?_, ?_⟩
  · exact _root_.Set.iUnion_subset fun i => (_root_.Set.subset_iUnion P i).trans hcover.subset
  · filter_upwards [hV, self_mem_nhdsWithin] with y hyV hyS
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hcover.symm ▸ hyS)
    have hi : i ∈ J := ⟨⟨y, hyS⟩, hyi, hVU hyV⟩
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_locallyFinite_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_locallyFinite_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_locallyFinite_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedral.of_locallyFinite_cover

end IsLocallyPolyhedral

theorem isLocallyPolyhedral_space_of_locallyFinite [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E)
    (hloc : LocallyFinite (fun s : K.faces => (Subtype.val : K.space → E) ⁻¹'
      convexHull ℝ ((s : Finset E) : Set E))) : IsLocallyPolyhedral K.space := by
  let P : K.faces → Set E := fun s => convexHull ℝ ((s : Finset E) : Set E)
  have hP : ∀ s, IsPolyhedron (P s) :=
    fun s => isPolyhedron_convexHull_of_affineIndependent s (K.indep s.property)
  have hcover : ⋃ s, P s = K.space := by
    change (⋃ s : K.faces, convexHull ℝ ((s : Finset E) : Set E)) = K.space
    rw [Geometry.SimplicialComplex.space, _root_.Set.biUnion_eq_iUnion]
  exact IsLocallyPolyhedral.of_locallyFinite_cover (S := K.space) (P := P) hP hcover hloc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_space_of_locallyFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_space_of_locallyFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_space_of_locallyFinite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isLocallyPolyhedral_space_of_locallyFinite

end DifferentialGeometry.Topology.PiecewiseLinear
