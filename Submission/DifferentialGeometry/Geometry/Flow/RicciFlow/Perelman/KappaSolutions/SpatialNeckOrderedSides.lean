import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOrientedSides
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckAmbientTopology
import Submission.DifferentialGeometry.Topology.SphereSeparation.FiniteBicollarOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance orderedSidesSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesSphereDimension target :: scope.openDecls } }

private local instance orderedSidesSphereConnected : ConnectedSpace SpatialNeckSphere := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesSphereConnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesSphereConnected target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance orderedSidesC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orderedSidesC1 target :: scope.openDecls } }

structure SpatialNeckSideData {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon) where
  lower : ℝ → Set N
  upper : ℝ → Set N
  slice_spec : ∀ s : ℝ, |s| < epsilon⁻¹ + 1 →
    IsConnected (lower s) ∧ IsConnected (upper s) ∧
      IsOpen (lower s) ∧ IsOpen (upper s) ∧ Disjoint (lower s) (upper s) ∧
      lower s ∪ upper s = (W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s})ᶜ ∧
      IsCompact (closure (lower s)) ∧ ¬ IsCompact (closure (upper s)) ∧
      closure (lower s) = lower s ∪ W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s} ∧
      interior (closure (lower s)) = lower s ∧
      frontier (lower s) = W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s} ∧
      frontier (upper s) = W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s}
  negative : ∀ s : ℝ, |s| < epsilon⁻¹ + 1 →
    ∀ x : spatialNeckBuffer epsilon, x.val.2 < s → W.embedding x ∈ lower s
  positive : ∀ s : ℝ, |s| < epsilon⁻¹ + 1 →
    ∀ x : spatialNeckBuffer epsilon, s < x.val.2 → W.embedding x ∈ upper s
  ordered_band : ∀ s t : ℝ, |s| < epsilon⁻¹ + 1 → |t| < epsilon⁻¹ + 1 → s < t →
    closure (lower s) ⊆ lower t ∧
      closure (lower t) = closure (lower s) ∪
        W.embedding '' {x : spatialNeckBuffer epsilon | s ≤ x.val.2 ∧ x.val.2 ≤ t} ∧
      (W.embedding '' {x : spatialNeckBuffer epsilon | s ≤ x.val.2 ∧ x.val.2 ≤ t})ᶜ =
        lower s ∪ upper t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
  (D : SpatialNeckSideData W)

theorem path_crosses_slice (s : ℝ) (hs : |s| < epsilon⁻¹ + 1)
    {x y : N} (hx : x ∈ D.lower s) (hy : y ∈ D.upper s) (γ : Path x y) :
    ∃ u, γ u ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
  by_contra! havoid
  obtain ⟨_hB, _hU, hBop, hUop, hBU, hcover, _hc, _hnc, _hcl, _hint, _hBfr, _hUfr⟩ :=
    D.slice_spec s hs
  have hsub : _root_.Set.range γ ⊆ D.lower s ∪ D.upper s := by
    rw [hcover]
    rintro q ⟨u, rfl⟩
    exact havoid u
  have hleft : _root_.Set.range γ ⊆ D.lower s :=
    (isConnected_range γ.continuous).isPreconnected.subset_left_of_subset_union
      hBop hUop hBU hsub ⟨x, ⟨0, γ.source⟩, hx⟩
  exact Set.disjoint_left.mp hBU (hleft ⟨1, γ.target⟩) hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.path_crosses_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.path_crosses_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.path_crosses_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.path_crosses_slice

theorem continuous_curve_crosses_slice (s : ℝ) (hs : |s| < epsilon⁻¹ + 1)
    {a b : ℝ} (hab : a ≤ b) {γ : ℝ → N} (hγ : ContinuousOn γ (_root_.Set.Icc a b))
    (ha : γ a ∈ D.lower s) (hb : γ b ∈ D.upper s) :
    ∃ u ∈ _root_.Set.Icc a b, γ u ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
  by_contra! havoid
  obtain ⟨_hB, _hU, hBop, hUop, hBU, hcover, _hc, _hnc, _hcl, _hint, _hBfr, _hUfr⟩ :=
    D.slice_spec s hs
  have hsub : γ '' _root_.Set.Icc a b ⊆ D.lower s ∪ D.upper s := by
    rw [hcover]
    rintro q ⟨u, hu, rfl⟩
    exact havoid u hu
  have hleft : γ '' _root_.Set.Icc a b ⊆ D.lower s :=
    (isPreconnected_Icc.image γ hγ).subset_left_of_subset_union hBop hUop hBU hsub
      ⟨γ a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩, ha⟩
  exact Set.disjoint_left.mp hBU (hleft ⟨b, ⟨hab, le_rfl⟩, rfl⟩) hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.continuous_curve_crosses_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.continuous_curve_crosses_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.continuous_curve_crosses_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.continuous_curve_crosses_slice


theorem closure_lower_eq_compl_upper (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) :
    closure (D.lower s) = (D.upper s)ᶜ := by
  classical
  obtain ⟨_hB, _hU, _hBop, _hUop, hBU, hcover, _hc, _hnc, hcl, _hint, _hBfr, _hUfr⟩ :=
    D.slice_spec s hs
  rw [hcl]
  ext x
  have hu : (x ∈ D.lower s ∨ x ∈ D.upper s) ↔
      x ∉ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} :=
    Iff.of_eq (congrArg (fun U : Set N => x ∈ U) hcover)
  have hd : ¬ (x ∈ D.lower s ∧ x ∈ D.upper s) :=
    fun hx => Set.disjoint_left.mp hBU hx.1 hx.2
  change (x ∈ D.lower s ∨ x ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s}) ↔
    x ∉ D.upper s
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.closure_lower_eq_compl_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.closure_lower_eq_compl_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.closure_lower_eq_compl_upper ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.closure_lower_eq_compl_upper


theorem marked_mem_lower (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) (hspos : 0 < s) :
    p ∈ D.lower s := by
  have hmem := D.negative s hs (spatialNeckCentralPoint epsilon W.epsilon_pos yStar) hspos
  rwa [W.marked] at hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_lower


theorem marked_mem_upper (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) (hsneg : s < 0) :
    p ∈ D.upper s := by
  have hmem := D.positive s hs (spatialNeckCentralPoint epsilon W.epsilon_pos yStar) hsneg
  rwa [W.marked] at hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_upper ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.marked_mem_upper

end SpatialNeckSideData

namespace SpatialNeckWitness

private theorem side_data_of_oriented [I.Boundaryless]
    [ConnectedSpace N] [LocallyConnectedSpace N] [NoncompactSpace N]
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (ρ : C(N, N)) (hρ : ContinuousMap.Homotopic ρ (ContinuousMap.id N))
    (hdisjoint : Disjoint (_root_.Set.range ρ) W.centralSphere)
    (B0 : Set N) (hB0 : IsConnected B0) (hB0op : IsOpen B0)
    (hB0c : IsCompact (closure B0)) (hB0fr : frontier B0 = W.centralSphere)
    (hn0 : ∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W.embedding x ∈ B0) :
    Nonempty (SpatialNeckSideData W) := by
  let r := epsilon⁻¹ + 1
  have hepsilon : 0 < epsilon := W.epsilon_pos
  have hr : 0 < r := by dsimp only [r]; positivity
  let ξ : {q : SpatialNeckCylinder // -r < q.2 ∧ q.2 < r} ≃ₜ spatialNeckBuffer epsilon :=
    Homeomorph.setCongr (by
      ext q
      change (-(epsilon⁻¹ + 1) < q.2 ∧ q.2 < epsilon⁻¹ + 1) ↔
        (-epsilon⁻¹ - 1 < q.2 ∧ q.2 < epsilon⁻¹ + 1)
      simp only [neg_add, sub_eq_add_neg])
  let η0 := bicollarLineHomeomorph (A := SpatialNeckSphere) r hr
  let η : SpatialNeckCylinder ≃ₜ spatialNeckBuffer epsilon := η0.trans ξ
  let φ0 : {q : SpatialNeckCylinder // -r < q.2 ∧ q.2 < r} → N := W.embedding ∘ ξ
  let φ : SpatialNeckCylinder → N := W.embedding ∘ η
  have hφ0 : _root_.Topology.IsOpenEmbedding φ0 := W.embedding_isOpenEmbedding.comp ξ.isOpenEmbedding
  have hφ : _root_.Topology.IsOpenEmbedding φ := W.embedding_isOpenEmbedding.comp η.isOpenEmbedding
  let f := OpenPartialHomeomorph.univBall (0 : ℝ) r
  let σ : ℝ → ℝ := f.symm
  have hcenter : _root_.Set.range (fun y => φ (y, 0)) = W.centralSphere := by
    rw [W.centralSphere_eq_range]
    congr 1
    funext y
    apply congrArg W.embedding
    apply Subtype.ext
    exact bicollarLineHomeomorph_center r hr y
  have hdisjointφ : Disjoint (_root_.Set.range ρ) (_root_.Set.range (fun y => φ (y, 0))) := by
    rwa [hcenter]
  have hdisjointφ0 : Disjoint (_root_.Set.range ρ)
      (_root_.Set.range (fun y => φ0 ⟨(y, 0), by constructor <;> linarith⟩)) := by
    have hcenter0 : _root_.Set.range (fun y => φ0 ⟨(y, 0), by constructor <;> linarith⟩) =
        W.centralSphere := by
      rw [W.centralSphere_eq_range]
      rfl
    rwa [hcenter0]
  have hpoint : φ (yStar, 0 - 1) ∈ B0 := by
    apply hn0
    exact (bicollarLineHomeomorph_negative_iff r hr yStar (0 - 1)).mpr (by norm_num)
  have hzeroEq := connectedComponentIn_compl_frontier_eq hB0 hB0op hpoint
  rw [hB0fr, ← hcenter] at hzeroEq
  have hzero : IsCompact (closure (bicollarLowerSide φ yStar 0)) := by
    change IsCompact (closure (connectedComponentIn (_root_.Set.range (fun y => φ (y, 0)))ᶜ
      (φ (yStar, 0 - 1))))
    rwa [hzeroEq]
  have hslice (s : ℝ) (hs : |s| < r) :
      _root_.Set.range (fun y => φ (y, σ s)) =
        W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
    have hfs : f (σ s) = s := bicollar_axial_apply_inverse r hr s (abs_lt.mp hs)
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨η (y, σ s), hfs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.val.1, congrArg W.embedding ?_⟩
      exact Subtype.ext (Prod.ext rfl (hfs.trans hx.symm))
  have hξimage (P : ℝ → Prop) :
      ξ '' {q : {q : SpatialNeckCylinder // -r < q.2 ∧ q.2 < r} | P q.val.2} =
        {q : spatialNeckBuffer epsilon | P q.val.2} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨ξ.symm x, hx, ξ.apply_symm_apply x⟩
  let B : ℝ → Set N := fun s => bicollarLowerSide φ yStar (σ s)
  let U : ℝ → Set N := fun s => bicollarUpperSide φ yStar (σ s)
  refine ⟨⟨B, U, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    obtain ⟨hB, hU, hBop, hUop, hBU, hcover, hBfr, hUfr, hBcl, _hUcl, _hn, _hp⟩ :=
      bicollar_slice_components_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar (σ s)
    rw [hslice s hs] at hcover hBfr hUfr hBcl
    exact ⟨hB, hU, hBop, hUop, hBU, hcover,
      bicollar_lower_compact_of_zero_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar hzero (σ s),
      bicollar_upper_noncompact_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar hzero (σ s), hBcl,
      bicollar_lower_regular_open_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar (σ s), hBfr, hUfr⟩
  · intro s hs x hx
    obtain ⟨_hB, _hU, _hBop, _hUop, _hBU, _hcover, _hBfr, _hUfr, _hBcl, _hUcl, hn, _hp⟩ :=
      bicollar_slice_components_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar (σ s)
    have hrecover : f (η.symm x).2 = x.val.2 :=
      congrArg (fun q : spatialNeckBuffer epsilon => q.val.2) (η.apply_symm_apply x)
    have hfs : f (σ s) = s := bicollar_axial_apply_inverse r hr s (abs_lt.mp hs)
    have hparam : (η.symm x).2 < σ s := by
      apply (bicollar_axial_strictMono r hr).lt_iff_lt.mp
      rw [hrecover, hfs]
      exact hx
    have hmem := hn (η.symm x).1 (η.symm x).2 hparam
    change W.embedding (η (η.symm x)) ∈ B s at hmem
    rwa [η.apply_symm_apply] at hmem
  · intro s hs x hx
    obtain ⟨_hB, _hU, _hBop, _hUop, _hBU, _hcover, _hBfr, _hUfr, _hBcl, _hUcl, _hn, hp⟩ :=
      bicollar_slice_components_of_homotopic_disjoint
        φ hφ ρ hρ hdisjointφ yStar (σ s)
    have hrecover : f (η.symm x).2 = x.val.2 :=
      congrArg (fun q : spatialNeckBuffer epsilon => q.val.2) (η.apply_symm_apply x)
    have hfs : f (σ s) = s := bicollar_axial_apply_inverse r hr s (abs_lt.mp hs)
    have hparam : σ s < (η.symm x).2 := by
      apply (bicollar_axial_strictMono r hr).lt_iff_lt.mp
      rw [hrecover, hfs]
      exact hx
    have hmem := hp (η.symm x).1 (η.symm x).2 hparam
    change W.embedding (η (η.symm x)) ∈ U s at hmem
    rwa [η.apply_symm_apply] at hmem
  · intro s t hs ht hst
    obtain ⟨hnest, hcl, hcompl⟩ :=
      finite_bicollar_ordered_band_of_homotopic_disjoint r hr φ0 hφ0 yStar
      ρ hρ hdisjointφ0 hzero s t (abs_lt.mp hs) (abs_lt.mp ht) hst
    have hband : φ0 '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} =
        W.embedding '' {q : spatialNeckBuffer epsilon | s ≤ q.val.2 ∧ q.val.2 ≤ t} := by
      change (W.embedding ∘ ξ) '' _ = _
      rw [_root_.Set.image_comp, hξimage (fun z => s ≤ z ∧ z ≤ t)]
    rw [hband] at hcl hcompl
    exact ⟨hnest, hcl, hcompl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.side_data_of_oriented
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.side_data_of_oriented target :: scope.openDecls } }

theorem exists_ordered_compact_end_sides [I.Boundaryless] [ConnectedSpace N] [NoncompactSpace N]
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ∃ W' : SpatialNeckWitness h yStar p epsilon,
      (W' = W ∨ W' = W.reflect) ∧ W'.centralSphere = W.centralSphere ∧
      W'.core = W.core ∧ W'.image = W.image ∧ Nonempty (SpatialNeckSideData W') := by
  obtain ⟨W', hchoice, hsphere, hcore, himage, B, U, hB, hU, hBop, _hUop, _hBU,
    hcover, hBc, _hUnc, _hcl, hint, hfr, _hUfr, hn, _hp⟩ :=
      W.exists_oriented_compact_end_sides hsec
  obtain ⟨e⟩ := W'.nonempty_ambient_homeomorph hsec
  let _ : LocallyPathConnectedSpace N := e.isOpenEmbedding.locallyPathConnectedSpace
  obtain ⟨q, hqU⟩ := hU.nonempty
  let ρ : C(N, N) := ContinuousMap.const N q
  have hρ : ContinuousMap.Homotopic ρ (ContinuousMap.id N) := by
    refine ⟨{
      toFun := fun z => e.symm ((1 - (z.1 : ℝ)) • e q + (z.1 : ℝ) • e z.2)
      continuous_toFun := e.symm.continuous.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (e.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      simp [ρ]
    · intro x
      simp
  have hdisjoint : Disjoint (_root_.Set.range ρ) W'.centralSphere := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ hx
    have hq : q ∈ B ∪ U := Or.inr hqU
    rw [hcover] at hq
    exact hq (hsphere ▸ hx)
  have hfront : frontier B = W'.centralSphere := by
    have hsame : frontier B = frontier (closure B) := by
      rw [frontier, frontier, closure_closure, hBop.interior_eq, hint]
    exact hsame.trans (hfr.trans hsphere.symm)
  exact ⟨W', hchoice, hsphere, hcore, himage,
    side_data_of_oriented W' ρ hρ hdisjoint B hB hBop hBc hfront hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides


theorem exists_ordered_compact_end_sides_of_homotopic_disjoint [I.Boundaryless]
    [ConnectedSpace N] [LocallyConnectedSpace N] [NoncompactSpace N]
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (ρ : C(N, N)) (hρ : ContinuousMap.Homotopic ρ (ContinuousMap.id N))
    (hdisjoint : Disjoint (_root_.Set.range ρ) W.centralSphere)
    (hends : ¬ DifferentialGeometry.Geometry.Topology.HasAtLeastEnds N 2) :
    ∃ W' : SpatialNeckWitness h yStar p epsilon,
      (W' = W ∨ W' = W.reflect) ∧ W'.centralSphere = W.centralSphere ∧
      W'.core = W.core ∧ W'.image = W.image ∧ Nonempty (SpatialNeckSideData W') := by
  obtain ⟨W', hchoice, hsphere, hcore, himage, B, U, hB, _hU, hBop, _hUop, _hBU,
    _hcover, hBc, _hUnc, _hcl, hint, hfr, _hUfr, hn, _hp⟩ :=
      W.exists_oriented_compact_end_sides_of_homotopic_disjoint ρ hρ hdisjoint hends
  have hfront : frontier B = W'.centralSphere := by
    have hsame : frontier B = frontier (closure B) := by
      rw [frontier, frontier, closure_closure, hBop.interior_eq, hint]
    exact hsame.trans (hfr.trans hsphere.symm)
  have hdisjoint' : Disjoint (_root_.Set.range ρ) W'.centralSphere := by rwa [hsphere]
  exact ⟨W', hchoice, hsphere, hcore, himage,
    side_data_of_oriented W' ρ hρ hdisjoint' B hB hBop hBc hfront hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides_of_homotopic_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides_of_homotopic_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides_of_homotopic_disjoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.exists_ordered_compact_end_sides_of_homotopic_disjoint

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
