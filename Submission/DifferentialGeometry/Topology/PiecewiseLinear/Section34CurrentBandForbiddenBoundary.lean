import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BandForbiddenBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem band_forbidden_boundary_of_annular_contacts
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {X Y As Bs A A₀ A₁ B B₀ B₁ R D F J₀ J₁ : Set M}
    (hcellA : IsPLCellOn 3 X As) (hcellB : IsPLCellOn 3 Y Bs)
    (hA : IsAnnulusOn A A₀ A₁) (hB : IsAnnulusOn B B₀ B₁)
    (hAAs : A ⊆ As) (hBBs : B ⊆ Bs)
    (hF : IsAnnulusOn F J₀ J₁) (hD : IsAnnulusOn D J₀ J₁)
    (hFA : F ⊆ A) (hDB : D ⊆ B)
    (hJA : Disjoint (J₀ ∪ J₁) (A₀ ∪ A₁))
    (hJB : Disjoint (J₀ ∪ J₁) (B₀ ∪ B₁))
    (hfirst : As ∩ R = F) (hsecond : Bs ∩ R = D) :
    let Z := ((A₀ ∪ A₁) ∪ (B₀ ∪ B₁)) ∪ closure (Bs \ B)
    IsClosed Z ∧ Z ⊆ As ∪ Bs ∧ Disjoint Z (D ∪ F) := by
  obtain ⟨hcA⟩ := hcellA.nonempty_chartedSpace_boundary
  obtain ⟨hcB⟩ := hcellB.nonempty_chartedSpace_boundary
  let _ := hcA
  let _ := hcB
  have hFrim := hF.disjoint_ends_of_subset_within hA hAAs hFA hJA
  have hDrim := hD.disjoint_ends_of_subset_within hB hBBs hDB hJB
  have hArim : A₀ ∪ A₁ ⊆ As :=
    (_root_.Set.union_subset hA.first_subset hA.second_subset).trans hAAs
  have hBrim : B₀ ∪ B₁ ⊆ Bs :=
    (_root_.Set.union_subset hB.first_subset hB.second_subset).trans hBBs
  have hDArim : Disjoint D (A₀ ∪ A₁) := by
    refine disjoint_left.mpr fun x hx hy => ?_
    exact disjoint_left.mp hFrim
      (hfirst.subset ⟨hArim hy, (hsecond.symm.subset hx).2⟩) hy
  have hFBrim : Disjoint F (B₀ ∪ B₁) := by
    refine disjoint_left.mpr fun x hx hy => ?_
    exact disjoint_left.mp hDrim
      (hsecond.subset ⟨hBrim hy, (hfirst.symm.subset hx).2⟩) hy
  have hcontact : (D ∪ F) ∩ Bs ⊆ B := by
    rintro x ⟨hx | hx, hxB⟩
    · exact hDB hx
    · exact hDB (hsecond.subset ⟨hxB, (hfirst.symm.subset hx).2⟩)
  have hBrim' := disjoint_union_left.mpr ⟨hDrim, hFBrim⟩
  have houtside := hcellB.disjoint_closure_sdiff_of_annular_contact hB hBBs hcontact hBrim'
  have hBs : IsClosed Bs := hcellB.boundary_eq_frontier ▸ isClosed_frontier
  refine ⟨?_, ?_, ?_⟩
  · exact (((hA.ends_isCompact.1.union hA.ends_isCompact.2).isClosed).union
      (hB.ends_isCompact.1.union hB.ends_isCompact.2).isClosed).union isClosed_closure
  · exact _root_.Set.union_subset (_root_.Set.union_subset (hArim.trans _root_.Set.subset_union_left)
      (hBrim.trans _root_.Set.subset_union_right))
      ((closure_minimal _root_.Set.sdiff_subset hBs).trans _root_.Set.subset_union_right)
  · exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨(disjoint_union_left.mpr ⟨hDArim, hFrim⟩).symm, hBrim'.symm⟩, houtside.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.band_forbidden_boundary_of_annular_contacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.band_forbidden_boundary_of_annular_contacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.band_forbidden_boundary_of_annular_contacts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.band_forbidden_boundary_of_annular_contacts

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34_current_band_forbidden_boundary
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) {D F T : Set M₂}
    (Ψ : M₂ ≃ₜ M₂) (hfix : _root_.Set.EqOn Ψ id (Pg e i ∪ Pg e j))
    (hcellB : IsPLCellOn 3 (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (Ψ '' (G (ends e).2 '' CpBd (ends e).2)))
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (Ψ '' (G (ends e).2 '' CpBd (ends e).2))
      T D F (Pg e i) (Pg e j))
    (hFA : F ⊆ G (ends e).1 '' Aa e) (hDB : D ⊆ Ψ '' (G (ends e).2 '' Bb e)) :
    let Z := (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ∪
      Ψ '' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e))) ∪
      closure (Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ Ψ '' (G (ends e).2 '' Bb e))
    IsClosed Z ∧ Z ⊆ G (ends e).1 '' CpBd (ends e).1 ∪
      Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∧ Disjoint Z (D ∪ F) := by
  obtain ⟨hF, hD, -⟩ := hfill.face_annuli_and_intersection
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, -, -, -, -, -, -, -, -, -, -, -, -, hfirst,
    hsecond, -⟩ := hfill
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, -⟩ := id hpack
  obtain ⟨hannA, hannB⟩ := section34_piercing_annuli hprep hpack e
  have hAsub : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ _root_.Set.inter_subset_left
  have hAcp := hAsub.trans (hCp (ends e).1).boundary_subset
  have hBcp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hendsA (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).1
    have hzCp := hAcp ((_root_.Set.union_subset (hAa e).2.first_subset (hAa e).2.second_subset) hz)
    have heq := (hGp (ends e).1).injOn (hAcp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hendsB (k : ℕ) (hk : k < cnt e) :
      Disjoint (Pg e k) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) := by
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e k hk).2 hy).2
    have hzCp := hBcp ((_root_.Set.union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGp (ends e).2).injOn (hBcp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hJA := disjoint_union_left.mpr ⟨hendsA i hi, hendsA j hj⟩
  have hJB := disjoint_union_left.mpr ⟨hendsB i hi, hendsB j hj⟩
  have hJB' : Disjoint (Pg e i ∪ Pg e j)
      (Ψ '' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e))) := by
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    have hzy' : z = y := Ψ.injective (hzy.trans (hfix hy).symm)
    exact disjoint_left.mp hJB hy (hzy' ▸ hz)
  have hannB' := hannB.image_of_continuousOn_injOn Ψ.continuous.continuousOn Ψ.injective.injOn
  have hz := band_forbidden_boundary_of_annular_contacts
    ((hCp (ends e).1).image (hGp (ends e).1)) hcellB hannA hannB'
    (_root_.Set.image_mono hAsub) (_root_.Set.image_mono (_root_.Set.image_mono (hBb e).1)) hF hD hFA hDB
    (by simpa only [_root_.Set.image_union] using hJA) (by simpa only [_root_.Set.image_union] using hJB')
    hfirst hsecond
  simpa only [_root_.Set.image_union] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_current_band_forbidden_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_current_band_forbidden_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_current_band_forbidden_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_current_band_forbidden_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
