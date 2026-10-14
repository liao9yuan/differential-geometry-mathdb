import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskTraceDeletion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem section34_piercing_disk_disjoint_first_rims
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i)) (hDA : D ⊆ G (ends e).1 '' Aa e) :
    Disjoint D (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).2
  have hgen := section34_piercing_generators hprep hpack e
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hG, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ _root_.Set.inter_subset_left
  have hDB : D ⊆ G (ends e).1 '' CpBd (ends e).1 := hDA.trans (_root_.Set.image_mono hAB)
  have hDT : D ⊆ Tp e := by
    rw [(htube e).2]
    exact hDA.trans (_root_.Set.image_mono ((hAa e).1 ▸ _root_.Set.inter_subset_right))
  have hR : Ab₀ e ∪ Ab₁ e ⊆ Cp (ends e).1 :=
    (_root_.Set.union_subset (hAa e).2.first_subset (hAa e).2.second_subset).trans
      (hAB.trans (hCp _).boundary_subset)
  have hsep : Disjoint (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) (Pg e i) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxJ
    obtain ⟨y, hy, hyx⟩ := ((hPg e i hi).2 hxJ).1
    have hxy := (hG _).injOn ((hCp _).boundary_subset (hAB hy.1)) (hR hx) hyx
    exact hy.2 (hxy.symm ▸ hx)
  have hdis (Y : Set M₂) (hY : IsPreconnected Y) (hne : Y.Nonempty)
      (hYR : Y ⊆ G (ends e).1 '' (Ab₀ e ∪ Ab₁ e))
      (hYB : Y ⊆ G (ends e).1 '' CpBd (ends e).1)
      (hcarry : CarriesFundamentalGroupOnto Y (Tp e)) : Disjoint D Y := by
    rcases ((hCp _).image (hG _)).subset_or_disjoint_boundary_disk hD hDB hY hYB
      (hsep.mono_left hYR) with hsub | hdis
    · exact (htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT hne hsub
        hcarry).elim
    · exact hdis
  rw [_root_.Set.image_union, _root_.Set.disjoint_union_right]
  exact ⟨hdis _ hann.isPreconnected_ends.1 hann.ends_nonempty.1
      (_root_.Set.image_mono _root_.Set.subset_union_left) (_root_.Set.image_mono ((hAa e).2.first_subset.trans hAB)) hgen.1,
    hdis _ hann.isPreconnected_ends.2 hann.ends_nonempty.2
      (_root_.Set.image_mono _root_.Set.subset_union_right) (_root_.Set.image_mono ((hAa e).2.second_subset.trans hAB)) hgen.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_disk_disjoint_first_rims then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_disk_disjoint_first_rims"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_disk_disjoint_first_rims ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_piercing_disk_disjoint_first_rims

end DifferentialGeometry.Topology.PiecewiseLinear
