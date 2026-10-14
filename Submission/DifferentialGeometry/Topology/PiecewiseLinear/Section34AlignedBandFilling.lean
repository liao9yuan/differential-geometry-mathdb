import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledPiercingConfiguration
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedFillingCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def Section34AlignedBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (Cc Cp As Bs T D F J₀ J₁ : Set M) : Prop :=
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a : Fin 2 → ℝ × ℝ),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCombinatorialSolidTorus R.space ∧
      IsCylindricalDiagram g (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) R.space ∧
      (∀ x ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)) ∧
      frontier R.space = g '' (frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ T ∧
      As ∩ u '' R.space = F ∧ Bs ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier T = F ∩ frontier T ∧
      (u '' R.space ⊆ Cp ∨ u '' R.space ∩ Cp = F) ∧
      (∀ k, a k ∈ frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      Function.Injective a ∧
      (u ∘ g) '' ({a 0} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = J₀ ∧
      (u ∘ g) '' ({a 1} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = J₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling

theorem Section34AlignedBandFilling.toSolidBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp As Bs T D F J₀ J₁ : Set M}
    (h : Section34AlignedBandFilling Cc Cp As Bs T D F J₀ J₁) :
    Section34SolidBandFilling Cc Cp As Bs T D F := by
  obtain ⟨P, u, R, g, a, hP, hu, hcell, hRfin, hR, hRP, hsolid, hg, hends,
    hside, hfront, hT, hfirst, hsecond, hcontact, hposition, -⟩ := h
  exact ⟨P, u, R, g, hP, hu, hcell, hRfin, hR, hRP, hsolid, hg, hends,
    hside, hfront, hT, hfirst, hsecond, hcontact, hposition⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling.toSolidBandFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling.toSolidBandFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling.toSolidBandFilling ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AlignedBandFilling.toSolidBandFilling

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

theorem section34_aligned_band_filling_of_solid
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    (hiess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e)
    (hjess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e j) ∧ D ⊆ G (ends e).2 '' Bb e)
    {D F : Set M₂} (hF : IsAnnulusOn F (Pg e i) (Pg e j))
    (hfill : Section34SolidBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F) :
    Section34AlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (G (ends e).2 '' CpBd (ends e).2) (Tp e) D F
      (Pg e i) (Pg e j) := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  obtain ⟨P, u, R, g, hP, hu, hcell, hRfin, hR, hRP, hsolid, hg, hends,
    -, hfront, hT, hfirst, hsecond, hcontact, hposition⟩ := hfill
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨B, hBfin, hBspace⟩ := isPLBall_unit_square.isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hB : IsPLBall 2 B.space := hBspace.symm ▸ isPLBall_unit_square
  have hgB : IsCylindricalDiagram g B.space R.space := hBspace.symm ▸ hg
  have hendsB : ∀ x ∈ B.space, g (x, 0) = g (x, 1) := hBspace.symm ▸ hends
  obtain ⟨g', -, a, hg', hends', -, -, hinj, hzero, hone⟩ :=
    exists_section34_aligned_filling_cylinder hprep hpack e hi hj hij hiess hjess
      B R hB hR hu hRP hgB hendsB hF hT hfront
  have hBd : (boundaryComplex 2 B).space =
      frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (by simp [Module.finrank_prod])
      B hB.isCombinatorialManifoldWithBoundary, hBspace]
  have hgfront := hg'.frontier_eq_image_side B R hB hR (by simp)
  rw [hBd] at hgfront
  rw [hBspace] at hg' hends'
  refine ⟨P, u, R, g', fun k => (a k : ℝ × ℝ), hP, hu, hcell, hRfin, hR, hRP,
    hsolid, hg', hends', hgfront, hfront, hT, hfirst, hsecond, hcontact, hposition,
    fun k => hBd ▸ (a k).2, ?_, hzero, hone⟩
  exact fun k l hkl => hinj (Subtype.ext hkl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_aligned_band_filling_of_solid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_aligned_band_filling_of_solid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_aligned_band_filling_of_solid ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_aligned_band_filling_of_solid

end DifferentialGeometry.Topology.PiecewiseLinear
