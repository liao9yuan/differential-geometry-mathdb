import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PairedPiercingConfiguration
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def Section34SolidBandFilling {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (Cc Cp As Bs T D F : Set M) : Prop :=
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (g : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      R.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R ∧ R.space ⊆ P ∧
      IsCombinatorialSolidTorus R.space ∧
      IsCylindricalDiagram g (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) R.space ∧
      (∀ x ∈ _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1, g (x, 0) = g (x, 1)) ∧
      frontier R.space = g '' (frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      u '' frontier R.space = D ∪ F ∧ u '' R.space ⊆ T ∧
      As ∩ u '' R.space = F ∧ Bs ∩ u '' R.space = D ∧
      u '' R.space ∩ frontier T = F ∩ frontier T ∧
      (u '' R.space ⊆ Cp ∨ u '' R.space ∩ Cp = F)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidBandFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidBandFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidBandFilling ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidBandFilling

def Section34FilledCancellationConfiguration {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (A As B Bs T Cc Cp : Set M) (k : ℕ) (J : ℕ → Set M) : Prop :=
    (∃ i < k, ∃ D : Set M, IsPLCellOn 2 D (J i) ∧
      D ⊆ B ∩ interior T ∧ D ∩ As = J i ∧ IsConnected (D \ J i)) ∨
    ∃ i < k, ∃ j < k, i ≠ j ∧
      (¬ ∃ D : Set M, IsPLCellOn 2 D (J i) ∧ D ⊆ B) ∧
      (¬ ∃ D : Set M, IsPLCellOn 2 D (J j) ∧ D ⊆ B) ∧
      ∃ (F : Set M) (P : Set (EuclideanSpace ℝ (Fin 3)))
        (u : EuclideanSpace ℝ (Fin 3) → M)
        (g : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)),
        IsAnnulusOn F (J i) (J j) ∧ F ⊆ A ∧ Disjoint (F \ (J i ∪ J j)) Bs ∧
        IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
        IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)
          (g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
        g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ P ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ B ∩ interior T ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {0}) = J i ∧
        (u ∘ g) '' (stdSimplexBoundary 2 ×ˢ {1}) = J j ∧
        Disjoint ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) As ∧
        Section34SolidBandFilling Cc Cp As Bs T
          ((u ∘ g) '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledCancellationConfiguration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledCancellationConfiguration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledCancellationConfiguration ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FilledCancellationConfiguration

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

theorem section34_filled_cancellation_configuration_of_paired
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hconfiguration : Section34PairedCancellationConfiguration
      (G (ends e).1 '' Aa e) (G (ends e).1 '' CpBd (ends e).1)
      (G (ends e).2 '' Bb e) (G (ends e).2 '' CpBd (ends e).2) (Tp e) (cnt e) (Pg e)) :
    Section34FilledCancellationConfiguration
      (G (ends e).1 '' Aa e) (G (ends e).1 '' CpBd (ends e).1)
      (G (ends e).2 '' Bb e) (G (ends e).2 '' CpBd (ends e).2) (Tp e)
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1) (cnt e) (Pg e) := by
  rcases hconfiguration with hD | ⟨i, hi, j, hj, hij, hiess, hjess, F, P, u, g,
    hF, hFA, hFempty, hP, hu, hg, hgP, hDT, hzero, hone, hempty⟩
  · exact Or.inl hD
  · have hfill := exists_section34_empty_annular_filling_cylinder hprep hpack e hi hj hij
      hiess hjess hu hg hgP hDT hzero hone hempty hF hFA hFempty
    exact Or.inr ⟨i, hi, j, hj, hij, hiess, hjess, F, P, u, g, hF, hFA, hFempty, hP,
      hu, hg, hgP, hDT, hzero, hone, hempty, hfill⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_filled_cancellation_configuration_of_paired then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_filled_cancellation_configuration_of_paired"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_filled_cancellation_configuration_of_paired ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_filled_cancellation_configuration_of_paired

end DifferentialGeometry.Topology.PiecewiseLinear
