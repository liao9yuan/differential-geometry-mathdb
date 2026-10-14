import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleOrderTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_ordered_disk_caps_of_essential_sequence {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) {n : ℕ} (J : Fin n → Set M)
    (hJsph : ∀ i, IsPolyhedralSphere (n := 3) 1 (J i)) (hJA : ∀ i, J i ⊆ A)
    (hJend : ∀ i, Disjoint (J i) (A₀ ∪ A₁))
    (hJdisj : Pairwise (fun i j => Disjoint (J i) (J j)))
    (hJess : ∀ i, ¬ ∃ D : Set M, IsPLCellOn 2 D (J i) ∧ D ⊆ A) :
    ∃ (σ : Fin n ≃ Fin n) (D₀ D₁ : Fin n → Set M),
      (∀ i, IsPLCellOn 2 (D₀ i) (J (σ i)) ∧ IsPLCellOn 2 (D₁ i) (J (σ i)) ∧
        D₀ i ∪ D₁ i = B ∧ D₀ i ∩ D₁ i = J (σ i) ∧
        A₀ ⊆ D₀ i ∧ A₁ ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, J (σ i) ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, J (σ i) ⊆ D₁ j ↔ j ≤ i) := by
  classical
  have hne (i : Fin n) : (J i).Nonempty := by
    obtain ⟨T, hT⟩ := hJsph i
    exact T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
  have hinj : Function.Injective J := by
    intro i j hij
    by_contra hneij
    obtain ⟨x, hx⟩ := hne i
    exact disjoint_left.mp (hJdisj hneij) hx (hij ▸ hx)
  have hsph : ∀ L ∈ _root_.Set.range J, IsPolyhedralSphere (n := 3) 1 L := by
    rintro _ ⟨i, rfl⟩
    exact hJsph i
  have hsub : ∀ L ∈ _root_.Set.range J, L ⊆ A := by
    rintro _ ⟨i, rfl⟩
    exact hJA i
  have hend : ∀ L ∈ _root_.Set.range J, Disjoint L (A₀ ∪ A₁) := by
    rintro _ ⟨i, rfl⟩
    exact hJend i
  have hdis : (_root_.Set.range J).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hJdisj (fun h => hij (congrArg J h))
  have hess : ∀ L ∈ _root_.Set.range J, ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A := by
    rintro _ ⟨i, rfl⟩
    exact hJess i
  have hex := hS.exists_ordered_disk_caps_of_essential_family hA hAB (_root_.Set.range J)
    (_root_.Set.finite_range J) hsph hsub hend hdis hess
  have hcard : (_root_.Set.range J).ncard = n := by
    rw [_root_.Set.ncard_range_of_injective hinj, Nat.card_fin]
  rw [hcard] at hex
  obtain ⟨e, D₀, D₁, hcaps, hmono, hanti, hdis, hpos₀, hpos₁⟩ := hex
  let σ := e.trans (Equiv.ofInjective J hinj).symm
  have hσ (i : Fin n) : J (σ i) = (e i).val := Equiv.apply_ofInjective_symm hinj _
  refine ⟨σ, D₀, D₁, ?_, hmono, hanti, hdis, ?_, ?_⟩
  · intro i
    rw [hσ]
    exact hcaps i
  · intro i j
    rw [hσ]
    exact hpos₀ i j
  · intro i j
    rw [hσ]
    exact hpos₁ i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_disk_caps_of_essential_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_disk_caps_of_essential_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_disk_caps_of_essential_sequence ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_ordered_disk_caps_of_essential_sequence

end DifferentialGeometry.Topology.PiecewiseLinear
