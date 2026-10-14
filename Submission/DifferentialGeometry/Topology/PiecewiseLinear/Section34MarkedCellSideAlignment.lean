import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellPageImages
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellReflection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_cell_sign_for_opposite_pairs
    {E : Type*} {G : (ℝ × ℝ) × ℝ → E} {P : Fin 4 → Set E}
    (heven : (G '' section34MarkedRibbon 0 = P 0 ∧
        G '' section34MarkedRibbon 2 = P 2) ∨
      (G '' section34MarkedRibbon 0 = P 2 ∧ G '' section34MarkedRibbon 2 = P 0))
    (hodd : (G '' section34MarkedRibbon 1 = P 1 ∧
        G '' section34MarkedRibbon 3 = P 3) ∨
      (G '' section34MarkedRibbon 1 = P 3 ∧ G '' section34MarkedRibbon 3 = P 1)) :
    ∃ a b : Bool, ∀ i, G '' section34MarkedRibbon (section34SpokeSignPerm a b i) = P i := by
  rcases heven with he | he <;> rcases hodd with ho | ho
  · refine ⟨false, _root_.Bool.false, ?_⟩
    intro i
    fin_cases i <;> simp only [section34SpokeSignPerm, Bool.false_eq_true,
      ↓reduceIte, Equiv.trans_apply, Equiv.refl_apply] <;>
      first | exact he.1 | exact he.2 | exact ho.1 | exact ho.2
  · refine ⟨false, _root_.Bool.true, ?_⟩
    intro i
    fin_cases i <;> simp only [section34SpokeSignPerm, Bool.false_eq_true,
      ↓reduceIte, Equiv.trans_apply, Equiv.refl_apply, Equiv.swap_apply_def] <;>
      norm_num [Fin.ext_iff] <;> first | exact he.1 | exact he.2 | exact ho.1 | exact ho.2
  · refine ⟨true, _root_.Bool.false, ?_⟩
    intro i
    fin_cases i <;> simp only [section34SpokeSignPerm, Bool.false_eq_true,
      ↓reduceIte, Equiv.trans_apply, Equiv.refl_apply, Equiv.swap_apply_def] <;>
      norm_num [Fin.ext_iff] <;> first | exact he.1 | exact he.2 | exact ho.1 | exact ho.2
  · refine ⟨true, _root_.Bool.true, ?_⟩
    intro i
    fin_cases i <;> simp only [section34SpokeSignPerm, ↓reduceIte,
      Equiv.trans_apply, Equiv.swap_apply_def] <;>
      norm_num [Fin.ext_iff] <;> first | exact he.1 | exact he.2 | exact ho.1 | exact ho.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cell_sign_for_opposite_pairs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_cell_sign_for_opposite_pairs target :: scope.openDecls } }

theorem exists_marked_cell_side_alignment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S₀ S₁ X Y C : Set E} {G : (ℝ × ℝ) × ℝ → E}
    (hG : IsPLHomeomorphOn G spliceCylinder C)
    (hS₀ : G '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ S₀)
    (hS₁ : G '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ S₁)
    (hFX : C ∩ S₀ = C ∩ frontier X) (hFY : C ∩ S₁ = C ∩ frontier Y)
    (hc : G (0, 1 / 2) ∈ interior C)
    (hcross : HasPLCrossingAt S₀ S₁ (G (0, 1 / 2)))
    (hball₀ : ∀ N ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ _root_.Set.InjOn g (Metric.ball c r) ∧
          _root_.Set.MapsTo g (Metric.ball c r) (S₀ ∩ N) ∧ g c = G (0, 1 / 2))
    (hball₁ : ∀ N ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ _root_.Set.InjOn g (Metric.ball c r) ∧
          _root_.Set.MapsTo g (Metric.ball c r) (S₁ ∩ N) ∧ g c = G (0, 1 / 2))
    (hX : IsClosed X) (hY : IsClosed Y)
    (hregX : closure (interior X) = X) (hregY : closure (interior Y) = Y) :
    ∃ H : (ℝ × ℝ) × ℝ → E, IsPLHomeomorphOn H spliceCylinder C ∧
      (∀ t, H (0, t) = G (0, t)) ∧
      (∀ T : Set ℝ, H '' (spliceSquare ×ˢ T) = G '' (spliceSquare ×ˢ T)) ∧
      H '' section34MarkedRibbon 0 = (C ∩ S₀) ∩ Y ∧
      H '' section34MarkedRibbon 2 = (C ∩ S₀) \ interior Y ∧
      H '' section34MarkedRibbon 1 = (C ∩ S₁) ∩ X ∧
      H '' section34MarkedRibbon 3 = (C ∩ S₁) \ interior X := by
  have hcross₀ : HasPLCrossingAt S₀ (frontier Y) (G (0, 1 / 2)) := by
    apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
    filter_upwards [isOpen_interior.mem_nhds hc] with x hx
    exact ⟨fun h => (hFY.subset ⟨interior_subset hx, h⟩).2,
      fun h => (hFY.symm.subset ⟨interior_subset hx, h⟩).2⟩
  have hcross₁ : HasPLCrossingAt S₁ (frontier X) (G (0, 1 / 2)) := by
    apply hcross.symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
    filter_upwards [isOpen_interior.mem_nhds hc] with x hx
    exact ⟨fun h => (hFX.subset ⟨interior_subset hx, h⟩).2,
      fun h => (hFX.symm.subset ⟨interior_subset hx, h⟩).2⟩
  have heven := hcross₀.opposite_marked_cell_ribbon_images hG 0 hS₀
    (hS₁.trans hFY) hc hball₀ hY hregY
  have hodd := hcross₁.opposite_marked_cell_ribbon_images hG 1 hS₁
    ((congrArg (fun Z => G '' Z) (_root_.Set.union_comm _ _)).trans (hS₀.trans hFX))
      hc hball₁ hX hregX
  let P : Fin 4 → Set E := ![(C ∩ S₀) ∩ Y, (C ∩ S₁) ∩ X,
    (C ∩ S₀) \ interior Y, (C ∩ S₁) \ interior X]
  obtain ⟨a, b, hab⟩ := exists_cell_sign_for_opposite_pairs (P := P) heven hodd
  let H := G ∘ section34CellSign a b
  have himage (i : Fin 4) : H '' section34MarkedRibbon i = P i := by
    rw [show H = G ∘ section34CellSign a b from rfl, _root_.Set.image_comp,
      section34_cell_sign_ribbon_image, hab]
  refine ⟨H, (isPLHomeomorphOn_section34_cell_sign a b).trans hG, ?_, ?_,
    himage 0, himage 2, himage 1, himage 3⟩
  · intro t
    exact congrArg G (section34_cell_sign_axis a b t)
  · intro T
    rw [show H = G ∘ section34CellSign a b from rfl, _root_.Set.image_comp,
      section34_cell_sign_face_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_cell_side_alignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_cell_side_alignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_cell_side_alignment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_cell_side_alignment

end DifferentialGeometry.Topology.PiecewiseLinear
