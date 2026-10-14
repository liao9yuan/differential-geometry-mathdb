import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredSheetAnnuliActual
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem section34_square_shell_top_frontier {c : ℝ} (hc : 0 ≤ c) :
    (fun p : ℝ × ℝ => section34SquareShellFlatten c (p, c)) ''
      frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        frontier (_root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)) := by
  let η := fun t : ℝ => (1 + 2 * c) * t + -c
  have hη : IsPLHomeomorphOn η (_root_.Set.Icc (0 : ℝ) 1) (_root_.Set.Icc (-c) (1 + c)) :=
    isPLHomeomorphOn_mul_add_Icc (by linarith) (by ring) (by ring)
  have htop (x : ℝ) (hx : 0 ≤ x) : section34SquareShellScalar c x c = η x := by
    unfold section34SquareShellScalar
    rw [max_eq_right (by nlinarith [mul_nonneg hc hx])]
    dsimp only [η]
    ring
  have heq : _root_.Set.EqOn (fun p : ℝ × ℝ => section34SquareShellFlatten c (p, c))
      (Prod.map η η) (frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
    intro p hp
    have hp' := (isClosed_Icc.prod isClosed_Icc).frontier_subset hp
    exact Prod.ext (htop p.1 hp'.1.1) (htop p.2 hp'.2.1)
  exact (_root_.Set.image_congr heq).trans ((hη.prodMap hη).image_frontier rfl
    (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_square_shell_top_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_square_shell_top_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_square_shell_top_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_square_shell_top_frontier

theorem IsCylindricalDiagram.frontier_eq_top_collar
    {R V : Set (EuclideanSpace ℝ (Fin 3))}
    {g H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    {ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    (hH : IsCylindricalDiagram H (_root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)) V)
    (hc : 0 < c)
    (hfront : frontier R = g ''
      (frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hshell : ∀ p ∈ frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1),
      ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, H (section34SquareShellFlatten c (p, c), s) = ρ (g (p, s), c)) :
    frontier V = ρ '' (frontier R ×ˢ {c}) := by
  have hbase : IsPLBall 2 (_root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)) :=
    isPLBall_two_prod (isPLBall_Icc (by linarith)) (isPLBall_Icc (by linarith))
  rw [hH.frontier_eq_image_base_frontier hbase (by simp) (by simp)]
  apply Subset.antisymm
  · rintro _ ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (section34_square_shell_top_frontier hc.le).symm.subset hq
    exact ⟨(g (p, s), c), ⟨hfront.symm.subset ⟨(p, s), ⟨hp, hs⟩, rfl⟩, rfl⟩,
      (hshell p hp s hs).symm⟩
  · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    change t = c at ht
    subst t
    obtain ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩ := hfront.subset hx
    exact ⟨(section34SquareShellFlatten c (p, c), s),
      ⟨(section34_square_shell_top_frontier hc.le).subset (_root_.Set.mem_image_of_mem _ hp), hs⟩,
      hshell p hp s hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.frontier_eq_top_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.frontier_eq_top_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.frontier_eq_top_collar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.frontier_eq_top_collar

theorem inter_frontier_of_image_trace
    {E M : Type*} [TopologicalSpace E] {u : E → M} {P V X K : Set E} {A : Set M}
    (hu : _root_.Set.InjOn u P) (hV : IsClosed V) (hVP : V ⊆ P) (hXP : X ⊆ P) (hKP : K ⊆ P)
    (hX : u '' X = u '' V ∩ A) (hK : u '' K = u '' frontier V ∩ A) :
    X ∩ frontier V = K := by
  apply (hu.image_eq_image_iff (inter_subset_left.trans hXP) hKP).mp
  rw [hu.image_inter hXP (hV.frontier_subset.trans hVP), hX, hK]
  ext y
  have hs : u '' frontier V ⊆ u '' V := _root_.Set.image_mono hV.frontier_subset
  simp only [_root_.Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hs h.1, h.2⟩, h.1⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_of_image_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_of_image_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_of_image_trace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_of_image_trace

end DifferentialGeometry.Topology.PiecewiseLinear
