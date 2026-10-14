import Submission.DifferentialGeometry.Topology.Planar.RoundingIsotopy
import Submission.DifferentialGeometry.Topology.Planar.VertexRoundingFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Planar

private theorem periodic_sample_eq_zmod_val {E : Type*} {γ : ℝ → E}
    (hp : Function.Periodic γ 1) {n : ℕ} [NeZero n] (k : ℤ) :
    γ ((k : ℝ) / n) = γ (((k : ZMod n).val : ℝ) / n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hval : (((k : ZMod n).val : ℕ) : ℝ) = (k % (n : ℤ) : ℤ) := by
    exact_mod_cast ZMod.val_intCast k
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) (Int.emod_add_mul_ediv k (n : ℤ))
  push_cast at hcast
  have heq : (k : ℝ) / n = ((k : ZMod n).val : ℝ) / n + ((k / (n : ℤ) : ℤ) : ℝ) := by
    rw [hval]
    field_simp
    nlinarith [hcast]
  rw [heq]
  simpa only [mul_one] using hp.int_mul (k / (n : ℤ)) (((k : ZMod n).val : ℝ) / n)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Planar.periodic_sample_eq_zmod_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Planar.periodic_sample_eq_zmod_val target :: scope.openDecls } }

theorem exists_diffeomorph_finite_vertex_rounding
    {f : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ f) :
    ∃ (m : ℕ) (P : Schoenflies.PrePolygon m)
      (e : ZMod (m + 3) → Schoenflies.Plane ≃ᵃ[ℝ] Schoenflies.Plane)
      (U : ZMod (m + 3) → Set Schoenflies.Plane)
      (r d s R : ZMod (m + 3) → ℝ) (ε : ℝ)
      (φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane),
      (∀ i, P.vertex i = f (((i.val : ℝ) / (m + 3) : ℝ) : AddCircle (1 : ℝ))) ∧
      (∀ i, 0 < r i ∧ e i (P.vertex (i - 1)) = Schoenflies.Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Schoenflies.Plane.mk (r i) (d i * r i) ∧ e i (P.vertex i) = 0) ∧
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ (d i = 0 ∨ d i = 1) ∧
        (s i = -1 ∨ s i = 1) ∧
        ∀ p ∈ U i, p ∈ closure (Schoenflies.inside P.carrier) ↔
          0 ≤ s i * ((e i p) 1 - d i * _root_.Max.max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, e i ⁻¹' _root_.Metric.closedBall (0 : Schoenflies.Plane) (R i) ⊆ U i) ∧
      0 < ε ∧ (∀ i, 3 * ε < R i) ∧
      let D := closure (Schoenflies.inside P.carrier)
      let D' := (D \ ⋃ i, e i ⁻¹' _root_.Metric.ball (0 : Schoenflies.Plane) (R i)) ∪
        ⋃ i, (e i ⁻¹' _root_.Metric.closedBall (0 : Schoenflies.Plane) (R i)) ∩
          {p | 0 ≤ s i * ((e i p) 1 - d i * Real.smoothMax ε ((e i p) 0) 0)}
      IsCompact D' ∧ φ '' _root_.Set.range f = frontier D' ∧
      ∃ S : Set Schoenflies.Plane, IsCompact S ∧ _root_.Set.EqOn φ id Sᶜ ∧ _root_.Set.EqOn φ.symm id Sᶜ := by
  obtain ⟨m, P, _, hp, hround⟩ := exists_inscribed_rounding_diffeomorph_forall_width hf zero_lt_one
  let h : ℝ := 1 / (m + 3 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨e, U, r, d, s, R, δ, hnorm, hU, hdisj, hKU, hδ, hfront⟩ :=
    P.exists_finite_vertex_roundings_frontier hh
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  obtain ⟨hεhalf, hεR, hD, hboundary⟩ := hfront ε ⟨hε, half_lt_self hδ⟩
  obtain ⟨φ, hφ, S, hS, hfix, hfixi⟩ := hround (h * ε) ⟨mul_pos hh hε, by nlinarith⟩
  let γ : ℝ → Schoenflies.Plane := fun t => f (t : AddCircle (1 : ℝ))
  have hper : Function.Periodic γ 1 := by
    intro t
    simp only [γ, QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]
  have hsample : (fun k : ℤ => f ((k * h : ℝ) : AddCircle (1 : ℝ))) =
      fun k : ℤ => P.vertex k := by
    funext k
    rw [hp]
    change γ ((k : ℝ) * (1 / (m + 3 : ℝ))) = γ _
    rw [mul_one_div]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      periodic_sample_eq_zmod_val hper (n := m + 3) k
  have hmatch (t : ℝ) : φ (f (t : AddCircle (1 : ℝ))) =
      DifferentialGeometry.Analysis.roundedPolygonalCurve h (h * ε) (fun k : ℤ => P.vertex k) t := by
    have ht := hφ t
    change φ (f (t : AddCircle (1 : ℝ))) =
      DifferentialGeometry.Analysis.roundedPolygonalCurve h (h * ε)
        (fun k : ℤ => f ((k * h : ℝ) : AddCircle (1 : ℝ))) t at ht
    simpa only [hsample] using ht
  refine ⟨m, P, e, U, r, d, s, R, ε, φ, hp, hnorm, hU, hdisj, hKU, hε, hεR,
    hD, ?_, S, hS, hfix, hfixi⟩
  rw [← hboundary]
  ext p
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    let t : ℝ := AddCircle.equivIco 1 0 z
    have ht : (t : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
    refine ⟨t, ?_⟩
    rw [← hmatch, ht]
  · rintro ⟨t, rfl⟩
    exact ⟨f (t : AddCircle (1 : ℝ)), _root_.Set.mem_range_self _, hmatch t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Planar.exists_diffeomorph_finite_vertex_rounding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Planar.exists_diffeomorph_finite_vertex_rounding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Planar.exists_diffeomorph_finite_vertex_rounding ``Submission.DifferentialGeometry.Topology.Planar.exists_diffeomorph_finite_vertex_rounding

end DifferentialGeometry.Topology.Planar
