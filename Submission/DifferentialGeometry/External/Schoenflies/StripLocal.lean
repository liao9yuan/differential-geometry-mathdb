/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.StripConstants
import Submission.DifferentialGeometry.External.Schoenflies.StripConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The local two-sidedness assertion of Lemma 1.8

`Schoenflies/Strip.lean`, `Schoenflies/StripConstants.lean` and `Schoenflies/StripConnected.lean`
build the collar of a simple closed polygon and prove the *global* half of Lemma 1.8 (a): the
collar minus the curve is the disjoint union of two connected open sets. This module adds the
*local* half, the sentence of the blueprint that begins "In either case the two sets `N_L`, `N_R`
are the two local sides of the curve in the following precise sense".

Two statements come out of it, and they are the two the polygonal Jordan curve theorem consumes.

* `Schoenflies.StripData.local_two_sided` and its packaging
  `Schoenflies.StripData.exists_reference_points`: a small enough disk about a point of the
  *relative interior* of an edge meets the polygon exactly in that edge, and the rest of the disk
  is the two open half-disks, one in each side. This is what supplies the two reference points
  `z_L`, `z_R` of the parity argument, together with the fact that they are separated by a single
  crossing of the curve.
* `Schoenflies.StripData.carrier_subset_closure_sideL` and `…_sideR`: every point of the polygon
  is in the closure of both sides. With `StripData.sideL_disjoint_carrier` this says the polygon
  is contained in the boundary of each side, which is what turns "there are exactly two regions"
  into "both regions have boundary `C`".

## What is proved, and how

The disk argument along an edge is `StripData.core_ball_trichotomy`: both frame coordinates are
`1`-Lipschitz, so a ball of radius at most `min lam rho` about a point of the middle stretch of
an edge cannot leave the block range in the longitudinal coordinate nor the block width in the
transverse one; the sign of the transverse coordinate then reads off which of the three pieces —
left block, edge, right block — the point is in.

Approaching a point of the polygon from a given side is `StripData.exists_near_sides`. Away from
the vertices the block does it. Near a vertex the block is not available (it stops short by
`lam`), and the approach is through the *sector*, reached by shrinking the transverse offset with
the longitudinal one held fixed: the germ lemmas `ClosedPolygon.off_sub_mem_arcL_start` and
friends need only that the offset be small against the progress, so at a point at distance `t > 0`
from the vertex any offset below `t · |det| / (1 + |⟪·,·⟫|)` works. At the vertex itself neither
is available and the approach is instead by shrinking a point of the sector towards the vertex,
which stays in the sector because an arc of directions is a cone (`Plane.smul_mem_arcCCW`).

## Blueprint

* `Schoenflies.StripData.local_two_sided`, `Schoenflies.StripData.exists_reference_points` —
  Lemma 1.8, the local two-sidedness assertion, along the relative interior of an edge.
* `Schoenflies.StripData.carrier_subset_closure_sideL`, `…_sideR` — the consequence of it used
  for "both regions have boundary `C`".
* `Schoenflies.ClosedPolygon.exists_two_sided_collar` — Lemma 1.8 (a) with those two clauses
  added, in existential form.

The local two-sidedness assertion *at a vertex* is not proved here; see the module note at the
end.
-/

open _root_.Metric _root_.Set

namespace Schoenflies

namespace Plane

variable {u w : Plane}

/-- The origin is on no arc: the arcs are open arcs of *directions*. -/
theorem zero_notMem_arcCCW (u w : Plane) : (0 : Plane) ∉ arcCCW u w := by
  have h := (notMem_arcCCW_smul u w (le_refl (0 : ℝ))).1
  rwa [zero_smul] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.Plane.zero_notMem_arcCCW then
    throwError "Refusing to shadow existing declaration Schoenflies.Plane.zero_notMem_arcCCW"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.Plane.zero_notMem_arcCCW ``Submission.Schoenflies.Plane.zero_notMem_arcCCW

end Plane

open _root_.Submission.Schoenflies.Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {t s : ℝ}

/-- Seen from the vertex it arrives at, a frame position of edge `i` is a germ at the incoming
ray there. This is the companion of `ClosedPolygon.off_sub_vertex`, which does the same at the
vertex the edge leaves. -/
theorem off_sub_vertex_succ_ray : P.off i t s - P.vertex (i + 1) =
    (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
  have hr : P.rayIn (i + 1) = -P.tang i := rayIn_succ
  have hp : perp (-P.tang i) = -perp (P.tang i) := by ext k; fin_cases k <;> simp [perp]
  rw [off_sub_vertex_succ, hr, hp]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.off_sub_vertex_succ_ray then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.off_sub_vertex_succ_ray"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.off_sub_vertex_succ_ray ``Submission.Schoenflies.ClosedPolygon.off_sub_vertex_succ_ray

/-! ### The four germs, for an arbitrary frame position

`StripData.blockL_sub_mem_arcL_start` and its three companions apply `Plane.germs_split'` to a
point of a *block*, where the smallness of the offset comes from the `germ` field of the
`StripData`. The four lemmas here are the same projections with the smallness left as a
hypothesis, which is what an approach to a point of the curve needs: there the progress `t` is
fixed by the point being approached and only the offset shrinks. -/

theorem off_sub_mem_arcL_start (hs : 0 < s)
    (hsm : s * |_root_.Inner.inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  rw [off_sub_vertex]
  exact (germs_split' det_rays_ne_zero hs hsm).1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.off_sub_mem_arcL_start then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.off_sub_mem_arcL_start"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.off_sub_mem_arcL_start ``Submission.Schoenflies.ClosedPolygon.off_sub_mem_arcL_start

theorem off_sub_mem_arcR_start (hs : s < 0)
    (hsm : (-s) * |_root_.Inner.inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  have h : P.off i t s - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.off_sub_mem_arcR_start then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.off_sub_mem_arcR_start"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.off_sub_mem_arcR_start ``Submission.Schoenflies.ClosedPolygon.off_sub_mem_arcR_start

theorem off_sub_mem_arcL_finish (hs : 0 < s)
    (hsm : s * |_root_.Inner.inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' det_rays_ne_zero hs hsm).1.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.off_sub_mem_arcL_finish then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.off_sub_mem_arcL_finish"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.off_sub_mem_arcL_finish ``Submission.Schoenflies.ClosedPolygon.off_sub_mem_arcL_finish

theorem off_sub_mem_arcR_finish (hs : s < 0)
    (hsm : (-s) * |_root_.Inner.inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  have h : P.off i t s - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.off_sub_mem_arcR_finish then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.off_sub_mem_arcR_finish"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.off_sub_mem_arcR_finish ``Submission.Schoenflies.ClosedPolygon.off_sub_mem_arcR_finish

/-- Offsetting a point of an edge moves it exactly the offset. -/
theorem dist_off_pt : _root_.Dist.dist (P.off i t s) (P.pt i t) = |s| := by
  rw [ClosedPolygon.pt, dist_eq_norm, show P.off i t s - P.off i t 0 = s • perp (P.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.dist_off_pt then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.dist_off_pt"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.dist_off_pt ``Submission.Schoenflies.ClosedPolygon.dist_off_pt

end ClosedPolygon

/-- One positive number below several prescribed thresholds at once. Used to offset a point of an
edge by less than the germ threshold at both of its endpoints, less than the block half-width and
less than a prescribed accuracy. -/
private theorem exists_common_bound {a b X₁ X₂ K₁ K₂ Y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hY : 0 < Y) :
    ∃ σ : ℝ, 0 < σ ∧ σ < a ∧ σ < b ∧ σ * K₁ ≤ X₁ ∧ σ * K₂ ≤ X₂ ∧ σ < Y := by
  refine ⟨min (_root_.Min.min (a / 2) (b / 2)) (_root_.Min.min (_root_.Min.min (X₁ / K₁) (X₂ / K₂)) (Y / 2)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_min_iff, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨div_pos hX₁ hK₁, div_pos hX₂ hK₂⟩, by linarith⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : _root_.Min.min (_root_.Min.min (a / 2) (b / 2)) (_root_.Min.min (_root_.Min.min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₁ / K₁ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₁.le
    rwa [div_mul_cancel₀ _ hK₁.ne'] at h2
  · have h : _root_.Min.min (_root_.Min.min (a / 2) (b / 2)) (_root_.Min.min (_root_.Min.min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₂ / K₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₂.le
    rwa [div_mul_cancel₀ _ hK₂.ne'] at h2
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)

run_cmd do
  let target := ``Submission.Schoenflies.exists_common_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.exists_common_bound target :: scope.openDecls } }

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i : ZMod (m + 3)}

/-! ### The disk about a point in the middle of an edge -/

/-- **The local picture along an edge.** A ball of radius at most `min lam rho` about a point of
the middle stretch of an edge is split by the sign of the transverse coordinate: positive is the
left block, negative the right block, zero the edge itself. Both coordinates are `1`-Lipschitz,
which is the whole proof. -/
theorem core_ball_trichotomy {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hη : η ≤ _root_.Min.min D.lam D.rho) {y : Plane} (hy0 : y ∈ _root_.Metric.ball (P.pt i c) η) :
    (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.blockL i) ∧
      (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.blockR i) ∧
      (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
  have hy : _root_.Dist.dist y (P.pt i c) < _root_.Min.min D.lam D.rho := lt_of_lt_of_le (mem_ball.1 hy0) hη
  set t := coordAlong (P.vertex i) (P.tang i) y with ht
  set σ := coordAcross (P.vertex i) (P.tang i) y with hσ
  have hyeq : y = P.off i t σ := ClosedPolygon.off_coord P i y
  have hpt : P.pt i c = P.off i c 0 := rfl
  have hta : |t - c| ≤ _root_.Dist.dist y (P.pt i c) := by
    have h := abs_coordAlong_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAlong_off] at h
    exact h
  have hsa : |σ| ≤ _root_.Dist.dist y (P.pt i c) := by
    have h := abs_coordAcross_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAcross_off, sub_zero] at h
    exact h
  have hlam : _root_.Dist.dist y (P.pt i c) < D.lam := lt_of_lt_of_le hy (min_le_left _ _)
  have hrho : _root_.Dist.dist y (P.pt i c) < D.rho := lt_of_lt_of_le hy (min_le_right _ _)
  have htlow : D.lam < t := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.1]
  have hthigh : t < P.len i - D.lam := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.2]
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · rw [hyeq]
    exact D.mem_blockL_off.2 ⟨htlow, hthigh, hs, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.2]⟩
  · rw [hyeq]
    exact D.mem_blockR_off.2 ⟨htlow, hthigh, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.1], hs⟩
  · rw [hyeq, hs, ← ClosedPolygon.pt]
    exact ClosedPolygon.pt_mem_edge ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.core_ball_trichotomy then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.core_ball_trichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.core_ball_trichotomy ``Submission.Schoenflies.StripData.core_ball_trichotomy

/-- **Local two-sidedness at an interior point of an edge.** A small enough disk about a point in
the middle stretch of an edge meets the polygon exactly in that edge; off the edge the disk lies
in the two blocks, one on each side; and both sides are met, at the two points obtained by
offsetting the centre. -/
theorem local_two_sided {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hηpos : 0 < η) (hη : η ≤ _root_.Min.min D.lam D.rho) :
    _root_.Metric.ball (P.pt i c) η ∩ P.carrier ⊆ P.edge i ∧
      (∀ y ∈ _root_.Metric.ball (P.pt i c) η, y ∉ P.carrier →
        (0 < coordAcross (P.vertex i) (P.tang i) y ∧ y ∈ D.sideL) ∨
          (coordAcross (P.vertex i) (P.tang i) y < 0 ∧ y ∈ D.sideR)) ∧
      P.off i c (η / 2) ∈ _root_.Metric.ball (P.pt i c) η ∩ D.sideL ∧
      P.off i c (-(η / 2)) ∈ _root_.Metric.ball (P.pt i c) η ∩ D.sideR := by
  have hsplit : ∀ y ∈ _root_.Metric.ball (P.pt i c) η,
      (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.sideL) ∧
        (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.sideR) ∧
        (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
    intro y hy
    obtain ⟨hL, hR, hE⟩ := D.core_ball_trichotomy h1 h2 hη hy
    exact ⟨fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hL hs)⟩,
      fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hR hs)⟩, hE⟩
  have hball : ∀ σ : ℝ, |σ| < η → P.off i c σ ∈ _root_.Metric.ball (P.pt i c) η := by
    intro σ hσ
    rw [_root_.Metric.mem_ball, ClosedPolygon.dist_off_pt]
    exact hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyc⟩
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideR_disjoint_carrier ((hsplit y hy).2.1 hs))
    · exact (hsplit y hy).2.2 hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideL_disjoint_carrier ((hsplit y hy).1 hs))
  · intro y hy hyc
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact Or.inr ⟨hs, (hsplit y hy).2.1 hs⟩
    · exact absurd (ClosedPolygon.edge_subset_carrier ((hsplit y hy).2.2 hs)) hyc
    · exact Or.inl ⟨hs, (hsplit y hy).1 hs⟩
  · have hmem := hball (η / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith
  · have hmem := hball (-(η / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).2.1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.local_two_sided then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.local_two_sided"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.local_two_sided ``Submission.Schoenflies.StripData.local_two_sided

/-- **The two reference points of the parity argument.** On every edge there is a disk that meets
the polygon only in that edge and contains a point of each side, on the two sides of the edge's
line. A horizontal segment joining the two crosses the polygon exactly once, which is what makes
the two reference points have opposite parity. -/
theorem exists_reference_points (i : ZMod (m + 3)) :
    ∃ (p : Plane) (η : ℝ), 0 < η ∧ p ∈ P.edge i ∧ _root_.Metric.ball p η ∩ P.carrier ⊆ P.edge i ∧
      (∃ zL ∈ _root_.Metric.ball p η, zL ∈ D.sideL ∧ 0 < coordAcross (P.vertex i) (P.tang i) zL) ∧
      (∃ zR ∈ _root_.Metric.ball p η, zR ∈ D.sideR ∧ coordAcross (P.vertex i) (P.tang i) zR < 0) := by
  have h4 := D.four_lam_lt_len i
  have hl := D.lam_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < _root_.Min.min D.lam D.rho := lt_min hl D.rho_pos
  obtain ⟨h1, -, ⟨hbL, hsL⟩, ⟨hbR, hsR⟩⟩ :=
    D.local_two_sided (i := i) hlow hhigh hηpos (le_refl _)
  refine ⟨P.pt i (P.len i / 2), _root_.Min.min D.lam D.rho, hηpos,
    ClosedPolygon.pt_mem_edge ⟨by linarith, by linarith⟩, h1, ⟨_, hbL, hsL, ?_⟩,
    ⟨_, hbR, hsR, ?_⟩⟩
  · rw [ClosedPolygon.coordAcross_off]; linarith
  · rw [ClosedPolygon.coordAcross_off]; linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.exists_reference_points then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.exists_reference_points"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.exists_reference_points ``Submission.Schoenflies.StripData.exists_reference_points

/-! ### Every point of the polygon is on the boundary of both sides -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex, which
stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorL i, _root_.Dist.dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorL (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_ofPred_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [_root_.Metric.mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.exists_near_sectorL then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.exists_near_sectorL"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.exists_near_sectorL ``Submission.Schoenflies.StripData.exists_near_sectorL

theorem exists_near_sectorR {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorR i, _root_.Dist.dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorR (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (_root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_ofPred_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [_root_.Metric.mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : _root_.Min.min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.exists_near_sectorR then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.exists_near_sectorR"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.exists_near_sectorR ``Submission.Schoenflies.StripData.exists_near_sectorR

/-- **Both sides come arbitrarily close to every point of the polygon.** Away from the vertices
this is the block; at a vertex it is `exists_near_sectorL`; in between it is the germ with the
progress held fixed and the offset shrunk below the corner's threshold. -/
theorem exists_near_sides {x : Plane} (hx : x ∈ P.carrier) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ D.sideL, _root_.Dist.dist x y < ε) ∧ (∃ y ∈ D.sideR, _root_.Dist.dist x y < ε) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := ClosedPolygon.mem_edge_iff.1 hi
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex
    rw [← hc0', ClosedPolygon.pt_zero]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε i
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε i
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex
    rw [hc1', ClosedPolygon.pt_len]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε (i + 1)
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε (i + 1)
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i + 1, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i + 1, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  -- an interior point of the edge: offset it, by less than every threshold at once
  have hL₁ : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hL₂ : 0 < |det (P.rayIn (i + 1)) (P.tang (i + 1))| :=
    abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hK₁ : (0 : ℝ) < 1 + |_root_.Inner.inner ℝ (P.rayIn i) (P.tang i)| := by positivity
  have hK₂ : (0 : ℝ) < 1 + |_root_.Inner.inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| := by positivity
  have hRlam : D.lam < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]
  obtain ⟨σ, hσpos, hσε, hσrho, hσ1, hσ2, hσR⟩ := exists_common_bound hε D.rho_pos
    (mul_pos hc0' hL₁) (mul_pos (show (0:ℝ) < P.len i - c by linarith) hL₂) hK₁ hK₂
    (show (0:ℝ) < D.R - D.lam by linarith)
  have hg1 : σ * |_root_.Inner.inner ℝ (P.rayIn i) (P.tang i)| < c * |det (P.rayIn i) (P.tang i)| := by
    nlinarith
  have hg2 : σ * |_root_.Inner.inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - c) * |det (P.rayIn (i + 1)) (P.tang (i + 1))| := by nlinarith
  have hdistL : _root_.Dist.dist (P.pt i c) (P.off i c σ) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_pos hσpos]; linarith
  have hdistR : _root_.Dist.dist (P.pt i c) (P.off i c (-σ)) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  by_cases hmid : D.lam < c ∧ c < P.len i - D.lam
  · -- the block does it
    exact ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩)⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩)⟩, hdistR⟩⟩
  push Not at hmid
  by_cases hnear : c ≤ D.lam
  · -- near the initial vertex: the sector there, reached by the germ
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → _root_.Dist.dist (P.off i c τ) (P.vertex i) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_start hσpos hg1,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_start (by linarith) (by rw [neg_neg]; exact hg1),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩
  · -- near the terminal vertex
    push Not at hnear
    have hfar : P.len i - c ≤ D.lam := by have h := hmid hnear; linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → _root_.Dist.dist (P.off i c τ) (P.vertex (i + 1)) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_succ_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < P.len i - c)] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_finish hσpos hg2,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_finish (by linarith) (by rw [neg_neg]; exact hg2),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.exists_near_sides then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.exists_near_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.exists_near_sides ``Submission.Schoenflies.StripData.exists_near_sides

/-- Every point of the polygon is in the closure of the left side. With
`StripData.sideL_disjoint_carrier` this says the polygon is contained in the boundary of the left
side. -/
theorem carrier_subset_closure_sideL : P.carrier ⊆ closure D.sideL := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨y, hy, hd⟩, -⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.carrier_subset_closure_sideL then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.carrier_subset_closure_sideL"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.carrier_subset_closure_sideL ``Submission.Schoenflies.StripData.carrier_subset_closure_sideL

theorem carrier_subset_closure_sideR : P.carrier ⊆ closure D.sideR := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨y, hy, hd⟩⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.StripData.carrier_subset_closure_sideR then
    throwError "Refusing to shadow existing declaration Schoenflies.StripData.carrier_subset_closure_sideR"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.StripData.carrier_subset_closure_sideR ``Submission.Schoenflies.StripData.carrier_subset_closure_sideR

end StripData

/-- **Lemma 1.8 (a), with the boundary clause.** A simple closed polygon has an open neighbourhood
`N`, inside any prescribed open set containing it, whose complement in `N` is the disjoint union
of two connected open sets, each of which has the polygon in its closure. -/
theorem ClosedPolygon.exists_two_sided_collar (P : ClosedPolygon m) {U : Set Plane}
    (hU : IsOpen U) (hPU : P.carrier ⊆ U) :
    ∃ N NL NR : Set Plane, IsOpen N ∧ P.carrier ⊆ N ∧ N ⊆ U ∧ IsOpen NL ∧ IsOpen NR ∧
      IsConnected NL ∧ IsConnected NR ∧ Disjoint NL NR ∧ N \ P.carrier = NL ∪ NR ∧
      P.carrier ⊆ closure NL ∧ P.carrier ⊆ closure NR := by
  obtain ⟨D, hD⟩ := exists_stripData_subset P hU hPU
  exact ⟨D.nbhd, D.sideL, D.sideR, D.isOpen_nbhd, D.carrier_subset_nbhd, hD, D.isOpen_sideL,
    D.isOpen_sideR, D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR,
    D.nbhd_diff_carrier, D.carrier_subset_closure_sideL, D.carrier_subset_closure_sideR⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ClosedPolygon.exists_two_sided_collar then
    throwError "Refusing to shadow existing declaration Schoenflies.ClosedPolygon.exists_two_sided_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ClosedPolygon.exists_two_sided_collar ``Submission.Schoenflies.ClosedPolygon.exists_two_sided_collar

/-!
## What is still missing from Lemma 1.8

Two things.

* The local two-sidedness assertion *at a vertex*. `StripData.ball_diff_carrier_subset` already
  says that a ball of radius `R` about a vertex minus the polygon lies in the two sectors there,
  and `StripData.sectorL_disjoint_sectorR` (through `sideL_disjoint_sideR`) says those are
  disjoint; what is not proved is that each of the two intersections
  `ball (P.vertex i) η ∩ sectorL i` is *connected*, i.e. that the ball minus the curve has
  exactly two components at a vertex rather than merely being covered by two disjoint open sets.
  For a ball of radius `η ≤ R` this is true and the proof is the one in
  `Plane.isConnected_arcCCW_ball`, since `ball (P.vertex i) η ∩ sectorL i = cone (P.vertex i) A η`
  for the same arc `A`. Nothing in the polygonal Jordan curve theorem needs it.
* Lemma 1.8 (b), the case of a polygonal *arc* with a compact subarc of its interior. The blocks
  and sectors here are built from a cyclic vertex family; the arc case needs the same
  construction along a linear chain, with the two end cross-sections and no cap. None of it is
  formalised.
-/

end Schoenflies
