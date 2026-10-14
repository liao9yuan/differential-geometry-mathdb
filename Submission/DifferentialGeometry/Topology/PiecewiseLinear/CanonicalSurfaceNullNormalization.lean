/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceSplit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def towerWindowSupport (S' : ℤ → Set E3) (window : Finset ℤ) : Set E3 :=
  ⋃ i ∈ window, interior (S' (2 * i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.towerWindowSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.towerWindowSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.towerWindowSupport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.towerWindowSupport

theorem IsCanonicalNullSplit.outside_window {S' T : ℤ → Set E3} {i : ℤ}
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} (hstep : IsCanonicalNullSplit S' T i X Y)
    {window : Finset ℤ} (hi : i ∈ window) (j : ℤ) :
    (Y j).space \ towerWindowSupport S' window = (X j).space \ towerWindowSupport S' window := by
  have hsub : interior (S' (2 * i)) ⊆ towerWindowSupport S' window :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  ext x
  exact ⟨fun hx => ⟨((hstep.outside j).subset ⟨hx.1, fun hO => hx.2 (hsub hO)⟩).1, hx.2⟩,
    fun hx => ⟨((hstep.outside j).symm.subset ⟨hx.1, fun hO => hx.2 (hsub hO)⟩).1, hx.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalNullSplit.outside_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalNullSplit.outside_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalNullSplit.outside_window ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalNullSplit.outside_window

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open _root_.Classical in
theorem IsCanonicalSurface.exists_window_null_normalization [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3)) (h303 : Moise303)
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (window : Finset ℤ) {F : Set E3}
    (hFO : ∀ i ∈ window, Disjoint F (interior (φ '' S (2 * i)))) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalSurface Y (fun j => φ '' S j) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
      windowNullRank Y T'' window = 0 ∧
      Relation.ReflTransGen (fun U V =>
        IsCanonicalSurface U (fun j => φ '' S j) T''
          (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
        IsCanonicalSurface V (fun j => φ '' S j) T''
          (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
        ∃ i ∈ window, IsCanonicalNullSplit (fun j => φ '' S j) T'' i U V) X Y ∧
      (∀ j, (Y j).space \ towerWindowSupport (fun k => φ '' S k) window =
        (X j).space \ towerWindowSupport (fun k => φ '' S k) window) ∧
      towerSurface T'' (fun j => (Y j).space) P' ∩ F =
        towerSurface T'' (fun j => (X j).space) P' ∩ F := by
  induction hn : windowNullRank X T'' window using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hz : n = 0
    · exact ⟨X, hX, hn.trans hz, Relation.ReflTransGen.refl, fun _ => rfl, rfl⟩
    · have hpos : 0 < windowNullRank X T'' window := hn ▸ Nat.pos_of_ne_zero hz
      obtain ⟨i, hi, G, hG, hbound⟩ := (hX.windowNullRank_pos_iff window).mp hpos
      obtain ⟨X₁, hX₁, hstep, hprot⟩ :=
        IsCanonicalSurface.exists_null_seam_split ht hu hv huv he htw havoid h303 hX i
          (hFO i hi) ⟨G, hG, hbound⟩
      have hlt : windowNullRank X₁ T'' window < n :=
        hn ▸ IsCanonicalNullSplit.windowNullRank_lt htw hstep hi
      obtain ⟨Y, hY, hzero, hpath, hout, hfix⟩ :=
        ih (windowNullRank X₁ T'' window) hlt hX₁ rfl
      refine ⟨Y, hY, hzero, ?_, fun j => (hout j).trans (hstep.outside_window hi j),
        hfix.trans hprot.2⟩
      apply Relation.ReflTransGen.trans ?_ hpath
      exact Relation.ReflTransGen.single ⟨hX, hX₁, i, hi, hstep⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.exists_window_null_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.exists_window_null_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.exists_window_null_normalization ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.exists_window_null_normalization

end DifferentialGeometry.Topology.PiecewiseLinear
