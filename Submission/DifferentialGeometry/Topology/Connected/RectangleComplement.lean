import Mathlib.Analysis.Complex.Convex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

theorem isConnected_compl_openRectangle (a b c d : ℝ) :
    IsConnected {z : ℂ | z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im} := by
  let L : Set ℂ := {z | z.re ≤ a}
  let R : Set ℂ := {z | b ≤ z.re}
  let B : Set ℂ := {z | z.im ≤ c}
  let T : Set ℂ := {z | d ≤ z.im}
  have hL : IsConnected L := (convex_halfSpace_re_le a).isConnected ⟨⟨a, 0⟩, by simp⟩
  have hR : IsConnected R := (convex_halfSpace_re_ge b).isConnected ⟨⟨b, 0⟩, by simp⟩
  have hB : IsConnected B := (convex_halfSpace_im_le c).isConnected ⟨⟨0, c⟩, by simp⟩
  have hT : IsConnected T := (convex_halfSpace_im_ge d).isConnected ⟨⟨0, d⟩, by simp⟩
  have hLB : IsConnected (L ∪ B) :=
    IsConnected.union ⟨⟨a, c⟩, by simp [L], by simp [B]⟩ hL hB
  have hRT : IsConnected (R ∪ T) :=
    IsConnected.union ⟨⟨b, d⟩, by simp [R], by simp [T]⟩ hR hT
  have hconn : IsConnected ((L ∪ B) ∪ (R ∪ T)) :=
    IsConnected.union ⟨⟨a, d⟩, Or.inl (by simp [L]), Or.inr (by simp [T])⟩ hLB hRT
  convert hconn using 1
  ext z
  change (z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im) ↔
    ((z.re ≤ a ∨ z.im ≤ c) ∨ b ≤ z.re ∨ d ≤ z.im)
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_compl_openRectangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_compl_openRectangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_compl_openRectangle ``Submission.DifferentialGeometry.Topology.isConnected_compl_openRectangle

end DifferentialGeometry.Topology
