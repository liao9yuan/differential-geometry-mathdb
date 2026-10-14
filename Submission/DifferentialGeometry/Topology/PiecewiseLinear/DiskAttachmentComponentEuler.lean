/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralAttachmentComponents
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (Q : Geometry.SimplicialComplex ℝ F) [Finite Q.faces]
    {D : Set E} {r : (Fin 3 → ℝ) → E} {f : E → F}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hmeet : K.space ∩ D = r '' stdSimplexBoundary 2)
    (hf : IsPLHomeomorphOn f (K.space ∪ D) Q.space) :
    letI (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
      (connectedComponentComplex_faces_finite K c).to_subtype
    letI (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
      (connectedComponentComplex_faces_finite Q c).to_subtype
    ∃ (c₀ : ConnectedComponents K.space) (e : ConnectedComponents K.space ≃
        ConnectedComponents Q.space),
      K.space ∩ D ⊆ (connectedComponentComplex K c₀).space ∧
      (∀ c, IsPLHomeomorphOn f
        ((connectedComponentComplex K c).space ∪ if c = c₀ then D else ∅)
        (connectedComponentComplex Q (e c)).space) ∧
      eulerChar (connectedComponentComplex Q (e c₀)) =
        eulerChar (connectedComponentComplex K c₀) + 1 ∧
      ∀ c, c ≠ c₀ → eulerChar (connectedComponentComplex Q (e c)) =
        eulerChar (connectedComponentComplex K c) := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hG : IsPLSphere 1 (r '' stdSimplexBoundary 2) :=
    hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨c₀, e, hattach, hcomp⟩ :=
    hf.exists_component_equiv_of_connected_attachment K Q hD.isPolyhedron hD.isConnected
      (hmeet.symm ▸ hG.isConnected)
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  refine ⟨c₀, e, hattach, hcomp, ?_, ?_⟩
  · let A := connectedComponentComplex K c₀
    have hAK : A.space ⊆ K.space :=
      (_root_.Set.subset_iUnion (fun c => (connectedComponentComplex K c).space) c₀).trans
        (iUnion_connectedComponentComplex_space K).subset
    have hAD : A.space ∩ D = r '' stdSimplexBoundary 2 := Subset.antisymm
      (fun x hx => hmeet.subset ⟨hAK hx.1, hx.2⟩)
      (fun x hx => ⟨hattach (hmeet.symm.subset hx), (hmeet.symm.subset hx).2⟩)
    obtain ⟨B, hBfin, hBspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    obtain ⟨R, hRfin, hRspace⟩ :=
      ((isPolyhedron_space A).union hD.isPolyhedron).exists_simplicialComplex
    let _ : Finite B.faces := hBfin.to_subtype
    let _ : Finite R.faces := hRfin.to_subtype
    have hχR := eulerChar_eq_add_of_space_union_of_isPLSphere_one R A B
      (by rw [hBspace]; exact hRspace) (by rw [hBspace, hAD]; exact hG)
    have hχB := eulerChar_of_isPLBall B (hBspace.symm ▸ hD)
    have hfR : IsPLHomeomorphOn f R.space (connectedComponentComplex Q (e c₀)).space := by
      rw [hRspace]
      simpa only [A, ↓reduceIte] using hcomp c₀
    have hχQ := eulerChar_eq_of_isPLHomeomorphOn R (connectedComponentComplex Q (e c₀)) hfR
    dsimp only [A] at hχR
    omega
  · intro c hc
    have hfC : IsPLHomeomorphOn f (connectedComponentComplex K c).space
        (connectedComponentComplex Q (e c)).space := by
      simpa only [if_neg hc, _root_.Set.union_empty] using hcomp c
    exact (eulerChar_eq_of_isPLHomeomorphOn (connectedComponentComplex K c)
      (connectedComponentComplex Q (e c)) hfC).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment

end DifferentialGeometry.Topology.PiecewiseLinear
