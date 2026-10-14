import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.Germ
import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Metric
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }

private def sphereProductLineDiffeomorph (d : ℝ ≃ₘ[ℝ] ℝ) :
    SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
  (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr d

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.sphereProductLineDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.sphereProductLineDiffeomorph target :: scope.openDecls } }

theorem exists_supported_cylinder_compression {r R ε : ℝ}
    (hr : 0 < r) (hrR : r < R) (hε : 0 < ε) :
    ∃ C : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ p : SphereCylinder, |p.2| ≤ r → |(C p).2| < ε) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo (-R) R ∧
        EqOn C id Kᶜ ∧ _root_.Set.EqOn C.symm id Kᶜ := by
  let R' := (r + R) / 2
  have hrR' : r < R' := by dsimp only [R']; linarith
  have hR'R : R' < R := by dsimp only [R']; linarith
  obtain ⟨D, _, _, _, _, hshrink, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_flow_contracting_closedBall (E := ℝ) hr hrR'
  let T := _root_.Max.max 0 (Real.log (r / ε)) + 1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hsmall : Real.exp (-T) * r < ε := by
    have hlog : Real.log (r / ε) < T := by dsimp only [T]; linarith [le_max_right 0 (Real.log (r / ε))]
    have hexp : r / ε < Real.exp T := by rwa [← Real.log_lt_iff_lt_exp (div_pos hr hε)]
    rw [Real.exp_neg]
    apply (inv_mul_lt_iff₀ (Real.exp_pos T)).mpr
    nlinarith [(div_lt_iff₀ hε).mp hexp]
  let C := sphereProductLineDiffeomorph (D T)
  refine ⟨C, ?_, _root_.Set.univ ×ˢ _root_.Set.Icc (-R') R', isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc,
    ?_, ?_, ?_⟩
  · intro p hp
    change |D T p.2| < ε
    rw [hshrink T p.2 hT (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hp),
      smul_eq_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_lt hsmall
  · rintro p ⟨_, hp⟩
    exact ⟨mem_univ _, by linarith [hp.1], by linarith [hp.2]⟩
  · intro p hp
    have hnot : p.2 ∉ _root_.Metric.closedBall (0 : ℝ) R' := by
      intro hx
      exact hp ⟨mem_univ _, (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).1,
        (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).2⟩
    exact Prod.ext rfl (hfix T p.2 hnot).1
  · intro p hp
    have hnot : p.2 ∉ _root_.Metric.closedBall (0 : ℝ) R' := by
      intro hx
      exact hp ⟨mem_univ _, (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).1,
        (abs_le.mp (by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using hx)).2⟩
    exact Prod.ext rfl (hfix T p.2 hnot).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_cylinder_compression then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_cylinder_compression"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_cylinder_compression ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_cylinder_compression

end DifferentialGeometry.Topology.Manifold
