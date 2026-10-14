import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.NormalDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }

theorem exists_supported_collar_extension_of_positive_axial_derivative
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, A (p, 0) = (η p, 0))
    (hpos : ∀ p : S2, 0 < deriv (fun t => (A (p, t)).2) 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → q ∈ A.source ∧ F q = A q) ∧
      (∀ p : S2, F (p, 0) = (η p, 0)) ∧
      (∀ q : SphereCylinder, q.2 ≤ l ∨ u ≤ q.2 → F q = q ∧ F.symm q = q) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u ∧
        EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  obtain ⟨R, hR, hRband, hRs, hRi, hRside⟩ :=
    exists_uniform_cylinder_width_of_positive_axial_derivative A hsource
      (fun p => congrArg Prod.snd (hzero p)) hpos l u hl hu
  let U : Set SphereCylinder := _root_.Set.univ ×ˢ _root_.Set.Ioo (-R) R
  let B := DifferentialGeometry.Topology.PartialDiffeomorph.restrict A U (isOpen_univ.prod isOpen_Ioo)
  have hBs : _root_.Set.univ ×ˢ _root_.Set.Icc (-(R / 2)) (R / 2) ⊆ B.source := by
    rintro q ⟨_, hq⟩
    have hqR : q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R := ⟨mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩
    exact ⟨hRs hqR, _root_.Set.mem_univ _, by linarith [hq.1], by linarith [hq.2]⟩
  have hBzero (p : S2) : B (p, 0) = (η p, 0) := hzero p
  have hBside : ∀ q ∈ B.source, q.2 ≤ 0 → (B q).2 ≤ 0 :=
    fun q hq hq0 => hRside q hq.2 hq0
  have hBi : B '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-(R / 2)) (R / 2)) ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioo l u := by
    rintro x ⟨q, hq, rfl⟩
    exact hRi q ⟨mem_univ _, by linarith [hq.2.1], by linarith [hq.2.2]⟩
  obtain ⟨F, hF, hFzero, K, hK, hKU, hfix, hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_parametrized_cylinder_collar B η hη
      (r := R / 4) (R := R / 2) (by linarith) (by linarith)
      (by linarith [(lt_min_iff.mp hRband).1]) (by linarith [(lt_min_iff.mp hRband).2])
      hBs hBzero hBside hBi
  refine ⟨R / 4, by linarith, F, ?_, hFzero, ?_, K, hK, hKU, hfix, hfixi⟩
  · intro q hq
    refine ⟨hRs ⟨mem_univ _, ?_, ?_⟩, hF q hq⟩ <;>
      linarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  · intro q hq
    have hn : q ∉ K := by
      intro hqK
      rcases hq with hq | hq
      · exact (not_lt_of_ge hq) (hKU hqK).2.1
      · exact (not_lt_of_ge hq) (hKU hqK).2.2
    exact ⟨hfix hn, hfixi hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_supported_collar_extension_of_positive_axial_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_supported_collar_extension_of_positive_axial_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_supported_collar_extension_of_positive_axial_derivative ``Submission.DifferentialGeometry.Topology.Manifold.exists_supported_collar_extension_of_positive_axial_derivative

end DifferentialGeometry.Topology.Manifold
