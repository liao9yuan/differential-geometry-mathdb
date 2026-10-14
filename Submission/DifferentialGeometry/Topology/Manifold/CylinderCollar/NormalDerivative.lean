import Submission.DifferentialGeometry.Topology.Manifold.CylinderCollar.Matching
import Submission.DifferentialGeometry.Topology.Diffeomorph.Collar
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

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

open private contMDiffOn_deriv_snd from Submission.DifferentialGeometry.Topology.Diffeomorph.Collar

private theorem cylinderAxialDerivative_continuousOn
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞) :
    ContinuousOn (fun q : SphereCylinder => deriv (fun t => (A (q.1, t)).2) q.2) A.source := by
  exact (contMDiffOn_deriv_snd A.open_source
    (contMDiff_snd.comp_contMDiffOn A.contMDiffOn_toFun)).continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.cylinderAxialDerivative_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.cylinderAxialDerivative_continuousOn target :: scope.openDecls } }

theorem exists_uniform_cylinder_width_of_positive_axial_derivative
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (hsource : ∀ p : S2, (p, 0) ∈ A.source)
    (hzero : ∀ p : S2, (A (p, 0)).2 = 0)
    (hpos : ∀ p : S2, 0 < deriv (fun t => (A (p, t)).2) 0)
    (l u : ℝ) (hl : l < 0) (hu : 0 < u) :
    ∃ R : ℝ, 0 < R ∧ R < _root_.Min.min (-l) u ∧
      (_root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ A.source) ∧
      (∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R, A q ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo l u) ∧
      ∀ q ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-R) R, q.2 ≤ 0 → (A q).2 ≤ 0 := by
  let f : SphereCylinder → ℝ := fun q => (A q).2
  let d : SphereCylinder → ℝ := fun q => deriv (fun t => (A (q.1, t)).2) q.2
  let W := (A.source ∩ d ⁻¹' _root_.Set.Ioi (0 : ℝ)) ∩ f ⁻¹' _root_.Set.Ioo l u
  have hd : ContinuousOn d A.source := cylinderAxialDerivative_continuousOn A
  have hf : ContinuousOn f A.source := A.contMDiffOn_toFun.continuousOn.snd
  have hW : IsOpen W :=
    (hf.mono _root_.Set.inter_subset_left).isOpen_inter_preimage
      (hd.isOpen_inter_preimage A.open_source isOpen_Ioi) isOpen_Ioo
  have hbase : (_root_.Set.univ : Set S2) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨hsource p, hpos p⟩, by change (A (p, 0)).2 ∈ _root_.Set.Ioo l u; rw [hzero p]; exact ⟨hl, hu⟩⟩
  obtain ⟨S, T, _, hT, hS, h0T, hST⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hW hbase
  obtain ⟨ρ, hρ, hρT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (_root_.Set.mem_singleton 0))
  let R := _root_.Min.min (ρ / 2) (_root_.Min.min (-l / 2) (u / 2))
  have hR : 0 < R := by
    dsimp only [R]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hRρ : R < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRband : R < _root_.Min.min (-l) u := by
    have hRl : R ≤ -l / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hRu : R ≤ u / 2 := (min_le_right _ _).trans (min_le_right _ _)
    exact lt_min (by linarith) (by linarith)
  have hstrip : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ W := by
    rintro q ⟨_, hq⟩
    apply hST
    refine ⟨hS (_root_.Set.mem_univ q.1), hρT ?_⟩
    have ha : |q.2| < ρ := (abs_le.mpr hq).trans_lt hRρ
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ha
  refine ⟨R, hR, hRband, fun q hq => (hstrip hq).1.1, ?_, ?_⟩
  · intro q hq
    exact ⟨mem_univ _, (hstrip hq).2⟩
  · rintro q ⟨_, hq⟩ hq0
    have hmono : StrictMonoOn (fun t => (A (q.1, t)).2) (_root_.Set.Ioo (-R) R) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
      · apply hf.comp (continuous_const.prodMk continuous_id).continuousOn
        intro t ht
        exact (hstrip ⟨mem_univ _, ht.1.le, ht.2.le⟩).1.1
      · intro t ht
        have ht' : t ∈ _root_.Set.Ioo (-R) R := interior_subset ht
        exact (hstrip (show (q.1, t) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R from ⟨mem_univ _, ht'.1.le, ht'.2.le⟩)).1.2
    have hz : (0 : ℝ) ∈ _root_.Set.Ioo (-R) R := ⟨neg_lt_zero.mpr hR, hR⟩
    have hh := hmono.monotoneOn hq hz hq0
    rw [hzero q.1] at hh
    exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_uniform_cylinder_width_of_positive_axial_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_uniform_cylinder_width_of_positive_axial_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_uniform_cylinder_width_of_positive_axial_derivative ``Submission.DifferentialGeometry.Topology.Manifold.exists_uniform_cylinder_width_of_positive_axial_derivative

end DifferentialGeometry.Topology.Manifold
