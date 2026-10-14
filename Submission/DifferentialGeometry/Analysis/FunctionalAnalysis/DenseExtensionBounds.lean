import Mathlib

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

theorem dense_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [T2Space Y] [CompleteSpace Y] {D : Set X} (hD : Dense D) {K : NNReal}
    (F : D → Y) (hF : LipschitzWith K F) :
    LipschitzWith K (Dense.extend hD F) := by
  have hFcont : Continuous F := hF.continuous
  have hext_cont : Continuous (Dense.extend hD F) :=
    (hD.uniformContinuous_extend hF.uniformContinuous).continuous
  have hext_eq : ∀ x : D, Dense.extend hD F (x : X) = F x :=
    fun x ↦ hD.extend_eq hFcont x
  have hlipD : LipschitzOnWith K (Dense.extend hD F) D := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun x hx y hy ↦ ?_)
    let xd : D := ⟨x, hx⟩
    let yd : D := ⟨y, hy⟩
    rw [show Dense.extend hD F x = F xd by simpa [xd] using hext_eq xd,
      show Dense.extend hD F y = F yd by simpa [yd] using hext_eq yd]
    simpa [xd, yd, Subtype.dist_eq] using hF.dist_le_mul xd yd
  have hlip_closure : LipschitzOnWith K (Dense.extend hD F) (closure D) :=
    hlipD.closure hext_cont.continuousOn
  rw [hD.closure_eq, lipschitzOnWith_univ] at hlip_closure
  exact hlip_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz

theorem mixed_of_dense
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] {D : Set X} (hD : Dense D)
    (N : X → Y) (hN : Continuous N) (J : X → Z) (hJ : Continuous J)
    (A B : Real)
    (hDense : ∀ x ∈ D, ∀ y ∈ D,
      ‖N x - N y‖ ≤
        A * _root_.Max.max ‖J x‖ ‖J y‖ * ‖x - y‖ + B * ‖J (x - y)‖) :
    ∀ x y : X,
      ‖N x - N y‖ ≤
        A * _root_.Max.max ‖J x‖ ‖J y‖ * ‖x - y‖ + B * ‖J (x - y)‖ := by
  let lhs : X × X → Real := fun p ↦ ‖N p.1 - N p.2‖
  let rhs : X × X → Real := fun p ↦
    A * _root_.Max.max ‖J p.1‖ ‖J p.2‖ * ‖p.1 - p.2‖ + B * ‖J (p.1 - p.2)‖
  have hlhs : Continuous lhs := by
    dsimp only [lhs]
    exact ((hN.comp continuous_fst).sub (hN.comp continuous_snd)).norm
  have hrhs : Continuous rhs := by
    dsimp only [rhs]
    apply Continuous.add
    · exact (continuous_const.mul
        (((hJ.comp continuous_fst).norm).max
          ((hJ.comp continuous_snd).norm))).mul
        (continuous_fst.sub continuous_snd).norm
    · exact continuous_const.mul
        (hJ.comp (continuous_fst.sub continuous_snd)).norm
  have hclosed : IsClosed {p | lhs p ≤ rhs p} := isClosed_le hlhs hrhs
  have hsub : D ×ˢ D ⊆ {p | lhs p ≤ rhs p} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact hDense x hx y hy
  have huniv : {p | lhs p ≤ rhs p} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hD.prod hD).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  intro x y
  have hxy : ((x, y) : X × X) ∈ {p | lhs p ≤ rhs p} := by
    rw [huniv]
    trivial
  exact hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.mixed_of_dense then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.mixed_of_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.mixed_of_dense ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.mixed_of_dense

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
