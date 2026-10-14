/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CellEnlargements
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLCellExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.exists_supported_conjugate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (T : PLPieceIn E n M W)
    {τ : E → E} (hτ : IsPLHomeomorphOn τ T.complex.space T.complex.space)
    {K : Set E} (hK : IsCompact K) (hKP : K ⊆ T.complex.space)
    (hKW : T.map '' K ⊆ interior W) (hfix : _root_.Set.EqOn τ id (T.complex.space \ K)) :
    ∃ φ : M ≃ₜ M, IsPL n n φ ∧ IsPL n n φ.symm ∧
      (∀ x ∈ T.complex.space, φ (T.map x) = T.map (τ x)) ∧
      EqOn φ id (T.map '' K)ᶜ := by
  classical
  let q := Function.invFunOn T.map T.complex.space
  let σ := Function.invFunOn τ T.complex.space
  let F := T.map ∘ τ ∘ q
  let G := T.map ∘ σ ∘ q
  have hq : _root_.Set.MapsTo q W T.complex.space := T.bijOn.surjOn.mapsTo_invFunOn
  have hσ : _root_.Set.MapsTo σ T.complex.space T.complex.space := hτ.symm.bijOn.mapsTo
  have hF : IsPLOn n n F W := T.isPLOn_conjugate hτ.isPiecewiseAffineOn hτ.bijOn.mapsTo
  have hG : IsPLOn n n G W := T.isPLOn_conjugate hτ.symm.isPiecewiseAffineOn hσ
  have hFW : _root_.Set.MapsTo F W W := T.bijOn.mapsTo.comp (hτ.bijOn.mapsTo.comp hq)
  have hGW : _root_.Set.MapsTo G W W := T.bijOn.mapsTo.comp (hσ.comp hq)
  have hGF : _root_.Set.LeftInvOn G F W := by
    intro x hx
    dsimp [G, F, q, σ, Function.comp_def]
    rw [T.bijOn.invOn_invFunOn.1 (hτ.bijOn.mapsTo (hq hx)),
      hτ.bijOn.invOn_invFunOn.1 (hq hx), T.bijOn.invOn_invFunOn.2 hx]
  have hFG : _root_.Set.LeftInvOn F G W := by
    intro x hx
    dsimp [G, F, q, σ, Function.comp_def]
    rw [T.bijOn.invOn_invFunOn.1 (hσ (hq hx)),
      hτ.bijOn.invOn_invFunOn.2 (hq hx), T.bijOn.invOn_invFunOn.2 hx]
  have hFfix : _root_.Set.EqOn F id (W \ T.map '' K) := by
    intro x hx
    have hqK : q x ∉ K := fun h => hx.2 ⟨q x, h, T.bijOn.invOn_invFunOn.2 hx.1⟩
    dsimp [F, Function.comp_def]
    rw [hfix ⟨hq hx.1, hqK⟩]
    exact T.bijOn.invOn_invFunOn.2 hx.1
  obtain ⟨φ, hφ, hφi, hφF, -, hφfix⟩ := exists_supported_isPL_homeomorph_extension
    (hK.image_of_continuousOn (T.continuousOn.mono hKP)).isClosed hKW hF hG hFW hGW
      hGF hFG hFfix
  refine ⟨φ, hφ, hφi, ?_, hφfix⟩
  intro x hx
  rw [hφF (T.bijOn.mapsTo hx)]
  dsimp [F, q, Function.comp_def]
  rw [T.bijOn.invOn_invFunOn.1 hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_conjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_supported_conjugate

end DifferentialGeometry.Topology.PiecewiseLinear
