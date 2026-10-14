import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance scalarTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarTopology target :: scope.openDecls } }
private local instance scalarCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarCharted target :: scope.openDecls } }
private local instance scalarSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarSmooth target :: scope.openDecls } }
private local instance scalarT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarT2 target :: scope.openDecls } }
private local instance scalarSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarSigma target :: scope.openDecls } }

theorem exists_neg_time_scalar_pos_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ b : ℝ, b < 0 ∧ ∃ x : F.M, 0 < F.S.scalar b x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨t, ht, x, hx⟩ := hF.notFlat
  have hop : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric t) x).mpr
    intro n c a d
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator t ht x n c a d
  have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hop
  have hnorm : 0 < normSq0S (I := I) (F.S.base.metric t) x 4
      (F.S.base.rm04 t x) :=
    lt_of_le_of_ne (normSq0S_nonneg (F.S.base.metric t) x 4 _) (Ne.symm hx)
  have hscalar : 0 < F.S.scalar t x := by
    by_contra h
    have hnonpos : (Module.finrank ℝ E : ℝ) ^ 2 * F.S.scalar t x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    have hpos := Real.sqrt_pos.mpr hnorm
    exact (not_lt_of_ge (hsqrt.trans hnonpos)) hpos
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using ht
  rcases lt_or_eq_of_le ht0 with htneg | rfl
  · exact ⟨t, htneg, x, hscalar⟩
  · have hcont : ContinuousWithinAt (fun s : ℝ => F.S.scalar s x) (_root_.Set.Iic 0) 0 := by
      have h := F.isSolution.scalarCont (0, x) (show (0, x) ∈
          D.carrier ×ˢ (_root_.Set.univ : Set F.M) from ⟨ht, _root_.Set.mem_univ _⟩)
      have hpair : ContinuousWithinAt (fun s : ℝ => (s, x)) (_root_.Set.Iic 0) 0 :=
        continuousWithinAt_id.prodMk continuousWithinAt_const
      exact h.comp (f := fun s : ℝ => (s, x)) (x := 0) hpair
        (fun s hs => ⟨by simpa only [hF.carrier_eq] using hs, _root_.Set.mem_univ _⟩)
    have hleft : ContinuousWithinAt (fun s : ℝ => F.S.scalar s x) (_root_.Set.Iio 0) 0 :=
      hcont.mono _root_.Set.Iio_subset_Iic_self
    have hpos : ∀ᶠ s in 𝓝[<] (0 : ℝ), 0 < F.S.scalar s x :=
      hleft.eventually (isOpen_Ioi.mem_nhds hscalar)
    obtain ⟨b, hb, hbx⟩ := (hpos.and self_mem_nhdsWithin).exists
    exact ⟨b, hbx, x, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_scalar_pos_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_scalar_pos_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_scalar_pos_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_scalar_pos_of_ancient

theorem exists_neg_time_rmNormSq_ne_zero_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ b : ℝ, b < 0 ∧ ∃ x : F.M,
      normSq0S (I := I) (F.S.base.metric b) x 4 (F.S.base.rm04 b x) ≠ 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨b, hb, x, hx⟩ := exists_neg_time_scalar_pos_of_ancient F hF
  refine ⟨b, hb, x, ?_⟩
  intro hzero
  have hbound := scalar_abs_le_rm (I := I) (M := F.M) (F.S.base.metric b) x
  have hz : normSq0S (I := I) (F.S.base.metric b) x 4
      (metricRm04At (I := I) (M := F.M) (F.S.base.metric b) x) = 0 := hzero
  rw [hz, Real.sqrt_zero, _root_.MulZeroClass.mul_zero] at hbound
  have habs : |F.S.scalar b x| = 0 := le_antisymm hbound (abs_nonneg _)
  exact (ne_of_gt hx) (abs_eq_zero.mp habs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_rmNormSq_ne_zero_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_rmNormSq_ne_zero_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_rmNormSq_ne_zero_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_neg_time_rmNormSq_ne_zero_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
