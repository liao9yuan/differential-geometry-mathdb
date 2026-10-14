import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.I_half target :: scope.openDecls } }

theorem dirichletGalerkin_integrated_weak_identity
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ)
    {γ : ℝ → EuclideanSpace ℝ ι}
    (hγcont : ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T))
    (hγweak : ∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
      ∃ v : EuclideanSpace ℝ ι,
        HasDerivWithinAt γ v (_root_.Set.Ici (0 : ℝ)) t ∧
          dirichletFinMass (G.metric t) (dirichletFinIncl φ) v =
            dirichletFinWeakForm (G.metric t) (X t) (a t)
              (dirichletFinIncl φ) (γ t))
    (w : EuclideanSpace ℝ ι)
    (η dη : ℝ → ℝ)
    (hηcont : ContinuousOn η (_root_.Set.Icc (0 : ℝ) T))
    (hηderiv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt η (dη t) (_root_.Set.Ioi t) t)
    (hηT : η T = 0)
    (hmassInt : IntervalIntegrable
      (fun t => dη t * dirichletMass (G.metric t)
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w)) _root_.MeasureTheory.MeasureSpace.volume 0 T)
    (hvariationInt : IntervalIntegrable
      (fun t => η t * dirichletMassVariation G.metric t
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w)) _root_.MeasureTheory.MeasureSpace.volume 0 T)
    (hweakInt : IntervalIntegrable
      (fun t => η t * dirichletWeakForm (G.metric t) (X t) (a t)
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w)) _root_.MeasureTheory.MeasureSpace.volume 0 T) :
    -(∫ t in (0 : ℝ)..T, dη t * dirichletMass (G.metric t)
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w)) -
      (∫ t in (0 : ℝ)..T, η t * dirichletMassVariation G.metric t
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w)) -
      η 0 * dirichletMass (G.metric 0)
        (dirichletFinIncl φ (γ 0)) (dirichletFinIncl φ w) =
      ∫ t in (0 : ℝ)..T, η t * dirichletWeakForm (G.metric t) (X t) (a t)
        (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ w) := by
  let J := dirichletFinIncl φ
  let mass : ℝ → ℝ := fun t => dirichletMass (G.metric t) (J (γ t)) (J w)
  let variation : ℝ → ℝ := fun t =>
    dirichletMassVariation G.metric t (J (γ t)) (J w)
  let weak : ℝ → ℝ := fun t =>
    dirichletWeakForm (G.metric t) (X t) (a t) (J (γ t)) (J w)
  have hmassForm : ContinuousOn
      (fun t => dirichletFinMass (G.metric t) J) (_root_.Set.Icc (0 : ℝ) T) :=
    dirichletFinMass_cont G.metric _root_.CompactIccSpace.isCompact_Icc
      (fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j) J
  have hmassCont : ContinuousOn mass (_root_.Set.Icc (0 : ℝ) T) := by
    exact (hmassForm.clm_apply hγcont).clm_apply continuousOn_const
  have hprodCont : ContinuousOn (fun t => η t * mass t) (_root_.Set.Icc (0 : ℝ) T) :=
    hηcont.mul hmassCont
  have hmassDeriv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt mass (weak t + variation t) (_root_.Set.Ioi t) t := by
    intro t ht
    obtain ⟨v, hγv, hv⟩ := hγweak t ⟨ht.1.le, ht.2⟩
    have hγv' : HasDerivWithinAt γ v (_root_.Set.Ioi t) t :=
      hγv.mono (fun s hs => le_trans ht.1.le hs.le)
    have hmass := hasDerivWithinAt_dirichletFinIncl_mass_left hG
      (hreg ⟨ht.1.le, ht.2.le⟩) φ (J w) hγv'
    apply hmass.congr_deriv
    have heval := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ => L w) hv
    have heval' : dirichletMass (G.metric t) (J v) (J w) = weak t := by
      simpa only [J, weak, dirichletFinMass_apply,
        dirichletFinWeakForm_apply] using heval
    rw [heval']
  have hprodDeriv : ∀ t ∈ _root_.Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => η s * mass s)
        (dη t * mass t + η t * weak t + η t * variation t) (_root_.Set.Ioi t) t := by
    intro t ht
    exact ((hηderiv t ht).mul (hmassDeriv t ht)).congr_deriv (by ring)
  have htotalInt : IntervalIntegrable
      (fun t => dη t * mass t + η t * weak t + η t * variation t)
      volume 0 T := by
    exact (hmassInt.add hweakInt).add hvariationInt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
    hprodCont hprodDeriv htotalInt
  rw [intervalIntegral.integral_add (hmassInt.add hweakInt) hvariationInt,
    intervalIntegral.integral_add hmassInt hweakInt, hηT, _root_.MulZeroClass.zero_mul, zero_sub] at hftc
  change -(∫ t in (0 : ℝ)..T, dη t * mass t) -
      (∫ t in (0 : ℝ)..T, η t * variation t) - η 0 * mass 0 =
    ∫ t in (0 : ℝ)..T, η t * weak t
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_integrated_weak_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_integrated_weak_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_integrated_weak_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.dirichletGalerkin_integrated_weak_identity

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
