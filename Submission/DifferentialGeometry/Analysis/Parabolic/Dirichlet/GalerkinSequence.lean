import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Integral.Measure
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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem exists_dirichletGalerkin_sequence
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : _root_.Set.Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (_root_.Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (_root_.Set.Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ _root_.Set.Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    ∃ γ : (m : ℕ) → ℝ →
        EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
      ∀ m,
        γ m 0 = smoothDirichletBasisCoordinates
            (smoothDirichletBasisFinset q m) f₀ ∧
        ContinuousOn (γ m) (_root_.Set.Icc (0 : ℝ) T) ∧
        (∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
          ∃ v : EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
            HasDerivWithinAt (γ m) v (_root_.Set.Ici (0 : ℝ)) t ∧
            dirichletFinMass (G.metric t)
                (smoothDirichletBasisFinIncl
                  (smoothDirichletBasisFinset q m)) v =
              dirichletFinWeakForm (G.metric t) (X t) (a t)
                (smoothDirichletBasisFinIncl
                  (smoothDirichletBasisFinset q m)) (γ m t)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
          dirichletMass (G.metric t)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ m t))
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ m t)) ≤
            dirichletMass (G.metric 0)
              (smoothDirichletBasisApproximation q m f₀)
              (smoothDirichletBasisApproximation q m f₀) *
                Real.exp (_root_.Max.max (Bx + (1 / 2) * Bv) 0 * T)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
          (∫ s in (0 : ℝ)..t,
            dirichletEnergy (G.metric s)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ m s))
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ m s))) ≤
            dirichletMass (G.metric 0)
              (smoothDirichletBasisApproximation q m f₀)
              (smoothDirichletBasisApproximation q m f₀) *
                (1 + _root_.Max.max (Bx + (1 / 2) * Bv) 0 * T *
                  Real.exp (_root_.Max.max (Bx + (1 / 2) * Bv) 0 * T))) := by
  classical
  have hm : ∀ m : ℕ,
      ∃ γ : ℝ → EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
        γ 0 = smoothDirichletBasisCoordinates
            (smoothDirichletBasisFinset q m) f₀ ∧
        ContinuousOn γ (_root_.Set.Icc (0 : ℝ) T) ∧
        (∀ t, (ht : t ∈ _root_.Set.Ico (0 : ℝ) T) →
          ∃ v : EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
            HasDerivWithinAt γ v (_root_.Set.Ici (0 : ℝ)) t ∧
            dirichletFinMass (G.metric t)
                (smoothDirichletBasisFinIncl
                  (smoothDirichletBasisFinset q m)) v =
              dirichletFinWeakForm (G.metric t) (X t) (a t)
                (smoothDirichletBasisFinIncl
                  (smoothDirichletBasisFinset q m)) (γ t)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
          dirichletMass (G.metric t)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ t))
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ t)) ≤
            dirichletMass (G.metric 0)
              (smoothDirichletBasisApproximation q m f₀)
              (smoothDirichletBasisApproximation q m f₀) *
                Real.exp (_root_.Max.max (Bx + (1 / 2) * Bv) 0 * T)) ∧
        (∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
          (∫ s in (0 : ℝ)..t,
            dirichletEnergy (G.metric s)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ s))
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m) (γ s))) ≤
            dirichletMass (G.metric 0)
              (smoothDirichletBasisApproximation q m f₀)
              (smoothDirichletBasisApproximation q m f₀) *
                (1 + _root_.Max.max (Bx + (1 / 2) * Bv) 0 * T *
                  Real.exp (_root_.Max.max (Bx + (1 / 2) * Bv) 0 * T))) := by
    intro m
    let s := smoothDirichletBasisFinset q m
    let J := smoothDirichletBasisFinIncl s
    let v₀ := smoothDirichletBasisCoordinates s f₀
    obtain ⟨γ, hγ0, hγcont, hγsol⟩ :=
      dirichletGalerkin_solution_exists hG hT hreg J
        (dirichletMass_smoothDirichletBasisFinIncl s) X hXcont a hacont v₀
    have hmass := dirichletGalerkin_mass_uniform_bound hG hT.le hreg
      (fun i : s => smoothDirichletBasisFunction q i) γ hγcont X a Bx Bv
      (by simpa only [J, smoothDirichletBasisFinIncl] using hγsol) hX htrace ha
    have henergy := dirichletGalerkin_energy_integral_bound hG hT.le hreg
      (fun i : s => smoothDirichletBasisFunction q i) γ hγcont X a Bx Bv
      (by simpa only [J, smoothDirichletBasisFinIncl] using hγsol) hX htrace ha
    have hinit :
        dirichletFinIncl (fun i : s => smoothDirichletBasisFunction q i) v₀ =
          smoothDirichletBasisApproximation q m f₀ := by
      change smoothDirichletBasisFinIncl s v₀ =
        smoothDirichletBasisApproximation q m f₀
      simpa only [s, v₀] using smoothDirichletBasisFinIncl_coordinates m f₀
    refine ⟨γ, hγ0, hγcont, hγsol, ?_, ?_⟩
    · intro t ht
      have h := hmass t ht
      rw [hγ0, hinit] at h
      simpa only [s, J, smoothDirichletBasisFinIncl] using h
    · intro t ht
      have h := henergy t ht
      rw [hγ0, hinit] at h
      simpa only [s, J, smoothDirichletBasisFinIncl] using h
  choose γ hγ using hm
  exact ⟨γ, hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_dirichletGalerkin_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_dirichletGalerkin_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_dirichletGalerkin_sequence ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_dirichletGalerkin_sequence

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
