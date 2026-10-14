import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvaturePolynomialConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance mixedConvergenceC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedConvergenceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedConvergenceC1 target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private theorem polynomial_on_ancient_carrier {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (p : ℕ) {n : ℕ}
    (P : (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ)
    (hP : ∀ q t, t ∈ D.regular → ∀ x : M,
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
      DifferentiableAt ℝ (fun s => mixedCurvatureTensor S p q s x) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots))
    (q : ℕ) {t : ℝ} (ht : t ≤ b) (x : M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + p) → Fin n) :
    component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots) := by
  rcases ht.lt_or_eq with ht | htb
  · exact (hP q t (by rwa [hregular]) x basis).2 slots
  · subst t
    have hreg : _root_.Set.Ioo (b - 1) b ⊆ D.regular := by
      intro s hs
      rw [hregular]
      exact hs.2
    exact (mixedCurvature_polynomial_terminal_of_regular S hS p
      (by linarith : b - 1 < b) hcarrier hreg P x basis
      (fun q s hs => hP q s (hreg hs) x basis) q).2 slots

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomial_on_ancient_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomial_on_ancient_carrier target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
theorem mixed_curvature_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b) (ht : t ≤ b)
    (p q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S p q t ((extChartAt I x₀).symm y)
      (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨A, hA⟩ := exists_ancient_mixed_curvature_fields S hS hcarrier hregular p
  apply (tensor_field_chart_components_contDiffOn (A q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hA q t ht ((extChartAt I x₀).symm y)).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_contDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_contDiffOn


theorem mixed_curvature_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {b b₀ : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (hcarrier₀ : D₀.carrier = _root_.Set.Iic b₀) (hregular₀ : D₀.regular = _root_.Set.Iio b₀)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ≤ b) (t₀ : ℝ) (ht₀ : t₀ ≤ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (p q : ℕ)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => mixedCurvatureTensor (S n) p q (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y => mixedCurvatureTensor S₀ p q t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  classical
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  have hpoly := curvature_jet_polynomial_mapCInf_of_gram S S₀ τ t₀ x₀ hW hWt hgram
    (p + 2 * q) (P q slots)
  have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
      (hT : IsSolutionOn T) {c s : ℝ}
      (hcar : D'.carrier = _root_.Set.Iic c) (hreg : D'.regular = _root_.Set.Iio c) (hs : s ≤ c)
      (y : E) (hy : y ∈ W) :
      mixedCurvatureTensor T p q s ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
      MvPolynomial.eval (chartCurvatureJetPolynomialValues T (p + 2 * q) s x₀ y) (P q slots) := by
    have hb : (extChartAt I x₀).symm y ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hh := (extChartAt I x₀).map_target (hWt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
    have hh := polynomial_on_ancient_carrier T hT hcar hreg p P
      (fun q s hs x basis => hP q T hT s hs x basis) q hs
      ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb) slots
    rw [curvatureJetPolynomialValues_eq_chart T (p + 2 * q) s x₀ hb] at hh
    simpa only [component0S_apply, chartBasisFamily_apply] using hh
  exact hpoly.congr hW
    (fun n y hy => hcomp (S n) (hS n) hcarrier hregular (hτ n) y hy)
    (fun y hy => hcomp S₀ hS₀ hcarrier₀ hregular₀ ht₀ y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_mapCInf_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_mapCInf_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_mapCInf_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixed_curvature_components_mapCInf_of_gram

omit [BoundarylessManifold I M] in
private theorem polynomial_on_closedWindow {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (p : ℕ) {n : ℕ}
    (P : (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ)
    (hP : ∀ q t, t ∈ D.regular → ∀ x : M,
      ∀ basis : Module.Basis (Fin n) ℝ (TangentSpace I x),
      DifferentiableAt ℝ (fun s => mixedCurvatureTensor S p q s x) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots))
    (q : ℕ) {t : ℝ} (ht : t ∈ _root_.Set.Icc c b) (x : M)
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (slots : Fin (4 + p) → Fin n) :
    component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
      MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots) := by
  rcases ht.2.lt_or_eq with htb | htb
  · exact (hP q t (hregular ⟨hac.trans_le ht.1, htb⟩) x basis).2 slots
  · subst t
    exact (mixedCurvature_polynomial_terminal_of_regular_Icc S hS p le_rfl
      (hac.trans hcb) hcarrier hregular P x basis
      (fun q s hs => hP q s (hregular hs) x basis) q).2 slots

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomial_on_closedWindow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.polynomial_on_closedWindow target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
theorem closedWindow_mixed_curvature_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular) (ht : t ∈ _root_.Set.Icc c b)
    (p q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => mixedCurvatureTensor S p q t ((extChartAt I x₀).symm y)
      (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  obtain ⟨A, hA⟩ := exists_closedWindow_mixed_curvature_fields S hS hac hcb hcarrier hregular p
  apply (tensor_field_chart_components_contDiffOn (A q t) x₀ hWt slots).congr
  intro y _hy
  rw [(hA q t ht ((extChartAt I x₀).symm y)).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_contDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_contDiffOn


theorem closedWindow_mixed_curvature_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b a₀ c₀ b₀ : ℝ} (hac : a < c) (hcb : c < b)
    (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (hcarrier₀ : D₀.carrier = _root_.Set.Icc a₀ b₀) (hregular₀ : _root_.Set.Ioo a₀ b₀ ⊆ D₀.regular)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ _root_.Set.Icc c b) (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc c₀ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (p q : ℕ)
    (slots : Fin (4 + p) → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y => mixedCurvatureTensor (S n) p q (τ n) ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y => mixedCurvatureTensor S₀ p q t₀ ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  classical
  choose P hP using fun q : ℕ =>
    exists_mixed_curvature_jet_polynomials (Module.finrank ℝ E) p q
  have hpoly := curvature_jet_polynomial_mapCInf_of_gram S S₀ τ t₀ x₀ hW hWt hgram
    (p + 2 * q) (P q slots)
  have hcomp {D' : RealTimeInterval} (T : SolutionOn (I := I) (M := M) D')
      (hT : IsSolutionOn T) {a' c' b' s : ℝ}
      (hac' : a' < c') (hcb' : c' < b')
      (hcar : D'.carrier = _root_.Set.Icc a' b') (hreg : _root_.Set.Ioo a' b' ⊆ D'.regular)
      (hs : s ∈ _root_.Set.Icc c' b')
      (y : E) (hy : y ∈ W) :
      mixedCurvatureTensor T p q s ((extChartAt I x₀).symm y)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)) =
      MvPolynomial.eval (chartCurvatureJetPolynomialValues T (p + 2 * q) s x₀ y) (P q slots) := by
    have hb : (extChartAt I x₀).symm y ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      have hh := (extChartAt I x₀).map_target (hWt hy)
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hh
    have hh := polynomial_on_closedWindow T hT hac' hcb' hcar hreg p P
      (fun q s hs x basis => hP q T hT s hs x basis) q hs
      ((extChartAt I x₀).symm y) (chartBasisFamily (I := I) x₀ hb) slots
    rw [curvatureJetPolynomialValues_eq_chart T (p + 2 * q) s x₀ hb] at hh
    simpa only [component0S_apply, chartBasisFamily_apply] using hh
  exact hpoly.congr hW
    (fun n y hy => hcomp (S n) (hS n) hac hcb hcarrier hregular (hτ n) y hy)
    (fun y hy => hcomp S₀ hS₀ ha₀c₀ hc₀b₀ hcarrier₀ hregular₀ ht₀ y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_mapCInf_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_mapCInf_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_mapCInf_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_mixed_curvature_components_mapCInf_of_gram

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
