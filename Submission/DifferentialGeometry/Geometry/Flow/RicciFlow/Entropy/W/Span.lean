import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.Galerkin.Span
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat.WSpan
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.LowerBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {M : Type u}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def flowW
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t theta : Real) (v : M → Real) : Real :=
  let g := S.family.metric t
  let f := perelmanPotential (Module.finrank Real E) theta v
  wFunctional (riemannianVolumeMeasure (I := I) (M := M) g)
    (Module.finrank Real E) theta (S.scalar t)
    (fun x => g.inner x
      (gradientFun (I := I) g f x)
      (gradientFun (I := I) g f x)) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.flowW then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.flowW"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.flowW ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.flowW

theorem w_span_uniform
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {a₀ a tauMax : Real} (ha₀a : a₀ < a) :
    ∃ L : Real, ∀ {b : Real}, a ≤ b →
      Set.Icc a₀ b ⊆ D.regular →
      ∀ t ∈ Set.Icc a b,
        ∀ {theta : Real}, 0 < theta → theta + (t - a) < tauMax →
        ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v →
          (∀ x : M, 0 < v x) →
          (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
            (S.family.metric t))) = 1 →
          L ≤ flowW (I := I) (M := M) S t theta v := by
  classical
  obtain ⟨L, hL⟩ := w_density_lower (I := I) (M := M)
    (S.family.metric a) hDim tauMax
  refine ⟨L, ?_⟩
  intro b hab hreg
  obtain ⟨rho₀, hrho₀, _hrho₀_one, hspan⟩ :=
    gallim_span (I := I) (M := M) S hS hreg
  let r : Real := _root_.Min.min rho₀ (a - a₀)
  have hr : 0 < r := lt_min hrho₀ (sub_pos.mpr ha₀a)
  have hr_rho : r ≤ rho₀ := min_le_left _ _
  have hr_gap : r ≤ a - a₀ := min_le_right _ _
  let delta : Real := r / 2
  have hdelta : 0 < delta := by
    simpa only [delta] using half_pos hr
  have hdelta_r : delta < r := by
    simpa only [delta] using half_lt_self hr
  let Good : Real → Prop := fun t =>
    ∀ theta : Real, 0 < theta → theta + (t - a) < tauMax →
      ∀ v : M → Real, ContMDiff I 𝓘(Real) ∞ v →
        (∀ x : M, 0 < v x) →
        (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric t))) = 1 →
        L ≤ flowW (I := I) (M := M) S t theta v
  have hbase : Good a := by
    dsimp only [Good]
    intro theta htheta hbudget v hv hpos hmass
    have hthetaMax : theta ∈ Set.Ioc (0 : Real) tauMax := by
      constructor
      · exact htheta
      · linarith
    have hbound := hL hthetaMax hv hpos hmass
    have hscalarA : S.scalar a =
        fun x => metricScalarAt (I := I) (M := M) (S.family.metric a) x := by
      funext x
      rw [SolutionOn.scalar_eq_metricTrace]
      rfl
    simpa only [flowW, hDim, hscalarA] using hbound
  have hstep (s t : Real) (hs : s ∈ Set.Icc a b)
      (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
      (hgap : t - s ≤ delta) (hgood : Good s) : Good t := by
    dsimp only [Good] at hgood ⊢
    intro theta htheta hbudget v hv hpos hmass
    by_cases hstEq : s = t
    · subst t
      exact hgood theta htheta hbudget v hv hpos hmass
    have hqpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst hstEq)
    let T : D.RegularTime :=
      ⟨t, hreg ⟨ha₀a.le.trans ht.1, ht.2⟩⟩
    have hT : (T : Real) ∈ Set.Icc a₀ b :=
      ⟨ha₀a.le.trans ht.1, ht.2⟩
    have hleft : a₀ ≤ (T : Real) - r := by
      change a₀ ≤ t - r
      linarith [ht.1, hr_gap]
    let zeta : C^∞⟮I, M; Real⟯ := ⟨v, hv⟩
    let u₀ : SmoothCcTensor (S.family.metric (T : Real)) 0 0 :=
      scalarCc (I := I) (M := M) (S.family.metric (T : Real)) zeta
    have hu₀ :
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u₀.toSection = v := by
      change TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (scalarCc (I := I) (M := M) (S.family.metric (T : Real)) zeta).toSection =
        (zeta : M → Real)
      exact scalar0_scalarCc (I := I) (M := M)
        (S.family.metric (T : Real)) zeta
    obtain ⟨V, phi, ulim, hlim, hpot⟩ :=
      hspan T hT r hr hr_rho hleft u₀
    let u : Real → M → Real := fun q x =>
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i z => ulim z i) q x
    have hinit : ∀ x : M,
        0 < TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          u₀.toSection x := by
      intro x
      rw [hu₀]
      exact hpos x
    have hposPath : ∀ q ∈ Set.Icc (0 : Real) r, ∀ x : M, 0 < u q x := by
      simpa only [u] using
        gallim_pos_on (I := I) (M := M) S hS hreg T hT hr hleft
          hlim hpot hinit
    have href : ∀ q ∈ Set.Icc (0 : Real) r,
        (T : Real) - q ∈ D.regular := by
      intro q hq
      apply hreg
      constructor <;> linarith [hq.1, hq.2, hT.1, hT.2, hleft]
    have hmassPath := heatpot_mass_on (I := I) (M := M)
      S hS T hr hpot href
    let q : Real := t - s
    have hqIcc : q ∈ Set.Icc (0 : Real) r := by
      constructor
      · exact hqpos.le
      · exact hgap.trans hdelta_r.le
    have hqIco : q ∈ Set.Ico (0 : Real) r :=
      ⟨hqpos.le, hgap.trans_lt hdelta_r⟩
    have htq : (T : Real) - q = s := by
      dsimp only [T, q]
      ring
    have hu0eq : u 0 = v := by
      dsimp only [u]
      rw [galerkinLim_initial (I := I) (M := M) hlim]
      exact hu₀
    have hmass0 :
        (∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M)
            (flowG (I := I) S) (T : Real)) 0)) = 1 := by
      rw [hu0eq]
      simpa only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, reverseFamily, flowG, sub_zero,
        SolutionOn.family_metric] using hmass
    have hmassq :
        (∫ x, u q x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric s))) = 1 := by
      have hm := (hmassPath q hqIcc).trans hmass0
      simpa only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, reverseFamily, flowG, htq,
        SolutionOn.family_metric] using hm
    have hsmoothq : ContMDiff I 𝓘(Real) ∞ (u q) := by
      exact hpot.sliceSmooth q hqIcc
    have hposq : ∀ x : M, 0 < u q x := hposPath q hqIcc
    have hthetaq : 0 < theta + q := add_pos_of_pos_of_nonneg htheta hqIco.1
    have hbudgetq : theta + q + (s - a) < tauMax := by
      have hqeq : q = t - s := rfl
      rw [hqeq]
      linarith
    have hlower : L ≤ flowW (I := I) (M := M) S s (theta + q) (u q) :=
      hgood (theta + q) hthetaq hbudgetq (u q) hsmoothq hposq hmassq
    have hW := gallim_w_lt (I := I) (M := M)
      hS hr hlim hpot href htheta hposPath q hqIco
    have hWflow :
        flowW (I := I) (M := M) S s (theta + q) (u q) ≤
          flowW (I := I) (M := M) S t theta v := by
      let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
      have hGq : G.metric q = S.family.metric s := by
        change S.family.metric ((T : Real) - q) = S.family.metric s
        rw [htq]
      have hG0 : G.metric 0 = S.family.metric t := by
        change S.family.metric ((T : Real) - 0) = S.family.metric t
        rw [sub_zero, show (T : Real) = t from rfl]
      have hscalar0 : (fun x => S.scalar (T : Real) x) = S.scalar t := by
        rw [show (T : Real) = t from rfl]
      have hu0fun :
          (fun x => scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i z => ulim z i) 0 x) = v := hu0eq
      dsimp only [flowW, u]
      rw [hDim] at hW ⊢
      simpa only [G, hGq, hG0, volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, add_zero, sub_zero, htq, hscalar0, hu0fun] using hW
    exact hlower.trans hWflow
  have hgrid : ∀ n : Nat, ∀ t ∈ Set.Icc a b,
      t ≤ a + (n : Real) * delta → Good t := by
    intro n
    induction n with
    | zero =>
        intro t ht hta
        have hta' : t = a := by
          norm_num at hta
          exact le_antisymm hta ht.1
        subst t
        exact hbase
    | succ n ih =>
        intro t ht htn
        let s : Real := _root_.Max.max a (t - delta)
        have hsA : a ≤ s := le_max_left _ _
        have hst : s ≤ t := by
          apply max_le ht.1
          linarith [hdelta.le]
        have hsB : s ≤ b := hst.trans ht.2
        have hsn : s ≤ a + (n : Real) * delta := by
          apply max_le
          · have hn0 : 0 ≤ (n : Real) * delta :=
              mul_nonneg (Nat.cast_nonneg n) hdelta.le
            linarith
          · norm_num [Nat.cast_succ] at htn ⊢
            linarith
        have hgap : t - s ≤ delta := by
          have hsLower : t - delta ≤ s := le_max_right _ _
          linarith
        exact hstep s t ⟨hsA, hsB⟩ ht hst hgap (ih s ⟨hsA, hsB⟩ hsn)
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt ((b - a) / delta)
  have hcover : b ≤ a + (N : Real) * delta := by
    have hmul : b - a < (N : Real) * delta :=
      (div_lt_iff₀ hdelta).mp hN
    linarith
  intro t ht theta htheta hbudget v hv hpos hmass
  have hgood := hgrid N t ht (ht.2.trans hcover)
  exact hgood theta htheta hbudget v hv hpos hmass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_span_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_span_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_span_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_span_uniform

theorem w_span
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3)
    {a₀ a b tauMax : Real} (ha₀a : a₀ < a) (hab : a ≤ b)
    (hreg : Set.Icc a₀ b ⊆ D.regular) :
    ∃ L : Real, ∀ t ∈ Set.Icc a b,
      ∀ {theta : Real}, 0 < theta → theta + (t - a) < tauMax →
      ∀ {v : M → Real}, ContMDiff I 𝓘(Real) ∞ v →
        (∀ x : M, 0 < v x) →
        (∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M)
          (S.family.metric t))) = 1 →
        L ≤ flowW (I := I) (M := M) S t theta v := by
  obtain ⟨L, hL⟩ := w_span_uniform (I := I) (M := M)
    (tauMax := tauMax) S hS hDim ha₀a
  exact ⟨L, hL (b := b) hab hreg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.w_span then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.w_span"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.w_span ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.w_span

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
