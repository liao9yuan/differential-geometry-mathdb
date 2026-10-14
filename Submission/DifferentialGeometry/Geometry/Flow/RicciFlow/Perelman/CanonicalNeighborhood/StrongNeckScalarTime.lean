import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.SuperlevelMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.MetricTrace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TerminalSlope
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.MetricTraceComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps t : ℝ} {x : M}

private theorem hasDerivWithinAt_ricci_component_of_metric_jet
    {u r e0 e1 : ℝ → ℝ} {a b A B e2 : ℝ} (hab : a < b)
    (hu : ∀ s ∈ _root_.Set.Icc a b, HasDerivWithinAt u (-2 * r s) (_root_.Set.Icc a b) s)
    (hzero : ∀ s ∈ _root_.Set.Icc a b, e0 s = u s - (A + s * B))
    (hfirst : ∀ s ∈ _root_.Set.Icc a b, e1 s = derivWithin e0 (_root_.Set.Icc a b) s)
    (hsecond : HasDerivWithinAt e1 e2 (_root_.Set.Icc a b) b) :
    HasDerivWithinAt r (-(1 / 2 : ℝ) * e2) (_root_.Set.Icc a b) b := by
  have heq (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) :
      r s = -(1 / 2 : ℝ) * (e1 s + B) := by
    have href : HasDerivWithinAt (fun z : ℝ => A + z * B) B (_root_.Set.Icc a b) s := by
      have hh : HasDerivAt (fun z : ℝ => z * B) B s := by
        simpa only [one_mul, id_eq] using (hasDerivAt_id s).mul_const B
      exact (hh.const_add A).hasDerivWithinAt
    have hd := ((hu s hs).sub href).congr (fun z hz => hzero z hz) (hzero s hs)
    rw [hfirst s hs, hd.derivWithin ((uniqueDiffOn_Icc hab) s hs)]
    ring
  exact ((hsecond.add_const B).const_mul (-(1 / 2 : ℝ))).congr
    (fun s hs => heq s hs) (heq b ⟨hab.le,le_rfl⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_ricci_component_of_metric_jet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasDerivWithinAt_ricci_component_of_metric_jet target :: scope.openDecls } }

private def cylinderDomain (eps : ℝ) : TopologicalSpace.Opens Cylinder :=
  ⟨univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.cylinderDomain target :: scope.openDecls } }

private def StrongNeck.domainMap (nk : StrongNeck S eps x t) : cylinderDomain eps → M :=
  fun z => nk.map z.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
private theorem StrongNeck.domainMap_isLocalDiffeomorph (nk : StrongNeck S eps x t) :
    IsLocalDiffeomorph IC I3 ∞ nk.domainMap := by
  intro z
  exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val (cylinderDomain eps) z).comp
    I3 M (nk.map.isLocalDiffeomorphAt IC I3 ∞ (nk.domain z.property))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap_isLocalDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap_isLocalDiffeomorph target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
private theorem StrongNeck.domainMap_mfderiv (nk : StrongNeck S eps x t)
    (z : cylinderDomain eps) (v : TangentSpace IC z) :
    mfderiv IC I3 nk.domainMap z v = mfderiv IC I3 nk.map z.val v := by
  change mfderiv IC I3 (nk.map ∘ (Subtype.val : cylinderDomain eps → Cylinder)) z v = _
  have hd := (nk.map.contMDiffOn_toFun.contMDiffAt
    (nk.map.open_source.mem_nhds (nk.domain z.property))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  rw [mfderiv_comp z hd
    (DifferentialGeometry.hasMFDerivAt_subtype_val (cylinderDomain eps) z).mdifferentiableAt]
  simp only [ContinuousLinearMap.comp_apply, DifferentialGeometry.mfderiv_subtype_val_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.domainMap_mfderiv target :: scope.openDecls } }

private theorem StrongNeck.scalar_derivWithin_normalized_ge
    (hS : IsSolutionOn S) (nk : StrongNeck S eps x t)
    (hreg : ∀ s ∈ _root_.Set.Ioo (-1 : ℝ) 0, parabolicTime t (S.scalar t x) s ∈ D.regular) :
    ∃ P : SolutionOn (I := IC) (M := cylinderDomain eps)
        (RealTimeInterval.closed (-1) 0 (by norm_num)),
      (∀ r (z : cylinderDomain eps), P.scalar r z =
        (S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) (nk.map z.val)) ∧
      ∀ (z : cylinderDomain eps),
        2 * P.scalar 0 z ^ 2 ≤ 3 *
          (derivWithin (fun r => P.scalar r z) (_root_.Set.Iic 0) 0 + 2 * eps) := by
  let Q := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  let T := S.parabolicClosedWindow t Q 1 hQ (by norm_num)
  have hcarrier : _root_.Set.Icc (t - 1 / Q) t ⊆ D.carrier := by
    simpa only [one_div] using nk.time_domain
  have hregular : _root_.Set.Ioo (t - 1 / Q) t ⊆ D.regular := by
    intro r hr
    have hs : Q * (r - t) ∈ _root_.Set.Ioo (-1 : ℝ) 0 := by
      have hlo := (div_lt_iff₀ hQ).mp (show (-1 : ℝ) / Q < r - t by rw [neg_div]; linarith [hr.1])
      constructor <;> nlinarith [hr.2]
    have hh := hreg (Q * (r - t)) hs
    have heq : parabolicTime t Q (Q * (r - t)) = r := by
      unfold parabolicTime
      field_simp
      ring
    rwa [heq] at hh
  have hT : IsSolutionOn T := isSolutionOn_parabolicClosedWindow S hS hQ (by norm_num)
    hcarrier hregular
  let P := T.localPullback nk.domainMap nk.domainMap_isLocalDiffeomorph
  have hP : IsSolutionOn P := hT.localPullback nk.domainMap nk.domainMap_isLocalDiffeomorph
  have hscalar (r : ℝ) (z : cylinderDomain eps) : P.scalar r z =
      Q⁻¹ * S.scalar (t + r / Q) (nk.map z.val) := by
    rw [SolutionOn.localPullback_scalar]
    change metricScalarAt (scaleMetric Q hQ (S.base.metric (t + r / Q))) (nk.map z.val) = _
    rw [metricScalarAt_scaleMetric]
    rfl
  refine ⟨P, hscalar, ?_⟩
  intro z
  have hinner (r : ℝ) (v : Fin 2 → TangentSpace IC z) :
      (P.base.metric r).inner z (v 0) (v 1) = nk.comparison.pullback r z.val v := by
    rw [nk.comparison.pullback_eq r z.val z.property v]
    change (localPullMetric (T.base.metric r) nk.domainMap
      nk.domainMap_isLocalDiffeomorph).inner z (v 0) (v 1) = _
    rw [localPullMetric_inner, nk.domainMap_mfderiv, nk.domainMap_mfderiv]
    rfl
  have hmetric (r : ℝ) (hr : r ∈ _root_.Set.Icc (-1 : ℝ) 0) (v w : TangentSpace IC z) :
      HasDerivWithinAt (fun s => (P.base.metric s).inner z v w)
        (-2 * P.ricciAt r z (vec2 v w)) (_root_.Set.Icc (-1) 0) r :=
    metric_inner_hasDerivWithinAt_on_closed_interval P hP (by norm_num)
      Subset.rfl Subset.rfl hr z v w
  let B : Tensor0SSpace (I := IC) 2 z := nk.comparison.jet 2 0 z.val
  have hRic (v : Fin 2 → TangentSpace IC z) :
      HasDerivWithinAt (fun r => P.ricciAt r z v) (- (1 / 2 : ℝ) * B v)
        (_root_.Set.Icc (-1 : ℝ) 0) 0 := by
    let A := _root_.Inner.inner ℝ
      (show ThreeSpace from mfderiv I2 I3 (fun w : Sphere 2 => (w : ThreeSpace)) z.val.1 (v 0).1)
      (show ThreeSpace from mfderiv I2 I3 (fun w : Sphere 2 => (w : ThreeSpace)) z.val.1 (v 1).1)
    have hvec : vec2 (v 0) (v 1) = v := by funext k; fin_cases k <;> rfl
    apply hasDerivWithinAt_ricci_component_of_metric_jet (A := 2 * A + (v 0).2 * (v 1).2)
      (B := -2 * A) (e0 := fun r => nk.comparison.jet 0 r z.val v)
      (e1 := fun r => nk.comparison.jet 1 r z.val v) (by norm_num)
    · intro r hr
      simpa only [hvec] using hmetric r hr (v 0) (v 1)
    · intro r hr
      erw [nk.comparison.jet_zero r z.val v, ← hinner r v, nk.cylinder.inner_eq r hr.2]
      dsimp only [A]
      ring
    · intro r hr
      exact nk.comparison.jet_succ 0 r hr z.val z.property v
    · exact nk.hasDerivWithinAt_comparison_jet hS hreg 1 (by norm_num) z.val z.property v
  have htrace : |metricTracePair0SAt (P.base.metric 0) B| ≤ 4 * eps := by
    have hcmp := nk.comparison.equivalence 0 (by norm_num) z.val z.property
    have hlo (v : TangentSpace IC z) :
        (1 - eps) * ((nk.cylinder.metric 0).restrictOpen (cylinderDomain eps)).inner z v v ≤
          (P.base.metric 0).inner z v v := by
      rw [hinner 0 (fun _ => v)]
      exact (hcmp v).1
    have hb : Real.sqrt (normSq0S ((nk.cylinder.metric 0).restrictOpen (cylinderDomain eps)) z 2 B) ≤ eps := by
      exact nk.comparison.close 0 2 (by
        have hh : (4 : ℝ) ≤ eps⁻¹ := by
          rw [inv_eq_one_div]
          apply (le_div_iff₀ nk.eps_pos).mpr
          linarith [nk.eps_small]
        exact_mod_cast hh.trans (Nat.le_ceil eps⁻¹)) 0 (by norm_num) z.val z.property
    have hden : 0 < 1 - eps := by linarith [nk.eps_small]
    have hn := abs_metricTracePair0SAt_le_of_metric_lower_bound (P.base.metric 0)
      ((nk.cylinder.metric 0).restrictOpen (cylinderDomain eps)) z hden hlo B
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by
      simp [Module.finrank_prod]
    rw [hdim, Nat.cast_ofNat] at hn
    have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3 / (1 - eps))
    have hsmall : 3 / (1 - eps) * eps ≤ 4 * eps := by
      have heps : 0 ≤ eps := nk.eps_pos.le
      have hratio : 3 / (1 - eps) ≤ (4 : ℝ) := by
        apply (div_le_iff₀ hden).mpr
        linarith [nk.eps_small]
      exact mul_le_mul_of_nonneg_right hratio heps
    exact hn.trans (hmul.trans hsmall)
  have hh := scalar_derivWithin_Iic_ge_of_ricci_deriv P (by norm_num : (-1 : ℝ) < 0) B
    (hmetric 0 (by norm_num)) hRic htrace
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  simpa only [hdim, Nat.cast_ofNat, show (4 : ℝ) * eps / 2 = 2 * eps by ring] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_normalized_ge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_normalized_ge target :: scope.openDecls } }

theorem StrongNeck.scalar_sq_mul_third_lt_derivWithin
    (hS : IsSolutionOn S) (nk : StrongNeck S eps x t)
    (hreg : ∀ s ∈ _root_.Set.Ioo (-1 : ℝ) 0, parabolicTime t (S.scalar t x) s ∈ D.regular) :
    (1 / 3 : ℝ) * S.scalar t x ^ 2 <
      derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t := by
  obtain ⟨P, hscalar, hbound⟩ := nk.scalar_derivWithin_normalized_ge hS hreg
  have hz : (nk.center, (0 : ℝ)) ∈ cylinderDomain eps := by
    refine ⟨mem_univ _, ?_⟩
    constructor <;> linarith [inv_pos.mpr nk.eps_pos]
  let z : cylinderDomain eps := ⟨(nk.center,0), hz⟩
  have hzero : P.scalar 0 z = 1 := by
    rw [hscalar, zero_div, add_zero]
    change (S.scalar t x)⁻¹ * S.scalar t (nk.map (nk.center,0)) = 1
    rw [nk.center_eq]
    exact inv_mul_cancel₀ nk.Q_pos.ne'
  have hnear : _root_.Set.Icc (t - (S.scalar t x)⁻¹) t ∈ 𝓝[≤] t :=
    Icc_mem_nhdsLE (sub_lt_self t (inv_pos.mpr nk.Q_pos))
  have hdiff : DifferentiableWithinAt ℝ (fun r => S.scalar r x) (_root_.Set.Iic t) t :=
    (hS.scalarTime (show t ∈ _root_.Set.Icc (t - (S.scalar t x)⁻¹) t from
      ⟨sub_le_self t (inv_nonneg.mpr nk.Q_pos.le),le_rfl⟩) nk.time_domain x).mono_of_mem_nhdsWithin hnear
  have hfn : (fun r => P.scalar r z) =
      (fun r => (S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) x) := by
    funext r
    rw [hscalar]
    change (S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) (nk.map (nk.center,0)) = _
    rw [nk.center_eq]
  have hd := CanonicalNeighborhood.derivWithin_parabolic_scalar_Iic
    (fun r => S.scalar r x) t (S.scalar t x) nk.Q_pos hdiff
  have hh := hbound z
  rw [hzero, hfn, hd] at hh
  have hnorm : (1 / 3 : ℝ) < (S.scalar t x)⁻¹ ^ 2 *
      derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t := by
    nlinarith [nk.eps_small]
  have hmul := mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos nk.Q_pos)
  have hcancel : (S.scalar t x) ^ 2 * ((S.scalar t x)⁻¹ ^ 2 *
      derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t) =
      derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ nk.Q_pos.ne', one_pow, one_mul]
  rw [hcancel] at hmul
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_sq_mul_third_lt_derivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_sq_mul_third_lt_derivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_sq_mul_third_lt_derivWithin ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_sq_mul_third_lt_derivWithin

theorem StrongNeck.scalar_derivWithin_pos
    (hS : IsSolutionOn S) (nk : StrongNeck S eps x t)
    (hreg : ∀ s ∈ _root_.Set.Ioo (-1 : ℝ) 0, parabolicTime t (S.scalar t x) s ∈ D.regular) :
    0 < derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t :=
  (mul_pos (by norm_num : (0 : ℝ) < 1 / 3) (sq_pos_of_pos nk.Q_pos)).trans
    (nk.scalar_sq_mul_third_lt_derivWithin hS hreg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.scalar_derivWithin_pos

theorem scalar_le_max_terminal_of_strongNeck_above
    (hS : IsSolutionOn S) {a b q : ℝ} (x : M)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hneck : ∀ t ∈ _root_.Set.Ioo a b, q < S.scalar t x → ∃ eps : ℝ, Nonempty (StrongNeck S eps x t))
    (hregular : ∀ t ∈ _root_.Set.Ioo a b, q < S.scalar t x → ∀ s ∈ _root_.Set.Ioo (-1 : ℝ) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc a b) : S.scalar t x ≤ _root_.Max.max q (S.scalar b x) := by
  apply DifferentialGeometry.Analysis.le_max_endpoint_of_deriv_nonneg_above
    (fun s hs => (hS.scalarTime hs hslab x).continuousWithinAt) ?_ ht
  intro s hs hhigh
  obtain ⟨eps, ⟨nk⟩⟩ := hneck s hs hhigh
  have hd := (hS.scalarTime hs (Ioo_subset_Icc_self.trans hslab) x).differentiableAt
    (Ioo_mem_nhds hs.1 hs.2)
  refine ⟨hd, ?_⟩
  have hleft := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic s)
  rw [← hleft]
  exact (nk.scalar_derivWithin_pos hS (hregular s hs hhigh)).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_max_terminal_of_strongNeck_above then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_max_terminal_of_strongNeck_above"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_max_terminal_of_strongNeck_above ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_max_terminal_of_strongNeck_above

theorem scalar_le_terminal_of_strongNeck_above
    (hS : IsSolutionOn S) {a b q : ℝ} (x : M)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hneck : ∀ t ∈ _root_.Set.Ioo a b, q < S.scalar t x → ∃ eps : ℝ, Nonempty (StrongNeck S eps x t))
    (hregular : ∀ t ∈ _root_.Set.Ioo a b, q < S.scalar t x → ∀ s ∈ _root_.Set.Ioo (-1 : ℝ) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (hterminal : q ≤ S.scalar b x) {t : ℝ} (ht : t ∈ _root_.Set.Icc a b) :
    S.scalar t x ≤ S.scalar b x := by
  simpa only [max_eq_right hterminal] using
    scalar_le_max_terminal_of_strongNeck_above hS x hslab hneck hregular ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_terminal_of_strongNeck_above then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_terminal_of_strongNeck_above"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_terminal_of_strongNeck_above ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_le_terminal_of_strongNeck_above

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
