import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.TailVariation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityComposition
import Submission.DifferentialGeometry.Analysis.Integration.Integral.MovingEndpointDerivative
import Submission.DifferentialGeometry.Analysis.Calculus.UpperSupport.Reparametrization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

section Calculus

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance temporalActionTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionTopology
local instance temporalActionCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionCharted
local instance temporalActionSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSmooth
local instance temporalActionT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionT2
local instance temporalActionSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalActionSigma

omit [I.Boundaryless] in
private theorem contMDiff_exponential_reparametrization
    (gamma : ℝ → F.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma) (c : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => gamma (c + Real.exp (-z.1) * (z.2 - c))) := by
  apply hgamma.comp
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, contMDiff_iff_contDiff]
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.contMDiff_exponential_reparametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.contMDiff_exponential_reparametrization target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem continuousOn_lVelocity_real_parameter_family
    {alpha : Real × Real → F.M} {V : Set Real} {K : Set Real}
    (hVopen : IsOpen V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1 alpha (V ×ˢ K)) :
    ContinuousOn
      (fun q : Real × Real ↦
        (Bundle.TotalSpace.mk' E (E := TangentSpace I)
          (alpha q)
          (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) :
            TangentBundle I F.M)) (V ×ˢ K) := by
  let J := 𝓘(Real, Real).prod 𝓘(Real, Real)
  let U := V ×ˢ K
  have hUopen : IsOpen U := hVopen.prod hKopen
  have htm :=
    halpha.continuousOn_tangentMapWithin le_rfl hUopen.uniqueMDiffOn
  have hunit : ContMDiff J J.tangent ∞
      (fun q : Real × Real ↦
        (Bundle.TotalSpace.mk' (Real × Real) q ((0 : Real), (1 : Real)) :
          TangentBundle J (Real × Real))) := by
    have hE : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun z : Real ↦
          (Bundle.TotalSpace.mk' Real z (0 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (0 : Real))).mpr contDiff_const
    have hR : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
        (fun r : Real ↦
          (Bundle.TotalSpace.mk' Real r (1 : Real) : TangentBundle 𝓘(Real, Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have hpair := (hE.comp contMDiff_fst).prodMk (hR.comp contMDiff_snd)
    have hsymm : ContMDiff
        (𝓘(Real, Real).tangent.prod 𝓘(Real, Real).tangent) J.tangent ∞
        ((equivTangentBundleProd 𝓘(Real, Real) Real
          𝓘(Real, Real) Real).symm) :=
      contMDiff_equivTangentBundleProd_symm
    change ContMDiff J J.tangent ∞
      ((equivTangentBundleProd 𝓘(Real, Real) Real
        𝓘(Real, Real) Real).symm ∘ fun q : Real × Real ↦
          ((Bundle.TotalSpace.mk' Real q.1 (0 : Real) : TangentBundle 𝓘(Real, Real) Real),
            (Bundle.TotalSpace.mk' Real q.2 (1 : Real) :
              TangentBundle 𝓘(Real, Real) Real)))
    exact hsymm.comp hpair
  have hcomp : ContinuousOn
      (fun q : Real × Real ↦ tangentMapWithin J I alpha U
        (Bundle.TotalSpace.mk' (Real × Real) q ((0 : Real), (1 : Real)))) U :=
    htm.comp hunit.continuous.continuousOn (fun _ hq ↦ hq)
  refine hcomp.congr ?_
  intro q hq
  have hwithin : mfderivWithin J I alpha U q = mfderiv J I alpha q :=
    mfderivWithin_of_isOpen hUopen hq
  have hdiff : MDifferentiableAt J I alpha q :=
    ((halpha q hq).contMDiffAt (hUopen.mem_nhds hq)).mdifferentiableAt (by simp)
  have hsplit := mfderiv_prod_eq_add_apply
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := alpha) (p := q) (v := ((0 : Real), (1 : Real))) hdiff
  have hzero :
      mfderiv 𝓘(Real, Real) I (fun z : Real ↦ alpha (z, q.2)) q.1 (0 : Real) = 0 :=
    (mfderiv 𝓘(Real, Real) I (fun z : Real ↦ alpha (z, q.2)) q.1).map_zero
  change Bundle.TotalSpace.mk' E (E := TangentSpace I) (alpha q)
      (lVelocity (I := I) (fun s ↦ alpha (q.1, s)) q.2) =
    tangentMapWithin J I alpha U
      (Bundle.TotalSpace.mk' (Real × Real) q ((0 : Real), (1 : Real)))
  simp only [tangentMapWithin, hwithin]
  refine Bundle.TotalSpace.ext rfl ?_
  exact heq_of_eq (by
    simpa only [lVelocity, hzero, zero_add] using hsplit.symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuousOn_lVelocity_real_parameter_family
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuousOn_lVelocity_real_parameter_family target :: scope.openDecls } }


omit [I.Boundaryless] in
private theorem continuous_lRegularizedLagrangian_real_parameter
    (alpha : ℝ × ℝ → F.M)
    (halpha : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 1 alpha) :
    Continuous (fun z : ℝ × ℝ => lRegularizedLagrangian F.S 0
      (fun s => alpha (z.1, s)) z.2) := by
  let timeLift : ℝ × ℝ → {t : ℝ // t ∈ ancientTimeInterval.carrier} :=
    fun z => ⟨0 - z.2 ^ 2, by
      simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
        neg_nonpos.mpr (sq_nonneg z.2)⟩
  let velocityLift : ℝ × ℝ → TangentBundle I F.M := fun z =>
    Bundle.TotalSpace.mk' E (E := TangentSpace I) (alpha z)
      (lVelocity (I := I) (fun s => alpha (z.1, s)) z.2)
  have htime : Continuous timeLift :=
    (continuous_const.sub (continuous_snd.pow 2)).subtype_mk _
  have hvel : Continuous velocityLift := by
    have hv := continuousOn_lVelocity_real_parameter_family F
      (V := Set.univ) (K := Set.univ) isOpen_univ isOpen_univ halpha.contMDiffOn
    simpa only [_root_.Set.univ_prod_univ, continuousOn_univ, velocityLift] using hv
  have hbase : Continuous alpha := halpha.continuous
  have hquad : Continuous
      (metricTimeBundleQuad (I := I) (M := F.M) F.S.family.metric
        ancientTimeInterval.carrier) :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := F.M) F.S.family.metric F.isSolution.smoothMetric
      (K := ancientTimeInterval.carrier) (fun _ ht => ht)
  have hkin0 := hquad.comp (htime.prodMk hvel)
  have hkin : Continuous (fun z : ℝ × ℝ =>
      (F.S.base.metric (0 - z.2 ^ 2)).inner (alpha z)
        (lVelocity (I := I) (fun s => alpha (z.1, s)) z.2)
        (lVelocity (I := I) (fun s => alpha (z.1, s)) z.2)) := hkin0
  let hSc : ScalarSTContOn (I := I) (M := F.M) F.S := ⟨F.isSolution.scalarCont⟩
  have hscalarBase : Continuous
      (fun z : {t : ℝ // t ∈ ancientTimeInterval.carrier} × F.M =>
        F.S.scalar z.1.1 z.2) := hSc.continuous_subtype
  have hscalar0 := hscalarBase.comp (htime.prodMk hbase)
  have hscalar : Continuous (fun z : ℝ × ℝ =>
      F.S.scalar (0 - z.2 ^ 2) (alpha z)) := hscalar0
  have hlag : Continuous (fun z : ℝ × ℝ =>
      (1 / 2 : ℝ) * (F.S.base.metric (0 - z.2 ^ 2)).inner (alpha z)
        (lVelocity (I := I) (fun s => alpha (z.1, s)) z.2)
        (lVelocity (I := I) (fun s => alpha (z.1, s)) z.2) +
      2 * z.2 ^ 2 * F.S.scalar (0 - z.2 ^ 2) (alpha z)) :=
    (continuous_const.mul hkin).add
      ((continuous_const.mul (continuous_snd.pow 2)).mul hscalar)
  exact hlag

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lRegularizedLagrangian_real_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lRegularizedLagrangian_real_parameter target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem continuous_lRegularizedLagrangian_exponential_reparametrization
    (gamma : ℝ → F.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma) (c : ℝ) :
    Continuous (fun z : ℝ × ℝ => lRegularizedLagrangian F.S 0
      (fun s => gamma (c + Real.exp (-z.1) * (s - c))) z.2) :=
  continuous_lRegularizedLagrangian_real_parameter F
    (fun z : ℝ × ℝ => gamma (c + Real.exp (-z.1) * (z.2 - c)))
    ((contMDiff_exponential_reparametrization F gamma hgamma c).of_le (by decide))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lRegularizedLagrangian_exponential_reparametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.continuous_lRegularizedLagrangian_exponential_reparametrization target :: scope.openDecls } }

private theorem hasDerivAt_lRegularizedAction_fixed_exponential_reparametrization
    (gamma : ℝ → F.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 gamma (_root_.Set.Icc c b)) :
    HasDerivAt
      (fun u : ℝ => lRegularizedAction F.S 0
        (fun s => gamma (c + Real.exp (-u) * (s - c))) c b)
      (-(b - c) * lRegularizedSpeedSq F.S 0 gamma b) 0 := by
  let f : ℝ → ℝ → F.M := fun u s => gamma (c + Real.exp (-u) * (s - c))
  have hfTop : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : ℝ × ℝ => f z.1 z.2) :=
    contMDiff_exponential_reparametrization F gamma hgamma c
  have hf : IsSmoothVariation (I := I) f := hfTop.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfzero : f 0 = gamma := by
    funext s
    simp only [f, neg_zero, Real.exp_zero, one_mul, add_sub_cancel]
  have hfix : lVelocity (I := I) (fun u => f u c) 0 = 0 := by
    have heq : (fun u => f u c) = fun _ => gamma c := by
      funext u
      simp only [f, sub_self, _root_.MulZeroClass.mul_zero, add_zero]
    rw [heq, lVelocity, mfderiv_const]
    rfl
  have hvelocity : lVelocity (I := I) (fun u => f u b) 0 =
      (-(b - c)) • lVelocity (I := I) gamma b := by
    let r : ℝ → ℝ := fun u => c + Real.exp (-u) * (b - c)
    have hrzero : r 0 = b := by simp only [r, neg_zero, Real.exp_zero, one_mul, add_sub_cancel]
    have hr : HasDerivAt r (-(b - c)) 0 := by
      have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
        simpa only [Function.comp_def, neg_zero, Real.exp_zero, one_mul] using
          (Real.hasDerivAt_exp (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      simpa only [r, neg_one_mul] using (hneg.mul_const (b - c)).const_add c
    have h := lVelocity_comp_of_hasDerivAt
      (hgamma.contMDiffAt.mdifferentiableAt (by simp) :
        MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (r 0)) hr
    have h' : lVelocity (I := I) (gamma ∘ r) 0 =
        (-(b - c)) • lVelocity (I := I) gamma b := by
      exact h.trans (congrArg (fun t : ℝ => (-(b - c)) •
        (lVelocity (I := I) gamma t : E)) hrzero)
    exact h'
  have hregular : ∀ s ∈ _root_.Set.uIcc c b, 0 - s ^ 2 ∈ ancientTimeInterval.regular := by
    intro s hs
    rw [_root_.Set.uIcc_of_le hcb.le] at hs
    rw [ancientTimeInterval_regular, _root_.Set.mem_Iio, zero_sub]
    exact neg_neg_of_pos (sq_pos_of_pos (hc.trans_le hs.1))
  have hfirst := lRegularizedAction_first_variation F.S F.isSolution 0 f hf c b hregular
  have heuler : (∫ s in c..b, lRegularizedEulerPair F.S 0 gamma s
      (lVelocity (I := I) (fun u => f u s) 0)) = 0 := by
    calc
      _ = ∫ _s in c..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ _root_.Set.Icc c b := by simpa only [_root_.Set.uIcc_of_le hcb.le] using hs
        simp only [lRegularizedEulerPair, (hgeo s hs').2.2.2, sub_self, map_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hfzero] at hfirst
  have hzero : (F.S.base.metric (0 - c ^ 2)).inner (gamma c)
      (0 : E) (lVelocity (I := I) gamma c) = 0 := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := (F.S.base.metric (0 - c ^ 2)).inner (gamma c)
    change B 0 (lVelocity (I := I) gamma c) = 0
    exact congrArg (fun L : E →L[ℝ] ℝ => L (lVelocity (I := I) gamma c)) B.map_zero
  have hfixed : HasDerivAt (fun u => lRegularizedAction F.S 0 (f u) c b)
      (-(b - c) * lRegularizedSpeedSq F.S 0 gamma b) 0 := by
    simp only [hfix, hvelocity, sub_zero, heuler,
      map_smul, smul_apply, smul_eq_mul] at hfirst
    apply hfirst.congr_deriv
    change -(b - c) * lRegularizedSpeedSq F.S 0 gamma b -
      (F.S.base.metric (0 - c ^ 2)).inner (gamma c) (0 : E)
        (lVelocity (I := I) gamma c) =
      -(b - c) * lRegularizedSpeedSq F.S 0 gamma b
    rw [hzero, sub_zero]
  exact hfixed

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_fixed_exponential_reparametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_fixed_exponential_reparametrization target :: scope.openDecls } }

theorem hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient
    (gamma : ℝ → F.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 gamma (_root_.Set.Icc c b)) :
    HasDerivAt
      (fun u : ℝ => lRegularizedAction F.S 0
        (fun s => gamma (c + Real.exp (-u) * (s - c))) c
        (c + Real.exp u * (b - c)))
      ((b - c) * (lRegularizedLagrangian F.S 0 gamma b -
        lRegularizedSpeedSq F.S 0 gamma b)) 0 := by
  let f : ℝ → ℝ → F.M := fun u s => gamma (c + Real.exp (-u) * (s - c))
  let g : ℝ → ℝ := fun u => c + Real.exp u * (b - c)
  have hfzero : f 0 = gamma := by
    funext s
    simp only [f, neg_zero, Real.exp_zero, one_mul, add_sub_cancel]
  have hgzero : g 0 = b := by simp only [g, Real.exp_zero, one_mul, add_sub_cancel]
  have hg : HasDerivAt g (b - c) 0 := by
    simpa only [g, Real.exp_zero, one_mul] using
      ((Real.hasDerivAt_exp (0 : ℝ)).mul_const (b - c)).const_add c
  have hfixed : HasDerivAt (fun u => lRegularizedAction F.S 0 (f u) c b)
      (-(b - c) * lRegularizedSpeedSq F.S 0 gamma b) 0 :=
    hasDerivAt_lRegularizedAction_fixed_exponential_reparametrization
      F gamma hgamma hc hcb hgeo
  have hlag : Continuous (fun z : ℝ × ℝ =>
      lRegularizedLagrangian F.S 0 (f z.1) z.2) :=
    continuous_lRegularizedLagrangian_exponential_reparametrization F gamma hgamma c
  have hint (u a d : ℝ) : IntervalIntegrable
      (lRegularizedLagrangian F.S 0 (f u)) _root_.MeasureTheory.MeasureSpace.volume a d :=
    (Continuous.uncurry_left (f := fun u s => lRegularizedLagrangian F.S 0 (f u) s)
      u hlag).intervalIntegrable a d
  have h := DifferentialGeometry.Analysis.Calculus.hasDerivAt_parametric_integral_right
    hlag.continuousAt
    (by simpa only [lRegularizedAction, hgzero] using hfixed)
    hg (Filter.Eventually.of_forall fun u => hint u c (g 0))
    (Filter.Eventually.of_forall fun u => hint u (g 0) (g u))
  change HasDerivAt (fun u => lRegularizedAction F.S 0 (f u) c (g u)) _ 0 at h
  apply h.congr_deriv
  rw [hgzero, hfzero, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient

end Calculus

section InnerProduct

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance temporalInnerTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerTopology
local instance temporalInnerCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerCharted
local instance temporalInnerSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSmooth
local instance temporalInnerT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerT2
local instance temporalInnerSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalInnerSigma

private theorem exists_lCost_time_upper_support_exponential_of_ancient_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {b : ℝ} (hb : 0 < b) :
    ∃ c ∈ _root_.Set.Ioo 0 b, ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      phi 0 = lCost F.S 0 p q (b ^ 2) ∧
      (∀ u, lCost F.S 0 p q ((c + Real.exp u * (b - c)) ^ 2) ≤ phi u) ∧
      HasDerivAt phi ((b - c) * d) 0 ∧
      -(3 * lCost F.S 0 p q (b ^ 2)) / b ≤ d := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨alpha, halpha, hstart, hend, hgeo, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p q (sq_pos_of_pos hb)
  rw [Real.sqrt_sq hb.le] at hend hgeo hcost
  obtain ⟨c, hc, gamma, hgamma, hgammaGeo, hgammaEq, hgammaVel⟩ :=
    exists_global_lRegularizedGeodesic_smooth_tail F.S F.isSolution 0 hb hgeo
  let f : ℝ → ℝ → F.M := fun u s => gamma (c + Real.exp (-u) * (s - c))
  let g : ℝ → ℝ := fun u => c + Real.exp u * (b - c)
  let phi : ℝ → ℝ := fun u => lRegularizedAction F.S 0 alpha 0 c +
    lRegularizedAction F.S 0 (f u) c (g u)
  let d : ℝ := lRegularizedLagrangian F.S 0 gamma b -
    lRegularizedSpeedSq F.S 0 gamma b
  have hfzero : f 0 = gamma := by
    funext s
    simp only [f, neg_zero, Real.exp_zero, one_mul, add_sub_cancel]
  have hgzero : g 0 = b := by simp only [g, Real.exp_zero, one_mul, add_sub_cancel]
  have hgammaEnd : gamma b = q := (hgammaEq ⟨hc.2.le, le_rfl⟩).trans hend
  have hgammaNode : gamma c = alpha c := hgammaEq ⟨le_rfl, hc.2.le⟩
  have hnode (u : ℝ) : alpha c = f u c := by
    simp only [f, sub_self, _root_.MulZeroClass.mul_zero, add_zero, hgammaNode]
  have hterminal (u : ℝ) : f u (g u) = q := by
    dsimp only [f, g]
    rw [add_sub_cancel_left, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_mul, add_sub_cancel, hgammaEnd]
  have hspan (u : ℝ) : c < g u := by
    dsimp only [g]
    exact lt_add_of_pos_right c (mul_pos (Real.exp_pos u) (sub_pos.mpr hc.2))
  have hback (s : ℝ) : 0 - s ^ 2 ∈ ancientTimeInterval.carrier := by
    simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg s)
  have hint (a e : ℝ) : IntervalIntegrable
      (lRegularizedLagrangian F.S 0 alpha) _root_.MeasureTheory.MeasureSpace.volume a e :=
    lRegLag_integrable_on_carrier F.S F.isSolution.smoothMetric
      ⟨F.isSolution.scalarCont⟩ 0 a e alpha halpha (fun s _ => hback s)
  have hcentral : lRegularizedAction F.S 0 gamma c b =
      lRegularizedAction F.S 0 alpha c b := by
    apply lRegularizedAction_congr
    intro s hs
    rw [_root_.Set.uIoo_of_le hc.2.le] at hs
    exact hgammaEq ⟨hs.1.le, hs.2.le⟩
  have htouch : phi 0 = lCost F.S 0 p q (b ^ 2) := by
    dsimp only [phi]
    rw [hfzero, hgzero, hcentral,
      lRegularizedAction_add F.S 0 alpha 0 c b (hint 0 c) (hint c b), hcost, hend]
  have hupper (u : ℝ) : lCost F.S 0 p q ((g u) ^ 2) ≤ phi u := by
    have hfu : ContMDiff 𝓘(ℝ, ℝ) I 1 (f u) := by
      apply (hgamma.of_le (by decide)).comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
    have h := lCost_le_join_on_carrier_of_bounded_rm F.S F.isSolution 0 (g u)
      hc.1 (hspan u) alpha (f u) halpha.contMDiffOn hfu.contMDiffOn (hnode u)
      (fun s _ => hback s) ⟨K, fun t ht y => hK t ht.2 y⟩
    simpa only [hstart, hterminal, phi] using h
  have hderiv : HasDerivAt phi ((b - c) * d) 0 :=
    (hasDerivAt_lRegularizedAction_exponential_reparametrization_of_ancient
      F gamma hgamma hc.1 hc.2 hgammaGeo).const_add
        (lRegularizedAction F.S 0 alpha 0 c)
  refine ⟨c, hc, phi, d, htouch, hupper, hderiv, ?_⟩
  have hlag := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    F hF alpha halpha hb.le (fun r hr => hgeo r ⟨hr.1, hr.2.le⟩)
  have hcostq : lRegularizedAction F.S 0 alpha 0 b =
      lCost F.S 0 p q (b ^ 2) := by simpa only [hend] using hcost
  rw [hcostq] at hlag
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  have hscalar : 0 ≤ F.S.scalar (-(b ^ 2)) (alpha b) :=
    (hB _ (neg_nonpos.mpr (sq_nonneg b)) (alpha b)).1
  have hpoint : gamma b = alpha b := hgammaEq ⟨hc.2.le, le_rfl⟩
  have hgammaS : lRegularizedSpeedSq F.S 0 gamma b =
      lRegularizedSpeedSq F.S 0 alpha b := by
    unfold lRegularizedSpeedSq
    rw [hgammaVel]
    exact congrArg (fun x : F.M => (F.S.base.metric (0 - b ^ 2)).inner x
      (lVelocity (I := I) alpha b) (lVelocity (I := I) alpha b)) hpoint
  have hgammaL : lRegularizedLagrangian F.S 0 gamma b =
      lRegularizedLagrangian F.S 0 alpha b := by
    change (1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 gamma b +
      2 * b ^ 2 * F.S.scalar (0 - b ^ 2) (gamma b) =
      (1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha b +
      2 * b ^ 2 * F.S.scalar (0 - b ^ 2) (alpha b)
    rw [hgammaS, hpoint]
  apply (div_le_iff₀ hb).mpr
  dsimp only [d]
  rw [hgammaL, hgammaS]
  dsimp only [lRegularizedLagrangian, lRegularizedSpeedSq] at hlag ⊢
  rw [zero_sub] at hlag ⊢
  nlinarith [mul_nonneg (pow_nonneg hb.le 3) hscalar]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient_of_innerProductSpace target :: scope.openDecls } }

end InnerProduct

section Normed

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance temporalTransferTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferTopology
local instance temporalTransferCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferCharted
local instance temporalTransferSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSmooth
local instance temporalTransferT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferT2
local instance temporalTransferSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.temporalTransferSigma

theorem exists_lCost_time_upper_support_exponential_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {b : ℝ} (hb : 0 < b) :
    ∃ c ∈ _root_.Set.Ioo 0 b, ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      phi 0 = lCost F.S 0 p q (b ^ 2) ∧
      (∀ u, lCost F.S 0 p q ((c + Real.exp u * (b - c)) ^ 2) ≤ phi u) ∧
      HasDerivAt phi ((b - c) * d) 0 ∧
      -(3 * lCost F.S 0 p q (b ^ 2)) / b ≤ d := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  obtain ⟨c, hc, phi, d, htouch, hupper, hderiv, hbound⟩ :=
    exists_lCost_time_upper_support_exponential_of_ancient_of_innerProductSpace G hG p q hb
  have hcost (tau : ℝ) : lCost G.S 0 p q tau = lCost F.S 0 p q tau := by
    change lCost (F.S.pullback Phi.symm) 0 p q tau = lCost F.S 0 p q tau
    exact lCost_pullback F.S Phi.symm 0 p q tau
  refine ⟨c, hc, phi, d, ?_, ?_, hderiv, ?_⟩
  · exact htouch.trans (hcost (b ^ 2))
  · intro u
    rw [← hcost]
    exact hupper u
  · rw [← hcost]
    exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_exponential_of_ancient

theorem exists_lCost_time_upper_support_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {b : ℝ} (hb : 0 < b) :
    ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      phi b = lCost F.S 0 p q (b ^ 2) ∧
      (fun r => lCost F.S 0 p q (r ^ 2)) ≤ᶠ[𝓝 b] phi ∧
      HasDerivAt phi d b ∧
      -(3 * lCost F.S 0 p q (b ^ 2)) / b ≤ d := by
  obtain ⟨c, hc, phi, d, htouch, hupper, hderiv, hbound⟩ :=
    exists_lCost_time_upper_support_exponential_of_ancient F hF p q hb
  obtain ⟨psi, hpsi, hpsiUpper, hpsiDeriv⟩ :=
    DifferentialGeometry.Analysis.Calculus.exists_upper_support_of_exp_reparametrization
      (C := fun r => lCost F.S 0 p q (r ^ 2))
      hc.2 htouch (Eventually.of_forall hupper) hderiv
  exact ⟨psi, d, hpsi, hpsiUpper, hpsiDeriv, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_lCost_time_upper_support_of_ancient

end Normed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
