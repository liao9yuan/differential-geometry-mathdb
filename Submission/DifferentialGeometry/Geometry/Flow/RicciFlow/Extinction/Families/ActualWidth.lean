import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.OpenConnection
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ComponentFlow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BackgroundBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ClassWidth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.CanonicalClass
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FaceLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Submission.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
section CanonicalSlab

universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem positiveFreeContractibleClass_isEssential (o : TangentOrientationSection M) :
    IsEssentialFamilyClass (positiveFreeContractibleClass o) := by
  exact isEssentialFamilyClass_of_pi2_zero
    (fun q => (rfs_homotopy_groups q).1) (positiveFreeContractibleClass o)
    (fun q => positiveFreeContractibleClass_nontrivial o q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.positiveFreeContractibleClass_isEssential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.positiveFreeContractibleClass_isEssential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.positiveFreeContractibleClass_isEssential ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.positiveFreeContractibleClass_isEssential

theorem canonicalWidth_smooth_on_regular_slab
    (B : RicciBackground (I := ThreeModel) (M := M) D a b)
    (o : TangentOrientationSection M) :
    ContinuousOn (fun t => Width.canonicalWidth (B.family.metric t) o) (_root_.Set.Icc a b) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ epsilon > 0, ∃ delta > 0,
        ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h ≤ b →
          (Width.canonicalWidth (B.family.metric (t + h)) o -
            Width.canonicalWidth (B.family.metric t) o) / h ≤
            -2 * Real.pi - halfScalarMinimum B.family t *
              Width.canonicalWidth (B.family.metric t) o + epsilon) ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ v ∈ _root_.Set.Ioc t b,
        0 < 2 * Real.pi * (∫ u in t..v, areaIntegratingFactor B.family t u) ∧
        2 * Real.pi * (∫ u in t..v, areaIntegratingFactor B.family t u) ≤
          Width.canonicalWidth (B.family.metric t) o := by
  simpa only [Width.canonicalWidth] using rfs_smooth_class_width B
    (by simp [ThreeSpace]) (positiveFreeContractibleClass o)
    (positiveFreeContractibleClass_isEssential o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.canonicalWidth_smooth_on_regular_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.canonicalWidth_smooth_on_regular_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.canonicalWidth_smooth_on_regular_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.canonicalWidth_smooth_on_regular_slab

end CanonicalSlab

universe u

def componentHalfScalar (P : OrientedThreeStage.{u})
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) (t : ℝ) : ℝ :=
  _root_.InfSet.sInf (_root_.Set.range (fun x : (P.component c).Carrier => F.scalar t x.1)) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar

def componentFactor (P : OrientedThreeStage.{u})
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) (s t : ℝ) : ℝ :=
  Real.exp (∫ r in s..t, componentHalfScalar P F c r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor

def componentAffine (P : OrientedThreeStage.{u})
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) (s t z : ℝ) : ℝ :=
  (componentFactor P F c s t)⁻¹ *
    (z - 2 * Real.pi * ∫ r in s..t, componentFactor P F c s r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine

variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem incoming_component_solution (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier) :
    ∃ F : SolutionOn (I := ThreeModel) (M := (P.component c).Carrier)
        (RealTimeInterval.closedOpen a b G.lt),
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F ∧
      (∀ t ∈ _root_.Set.Ico a b, F.base.metric t = P.componentMetric (G.flow.base.metric t) c) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ x : (P.component c).Carrier,
        F.base.scalar t x = G.flow.base.scalar t x.1) ∧
      (∀ u ∈ _root_.Set.Ioo a b, ∀ v ∈ _root_.Set.Ioo u b,
        ∃ B : RicciBackground (I := ThreeModel) (M := (P.component c).Carrier)
            (RealTimeInterval.closedOpen a b G.lt) u v,
          B.family = F.base) := by
  let : ConnectedSpace (P.component c).Carrier := P.component_connected c
  obtain ⟨F, hF, hmetric, hscalar⟩ := incoming_component_native_solution G c
  refine ⟨F, hF, hmetric, hscalar, ?_⟩
  intro u hu v hv
  have hreg : _root_.Set.Icc u v ⊆ (RealTimeInterval.closedOpen a b G.lt).regular := by
    intro t ht
    exact ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
  obtain ⟨B, hB, _⟩ := rfs_csf_background F hF hv.1 hreg
  exact ⟨B, hB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_solution

theorem component_covDerivAlong (g : P.Metric) (c : ConnectedComponents P.Carrier)
    (gamma : ℝ → (P.component c).Carrier)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ gamma)
    (V : (r : ℝ) → TangentSpace ThreeModel (gamma r))
    (hV : ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun r => (⟨gamma r, V r⟩ : TangentBundle ThreeModel (P.component c).Carrier)))
    (r : ℝ) :
    (show TangentSpace ThreeModel (gamma r).1 from
      covDerivAlong (P.componentMetric g c) gamma V r) =
      covDerivAlong g (fun s => (gamma s).1)
        (fun s => (show TangentSpace ThreeModel (gamma s).1 from V s)) r := by
  let _ := hV
  exact covDerivAlong_restrictOpen g (P.componentOpen c) gamma V r hgamma.continuous.continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_covDerivAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_covDerivAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_covDerivAlong ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_covDerivAlong

private theorem componentHalfScalar_continuousOn {D : RealTimeInterval}
    (F : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (hF : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn F)
    (c : ConnectedComponents P.Carrier) :
    ContinuousOn (componentHalfScalar P F.base c) D.carrier := by
  have hraw : ContinuousOn (fun p : ℝ × P.Carrier => F.base.scalar p.1 p.2)
      (D.carrier ×ˢ (_root_.Set.univ : Set P.Carrier)) := by
    simpa only [SolutionOn.scalar] using hF.scalarCont
  have hmap : Continuous (fun p : D.carrier × (P.component c).Carrier =>
      ((p.1 : ℝ), p.2.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hscalar : Continuous (fun p : D.carrier × (P.component c).Carrier =>
      F.base.scalar p.1 p.2.1) :=
    hraw.comp_continuous
      (f := fun p : D.carrier × (P.component c).Carrier => ((p.1 : ℝ), p.2.1))
      hmap (fun p => ⟨p.1.property, _root_.Set.mem_univ _⟩)
  have hmin : Continuous (fun t : D.carrier => componentHalfScalar P F.base c t) := by
    have hc : Continuous (fun t : D.carrier =>
        sInf ((fun x : (P.component c).Carrier => F.base.scalar t x.1) '' _root_.Set.univ)) :=
      (isCompact_univ : IsCompact (_root_.Set.univ : Set (P.component c).Carrier)).continuous_sInf
        (f := fun (t : D.carrier) (x : (P.component c).Carrier) => F.base.scalar t x.1) hscalar
    simpa only [_root_.Set.image_univ, componentHalfScalar] using hc.div_const (2 : ℝ)
  exact continuousOn_iff_continuous_domRestrict.mpr hmin

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_continuousOn target :: scope.openDecls } }

theorem incoming_component_continuity (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    ContinuousOn (componentHalfScalar P G.flow.base c) (_root_.Set.Ico a b) ∧
      ContinuousOn (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC) (_root_.Set.Ico a b) := by
  exact ⟨componentHalfScalar_continuousOn G.flow G.equation c,
    Width.continuousOn_componentWidth_metricFamily P
      (RealTimeInterval.closedOpen a b G.lt) G.flow.base.metric G.equation.smoothMetric c hSC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_continuity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_continuity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_continuity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_continuity

theorem incoming_component_integrated_width (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    ∀ s ∈ _root_.Set.Ico a b, ∀ t ∈ _root_.Set.Ico s b,
      0 ≤ Width.componentWidth P (G.flow.base.metric t) c hSC ∧
      Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        componentAffine P G.flow.base c s t
          (Width.componentWidth P (G.flow.base.metric s) c hSC) ∧
      componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
  let := P.component_connected c
  let := hSC
  obtain ⟨F, _hF, hmetric, hscalar, hbackground⟩ := incoming_component_solution G c
  have hrho (r : ℝ) (hr : r ∈ _root_.Set.Ico a b) :
      halfScalarMinimum F.base r = componentHalfScalar P G.flow.base c r := by
    change _root_.InfSet.sInf (_root_.Set.range (F.base.scalar r)) / 2 =
      _root_.InfSet.sInf (_root_.Set.range (fun x : (P.component c).Carrier => G.flow.base.scalar r x.1)) / 2
    rw [show F.base.scalar r =
      (fun x : (P.component c).Carrier => G.flow.base.scalar r x.1) from
        funext (hscalar r hr)]
  have hwidth (r : ℝ) (hr : r ∈ _root_.Set.Ico a b) :
      Width.classWidth (F.base.metric r) (positiveFreeContractibleClass (P.component c).orientation) =
        Width.componentWidth P (G.flow.base.metric r) c hSC := by
    rw [hmetric r hr]
    rfl
  have hfactor {s t : ℝ} (hs : s ∈ _root_.Set.Ico a b) (ht : t ∈ _root_.Set.Ico s b) :
      areaIntegratingFactor F.base s t = componentFactor P G.flow.base c s t := by
    have hexp : areaIntegratingFactor F.base s t =
        Real.exp (∫ r in s..t, halfScalarMinimum F.base r) := by
      unfold areaIntegratingFactor halfScalarMinimum
      rw [intervalIntegral.integral_div]
      congr 1
      ring
    rw [hexp]
    unfold componentFactor
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [_root_.Set.uIcc_of_le ht.1] at hr
    exact hrho r ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩
  have hinterior {s t : ℝ} (hs : s ∈ _root_.Set.Ioo a b) (ht : t ∈ _root_.Set.Ioo s b) :
      componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
    obtain ⟨B, hB⟩ := hbackground s hs t ht
    have hess : IsEssentialFamilyClass (positiveFreeContractibleClass (P.component c).orientation) :=
      isEssentialFamilyClass_of_pi2_zero
        (fun q => (rfs_homotopy_groups q).1)
        (positiveFreeContractibleClass (P.component c).orientation)
        (fun q => positiveFreeContractibleClass_nontrivial (P.component c).orientation q)
    have h := (rfs_integrated_class_width B (by simp [ThreeSpace])
      (positiveFreeContractibleClass (P.component c).orientation) hess
      s ⟨le_rfl, ht.1.le⟩ t ⟨ht.1.le, le_rfl⟩).2.2
    rw [hB] at h
    have hs' : s ∈ _root_.Set.Ico a b := ⟨hs.1.le, hs.2⟩
    have ht' : t ∈ _root_.Set.Ico a b := ⟨hs.1.le.trans ht.1.le, ht.2⟩
    rw [hwidth s hs', hwidth t ht', hfactor hs' ⟨ht.1.le, ht.2⟩] at h
    have hJ : (∫ r in s..t, areaIntegratingFactor F.base s r) =
        ∫ r in s..t, componentFactor P G.flow.base c s r := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [_root_.Set.uIcc_of_le ht.1.le] at hr
      exact hfactor hs' ⟨hr.1, hr.2.trans_lt ht.2⟩
    rwa [hJ] at h
  obtain ⟨hrho_cont, hwidth_cont⟩ := incoming_component_continuity G c hSC
  intro s hs t ht
  have hnonneg := Width.componentWidth_nonneg P (G.flow.base.metric t) c hSC
  have hbound : componentFactor P G.flow.base c s t *
          Width.componentWidth P (G.flow.base.metric t) c hSC ≤
        Width.componentWidth P (G.flow.base.metric s) c hSC -
          2 * Real.pi * ∫ r in s..t, componentFactor P G.flow.base c s r := by
    rcases eq_or_lt_of_le ht.1 with rfl | hst
    · simp only [componentFactor, intervalIntegral.integral_same, Real.exp_zero,
        one_mul, _root_.MulZeroClass.mul_zero, sub_zero, le_refl]
    · apply integrated_comparison_le_endpoints hst
        (hrho_cont.mono (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩))
        (hwidth_cont.mono (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩))
      intro u hu v hv
      exact hinterior ⟨hs.1.trans_lt hu.1, hu.2.trans ht.2⟩
        ⟨hv.1, hv.2.trans ht.2⟩
  refine ⟨hnonneg, ?_, hbound⟩
  exact (le_inv_mul_iff₀ (Real.exp_pos _)).mpr hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_integrated_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_integrated_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_integrated_width ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_integrated_width

private theorem component_primitive_deriv {f : ℝ → ℝ} {l r s t : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc l r)) (hs : s ∈ _root_.Set.Icc l r) (ht : t ∈ _root_.Set.Icc l r) :
    HasDerivWithinAt (fun v => ∫ w in s..v, f w) (f t) (_root_.Set.Icc l r) t := by
  let : Fact (t ∈ _root_.Set.Icc l r) := ⟨ht⟩
  have hi : IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume s t :=
    (hf.mono (_root_.Set.uIcc_subset_Icc hs ht)).intervalIntegrable
  have hm : StronglyMeasurableAtFilter f (𝓝[_root_.Set.Icc l r] t) volume :=
    ⟨Icc l r, self_mem_nhdsWithin, hf.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right hi hm (hf t ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_primitive_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.component_primitive_deriv target :: scope.openDecls } }

private theorem componentFactor_continuousOn
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) {l r s : ℝ}
    (hf : ContinuousOn (componentHalfScalar P F c) (_root_.Set.Icc l r)) (hs : s ∈ _root_.Set.Icc l r) :
    ContinuousOn (componentFactor P F c s) (_root_.Set.Icc l r) := by
  intro t ht
  exact ((component_primitive_deriv hf hs ht).exp).continuousWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentFactor_continuousOn target :: scope.openDecls } }

private theorem componentAffine_hasDerivWithinAt
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (c : ConnectedComponents P.Carrier) {l r s t : ℝ}
    (hf : ContinuousOn (componentHalfScalar P F c) (_root_.Set.Icc l r))
    (hs : s ∈ _root_.Set.Icc l r) (ht : t ∈ _root_.Set.Icc l r) (z : ℝ) :
    HasDerivWithinAt (fun v => componentAffine P F c s v z)
      (-2 * Real.pi - componentHalfScalar P F c t * componentAffine P F c s t z)
      (_root_.Set.Icc l r) t := by
  have hcont := componentFactor_continuousOn F c hf hs
  have hfac : HasDerivWithinAt (componentFactor P F c s)
      (componentHalfScalar P F c t * componentFactor P F c s t) (_root_.Set.Icc l r) t := by
    change HasDerivWithinAt (fun v => Real.exp (∫ r in s..v, componentHalfScalar P F c r))
      (componentHalfScalar P F c t * Real.exp (∫ r in s..t, componentHalfScalar P F c r))
      (_root_.Set.Icc l r) t
    simpa only [mul_comm] using (component_primitive_deriv hf hs ht).exp
  have hne : componentFactor P F c s t ≠ 0 := (Real.exp_pos _).ne'
  have hd := (hfac.inv hne).mul
    ((hasDerivWithinAt_const t (_root_.Set.Icc l r) z).sub
      ((component_primitive_deriv hcont hs ht).const_mul (2 * Real.pi)))
  convert! hd using 1
  simp only [componentAffine, Pi.inv_apply, Pi.sub_apply]
  field_simp [hne]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine_hasDerivWithinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentAffine_hasDerivWithinAt target :: scope.openDecls } }

theorem incoming_component_smooth_width (G : P.IncomingSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    ContinuousOn (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC) (_root_.Set.Ico a b) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ epsilon > 0, ∃ delta > 0,
        ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h < b →
          (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
            Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
            -2 * Real.pi - componentHalfScalar P G.flow.base c t *
              Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon) ∧
      ∀ t ∈ _root_.Set.Ico a b, ∀ v ∈ _root_.Set.Ioo t b,
        0 < 2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ∧
        2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ≤
          Width.componentWidth P (G.flow.base.metric t) c hSC := by
  obtain ⟨hrho, hw⟩ := incoming_component_continuity G c hSC
  have hcmp := incoming_component_integrated_width G c hSC
  have hself (s z : ℝ) : componentAffine P G.flow.base c s s z = z := by
    simp only [componentAffine, componentFactor, intervalIntegral.integral_same,
      Real.exp_zero, inv_one, one_mul, _root_.MulZeroClass.mul_zero, sub_zero]
  refine ⟨hw, ?_, ?_⟩
  · intro t ht epsilon hepsilon
    let v := (t + b) / 2
    have htv : t < v := by dsimp [v]; linarith [ht.2]
    have hvb : v < b := by dsimp [v]; linarith [ht.2]
    have hsub : _root_.Set.Icc t v ⊆ _root_.Set.Ico a b :=
      fun r hr => ⟨ht.1.trans hr.1, hr.2.trans_lt hvb⟩
    let f : ℝ → ℝ := fun r => componentAffine P G.flow.base c t r
      (Width.componentWidth P (G.flow.base.metric t) c hSC)
    have hd : HasDerivWithinAt f
        (-2 * Real.pi - componentHalfScalar P G.flow.base c t *
          Width.componentWidth P (G.flow.base.metric t) c hSC) (_root_.Set.Icc t v) t := by
      simpa only [hself] using componentAffine_hasDerivWithinAt G.flow.base c
        (hrho.mono hsub) ⟨le_rfl, htv.le⟩ ⟨le_rfl, htv.le⟩
        (Width.componentWidth P (G.flow.base.metric t) c hSC)
    have hevent := hd.limsup_slope_le (by linarith :
      -2 * Real.pi - componentHalfScalar P G.flow.base c t *
        Width.componentWidth P (G.flow.base.metric t) c hSC <
      -2 * Real.pi - componentHalfScalar P G.flow.base c t *
        Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon)
    obtain ⟨delta, hdelta, hclose⟩ := Metric.mem_nhdsWithin_iff.mp hevent
    refine ⟨min delta (v - t), lt_min hdelta (sub_pos.mpr htv), ?_⟩
    intro h hh htb
    have hhd : h < delta := hh.2.trans_le (min_le_left _ _)
    have hhv : t + h ≤ v := by
      have h := hh.2.trans_le (min_le_right delta (v - t))
      linarith
    have hball : t + h ∈ Metric.ball t delta := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hh.1]
      exact hhd
    have hwindow : t + h ∈ _root_.Set.Icc t v \ {t} := by
      refine ⟨⟨by linarith [hh.1], hhv⟩, ?_⟩
      simp only [_root_.Set.mem_singleton_iff]
      linarith [hh.1]
    have hslope : (f (t + h) - f t) / h <
        -2 * Real.pi - componentHalfScalar P G.flow.base c t *
          Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon := by
      have hc := hclose ⟨hball, hwindow⟩
      change slope f t (t + h) < _ at hc
      simpa only [slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul,
        div_eq_mul_inv, mul_comm] using hc
    have hup := (hcmp t ht (t + h) ⟨by linarith [hh.1], htb⟩).2.1
    have heq : f t = Width.componentWidth P (G.flow.base.metric t) c hSC := hself _ _
    calc
      (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
          Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
          (f (t + h) - f t) / h := by
        rw [heq]
        exact div_le_div_of_nonneg_right (sub_le_sub_right hup _) hh.1.le
      _ ≤ _ := hslope.le
  · intro t ht v hv
    have hsub : _root_.Set.Icc t v ⊆ _root_.Set.Ico a b :=
      fun r hr => ⟨ht.1.trans hr.1, hr.2.trans_lt hv.2⟩
    have hfactor := componentFactor_continuousOn G.flow.base c
      (hrho.mono hsub) ⟨le_rfl, hv.1.le⟩
    have hpositive : 0 < ∫ r in t..v, componentFactor P G.flow.base c t r :=
      intervalIntegral.integral_pos hv.1 hfactor
        (fun _ _ => (Real.exp_pos _).le)
        ⟨t, ⟨le_rfl, hv.1.le⟩, Real.exp_pos _⟩
    obtain ⟨hW, _, hbound⟩ := hcmp t ht v ⟨hv.1.le, hv.2⟩
    have hprod : 0 ≤ componentFactor P G.flow.base c t v *
        Width.componentWidth P (G.flow.base.metric v) c hSC :=
      mul_nonneg (Real.exp_pos _).le hW
    exact ⟨mul_pos (mul_pos (by norm_num) Real.pi_pos) hpositive, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_smooth_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_smooth_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_smooth_width ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.incoming_component_smooth_width

private def closedSlabIncoming (G : P.ClosedSlab a b) : P.IncomingSlab a b where
  lt := G.lt
  flow := G.flow.timeRestrict (RealTimeInterval.closedOpen a b G.lt)
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.le⟩) (fun _ ht => ht)
  smoothUpTo := by
    intro p t ht
    obtain ⟨U, hU, hp, hsub, V, hV, htV, A, hA, heq⟩ :=
      G.smoothUpTo p t ⟨ht.1, ht.2.le⟩
    refine ⟨U, hU, hp, hsub, V, hV, htV, A, hA, ?_⟩
    intro s hs x hx i j
    exact heq s ⟨hs.1, ⟨hs.2.1, hs.2.2.le⟩⟩ x hx i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closedSlabIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closedSlabIncoming target :: scope.openDecls } }

theorem closed_component_smooth_width (G : P.ClosedSlab a b)
    (c : ConnectedComponents P.Carrier)
    (hSC : SimplyConnectedSpace (P.component c).Carrier) :
    ContinuousOn (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC) (_root_.Set.Icc a b) ∧
      (∀ t ∈ _root_.Set.Ico a b, ∀ epsilon > 0, ∃ delta > 0,
        ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h ≤ b →
          (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
            Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
            -2 * Real.pi - componentHalfScalar P G.flow.base c t *
              Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon) ∧
      ∀ t ∈ _root_.Set.Icc a b, ∀ v ∈ _root_.Set.Ioc t b,
        0 < 2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ∧
        2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ≤
          Width.componentWidth P (G.flow.base.metric t) c hSC := by
  let GI := closedSlabIncoming G
  have hincoming := incoming_component_smooth_width GI c hSC
  have hintegrated := incoming_component_integrated_width GI c hSC
  have hrho : ContinuousOn (componentHalfScalar P G.flow.base c) (_root_.Set.Icc a b) :=
    componentHalfScalar_continuousOn G.flow G.equation c
  have hw : ContinuousOn
      (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC) (_root_.Set.Icc a b) :=
    Width.continuousOn_componentWidth_metricFamily P
      (RealTimeInterval.closed a b G.lt.le) G.flow.base.metric G.equation.smoothMetric c hSC
  refine ⟨hw, ?_, ?_⟩
  · intro t ht epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hincoming.2.1 t ht epsilon hepsilon
    refine ⟨min delta (b - t), lt_min hdelta (sub_pos.mpr ht.2), ?_⟩
    intro h hh _htb
    have hsmall : h < b - t := hh.2.trans_le (min_le_right _ _)
    exact hbound h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩ (by linarith)
  · intro t ht v hv
    have hsub : _root_.Set.Icc t v ⊆ _root_.Set.Icc a b :=
      fun r hr => ⟨ht.1.trans hr.1, hr.2.trans hv.2⟩
    have hbound : componentFactor P G.flow.base c t v *
          Width.componentWidth P (G.flow.base.metric v) c hSC ≤
        Width.componentWidth P (G.flow.base.metric t) c hSC -
          2 * Real.pi * ∫ r in t..v, componentFactor P G.flow.base c t r := by
      apply integrated_comparison_le_endpoints hv.1 (hrho.mono hsub) (hw.mono hsub)
      intro s hs r hr
      exact (hintegrated s ⟨ht.1.trans hs.1.le, hs.2.trans_le hv.2⟩
        r ⟨hr.1.le, hr.2.trans_le hv.2⟩).2.2
    have hfactor := componentFactor_continuousOn G.flow.base c
      (hrho.mono hsub) ⟨le_rfl, hv.1.le⟩
    have hpositive : 0 < ∫ r in t..v, componentFactor P G.flow.base c t r :=
      intervalIntegral.integral_pos hv.1 hfactor
        (fun _ _ => (Real.exp_pos _).le)
        ⟨t, ⟨le_rfl, hv.1.le⟩, Real.exp_pos _⟩
    have hprod : 0 ≤ componentFactor P G.flow.base c t v *
        Width.componentWidth P (G.flow.base.metric v) c hSC :=
      mul_nonneg (Real.exp_pos _).le
        (Width.componentWidth_nonneg P (G.flow.base.metric v) c hSC)
    exact ⟨mul_pos (mul_pos (by norm_num) Real.pi_pos) hpositive, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closed_component_smooth_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closed_component_smooth_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closed_component_smooth_width ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.closed_component_smooth_width


theorem history_component_initial_width (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (c : ConnectedComponents (H.stage i.castSucc).Carrier)
    (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component c).Carrier) :
    Width.componentWidth (H.stage i.castSucc)
        ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) c hSC =
      Width.componentWidth (H.stage i.castSucc) (H.initialMetric i.castSucc) c hSC := by
  rw [H.event_initial]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_component_initial_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_component_initial_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_component_initial_width ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_component_initial_width

theorem history_incoming_component_dini (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (c : ConnectedComponents (H.stage i.castSucc).Carrier)
    (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component c).Carrier) :
    ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∀ epsilon > 0,
      ∃ delta > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h < H.time i.succ →
        (Width.componentWidth (H.stage i.castSucc)
            ((H.event i).incoming.flow.base.metric (t + h)) c hSC -
          Width.componentWidth (H.stage i.castSucc)
            ((H.event i).incoming.flow.base.metric t) c hSC) / h ≤
          -2 * Real.pi - componentHalfScalar (H.stage i.castSucc)
            (H.event i).incoming.flow.base c t *
            Width.componentWidth (H.stage i.castSucc)
              ((H.event i).incoming.flow.base.metric t) c hSC + epsilon :=
  (incoming_component_smooth_width (H.event i).incoming c hSC).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_incoming_component_dini then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_incoming_component_dini"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_incoming_component_dini ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.history_incoming_component_dini

theorem rfs_actual_smooth_width (H : ObservedHistory.{u}) :
    (∀ (i : Fin H.eventCount) (c : ConnectedComponents (H.stage i.castSucc).Carrier)
      (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component c).Carrier),
      let P := H.stage i.castSucc
      let G := (H.event i).incoming
      ContinuousOn (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC)
          (_root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) ∧
        (∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∀ epsilon > 0,
          ∃ delta > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h < H.time i.succ →
            (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
              Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
              -2 * Real.pi - componentHalfScalar P G.flow.base c t *
                Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon) ∧
        ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∀ v ∈ _root_.Set.Ioo t (H.time i.succ),
          0 < 2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ∧
            2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ≤
              Width.componentWidth P (G.flow.base.metric t) c hSC) ∧
    (∀ (hfinal : H.time (Fin.last H.eventCount) < H.horizon)
      (c : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (hSC : SimplyConnectedSpace ((H.stage (Fin.last H.eventCount)).component c).Carrier),
      let P := H.stage (Fin.last H.eventCount)
      let G := H.finalSlab hfinal
      ContinuousOn (fun t => Width.componentWidth P (G.flow.base.metric t) c hSC)
          (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon) ∧
        (∀ t ∈ _root_.Set.Ico (H.time (Fin.last H.eventCount)) H.horizon, ∀ epsilon > 0,
          ∃ delta > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) delta, t + h ≤ H.horizon →
            (Width.componentWidth P (G.flow.base.metric (t + h)) c hSC -
              Width.componentWidth P (G.flow.base.metric t) c hSC) / h ≤
              -2 * Real.pi - componentHalfScalar P G.flow.base c t *
                Width.componentWidth P (G.flow.base.metric t) c hSC + epsilon) ∧
        ∀ t ∈ _root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon, ∀ v ∈ _root_.Set.Ioc t H.horizon,
          0 < 2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ∧
            2 * Real.pi * (∫ r in t..v, componentFactor P G.flow.base c t r) ≤
              Width.componentWidth P (G.flow.base.metric t) c hSC) ∧
    (∀ (i : Fin H.eventCount) (c : ConnectedComponents (H.stage i.castSucc).Carrier)
      (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component c).Carrier),
      Width.componentWidth (H.stage i.castSucc)
          ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) c hSC =
        Width.componentWidth (H.stage i.castSucc) (H.initialMetric i.castSucc) c hSC) ∧
    ∀ (hfinal : H.time (Fin.last H.eventCount) < H.horizon)
      (c : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
      (hSC : SimplyConnectedSpace ((H.stage (Fin.last H.eventCount)).component c).Carrier),
      Width.componentWidth (H.stage (Fin.last H.eventCount))
          ((H.finalSlab hfinal).flow.base.metric (H.time (Fin.last H.eventCount))) c hSC =
        Width.componentWidth (H.stage (Fin.last H.eventCount))
          (H.initialMetric (Fin.last H.eventCount)) c hSC := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i c hSC
    exact incoming_component_smooth_width (H.event i).incoming c hSC
  · intro hfinal c hSC
    exact closed_component_smooth_width (H.finalSlab hfinal) c hSC
  · exact history_component_initial_width H
  · intro hfinal c hSC
    rw [H.final_initial]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_actual_smooth_width then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_actual_smooth_width"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_actual_smooth_width ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.rfs_actual_smooth_width

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
