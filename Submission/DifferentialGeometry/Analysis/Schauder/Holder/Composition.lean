import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X Y F : Type*} [MetricSpace X] [MetricSpace Y]
  [NormedAddCommGroup F]

omit [MetricSpace X] [MetricSpace Y] in
theorem eSupNormOn_comp_le_of_mapsTo
    {s : Set X} {t : Set Y} (phi : X → Y) (f : Y → F)
    (hphi : _root_.Set.MapsTo phi s t) :
    eSupNormOn s (f ∘ phi) ≤ eSupNormOn t f := by
  rw [eSupNormOn_le]
  intro x hx
  exact norm_le_eSupNormOn t f (phi x) (hphi hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eSupNormOn_comp_le_of_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eSupNormOn_comp_le_of_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eSupNormOn_comp_le_of_mapsTo ``Submission.DifferentialGeometry.Analysis.Schauder.eSupNormOn_comp_le_of_mapsTo

theorem holderWith_restrict_comp_of_lipschitzWith
    {s : Set X} {t : Set Y} {L K alpha : NNReal}
    (phi : X → Y) (f : Y → F)
    (hphi : LipschitzWith L phi) (hst : _root_.Set.MapsTo phi s t)
    (hf : HolderWith K alpha (t.domRestrict f)) :
    HolderWith (K * L ^ (alpha : Real)) alpha (s.domRestrict (f ∘ phi)) := by
  let phi' : s → t := fun x ↦ ⟨phi x, hst x.2⟩
  have hphi' : LipschitzWith L phi' := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hphi.dist_le_mul x.1 y.1
  have hcomp := hf.comp hphi'.holderWith
  have heq : t.domRestrict f ∘ phi' = s.domRestrict (f ∘ phi) := by
    rfl
  rw [heq] at hcomp
  simpa only [mul_one] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_of_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_of_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_of_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_of_lipschitzWith

theorem eHolderSeminormOn_comp_le_of_lipschitzWith
    {s : Set X} {t : Set Y} {L K alpha : NNReal}
    (phi : X → Y) (f : Y → F)
    (hphi : LipschitzWith L phi) (hst : _root_.Set.MapsTo phi s t)
    (hf : eHolderSeminormOn alpha t f ≤ K) :
    eHolderSeminormOn alpha s (f ∘ phi) ≤
      ((K * L ^ (alpha : Real) : NNReal) : ENNReal) := by
  exact HolderWith.eHolderNorm_le
    (holderWith_restrict_comp_of_lipschitzWith phi f hphi hst
      (holderWith_restrict_of_eHolderSeminormOn_le hf))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_le_of_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_le_of_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_le_of_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_le_of_lipschitzWith

def parabolicMap (phi : X → Y) : ParabolicPoint X → ParabolicPoint Y :=
  fun p ↦ parabolicPoint p.time (phi p.space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicMap ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicMap

def parabolicToProduct (p : ParabolicPoint X) : Real × X :=
  (p.time, p.space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicToProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicToProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicToProduct ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicToProduct

def parabolicTimeSlabLipschitzConst (a b : Real) : NNReal :=
  ⟨max 1 (Real.sqrt (b - a)), by positivity⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicTimeSlabLipschitzConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicTimeSlabLipschitzConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicTimeSlabLipschitzConst ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicTimeSlabLipschitzConst

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicToProduct_apply (t : Real) (x : X) :
    parabolicToProduct (parabolicPoint t x) = (t, x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicToProduct_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicToProduct_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicToProduct_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicToProduct_apply

theorem one_le_parabolicTimeSlabLipschitzConst (a b : Real) :
    1 ≤ parabolicTimeSlabLipschitzConst a b := by
  change (1 : Real) ≤ _root_.Max.max 1 (Real.sqrt (b - a))
  exact le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.one_le_parabolicTimeSlabLipschitzConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.one_le_parabolicTimeSlabLipschitzConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.one_le_parabolicTimeSlabLipschitzConst ``Submission.DifferentialGeometry.Analysis.Schauder.one_le_parabolicTimeSlabLipschitzConst

theorem sqrt_sub_le_parabolicTimeSlabLipschitzConst (a b : Real) :
    Real.sqrt (b - a) ≤ parabolicTimeSlabLipschitzConst a b := by
  change Real.sqrt (b - a) ≤ _root_.Max.max 1 (Real.sqrt (b - a))
  exact le_max_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.sqrt_sub_le_parabolicTimeSlabLipschitzConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.sqrt_sub_le_parabolicTimeSlabLipschitzConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.sqrt_sub_le_parabolicTimeSlabLipschitzConst ``Submission.DifferentialGeometry.Analysis.Schauder.sqrt_sub_le_parabolicTimeSlabLipschitzConst

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_apply (phi : X → Y) (t : Real) (x : X) :
    parabolicMap phi (parabolicPoint t x) = parabolicPoint t (phi x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicMap_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicMap_apply

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_time (phi : X → Y) (p : ParabolicPoint X) :
    (parabolicMap phi p).time = p.time := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicMap_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicMap_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicMap_time ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicMap_time

omit [MetricSpace X] [MetricSpace Y] in
@[simp]
theorem parabolicMap_space (phi : X → Y) (p : ParabolicPoint X) :
    (parabolicMap phi p).space = phi p.space := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicMap_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicMap_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicMap_space ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicMap_space

omit [MetricSpace X] [MetricSpace Y] in
theorem parabolicMap_preimage_cylinder
    (phi : X → Y) (J : Set Real) (Omega : Set Y) :
    parabolicMap phi ⁻¹' parabolicCylinder J Omega =
      parabolicCylinder J (phi ⁻¹' Omega) := by
  ext p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicMap_preimage_cylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicMap_preimage_cylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicMap_preimage_cylinder ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicMap_preimage_cylinder

theorem lipschitzWith_parabolicMap
    {L : NNReal} (hL : 1 ≤ L) {phi : X → Y}
    (hphi : LipschitzWith L phi) :
    LipschitzWith L (parabolicMap phi) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
    parabolicMap_apply, parabolicMap_apply, dist_parabolicPoint,
    dist_parabolicPoint]
  apply max_le
  · calc
      |p.time - q.time| ^ (1 / 2 : Real) ≤
          max (|p.time - q.time| ^ (1 / 2 : Real)) (_root_.Dist.dist p.space q.space) :=
        le_max_left _ _
      _ = 1 * _root_.Max.max (|p.time - q.time| ^ (1 / 2 : Real))
          (_root_.Dist.dist p.space q.space) := by rw [one_mul]
      _ ≤ L * _root_.Max.max (|p.time - q.time| ^ (1 / 2 : Real))
          (_root_.Dist.dist p.space q.space) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL)
          ((Real.rpow_nonneg (abs_nonneg _) _).trans
            (le_max_left _ _))
  · exact (hphi.dist_le_mul p.space q.space).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) L.coe_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.lipschitzWith_parabolicMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.lipschitzWith_parabolicMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.lipschitzWith_parabolicMap ``Submission.DifferentialGeometry.Analysis.Schauder.lipschitzWith_parabolicMap

theorem lipschitzOnWith_parabolicMap
    {L : NNReal} (hL : 1 ≤ L) {phi : X → Y} {s : Set X}
    (hphi : LipschitzOnWith L phi s) (J : Set Real) :
    LipschitzOnWith L (parabolicMap phi) (parabolicCylinder J s) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
    parabolicMap_apply, parabolicMap_apply, dist_parabolicPoint,
    dist_parabolicPoint]
  apply max_le
  · calc
      |p.time - q.time| ^ (1 / 2 : Real) ≤
          max (|p.time - q.time| ^ (1 / 2 : Real)) (_root_.Dist.dist p.space q.space) :=
        le_max_left _ _
      _ = 1 * _root_.Max.max (|p.time - q.time| ^ (1 / 2 : Real))
          (_root_.Dist.dist p.space q.space) := by rw [one_mul]
      _ ≤ L * _root_.Max.max (|p.time - q.time| ^ (1 / 2 : Real))
          (_root_.Dist.dist p.space q.space) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL)
          ((Real.rpow_nonneg (abs_nonneg _) _).trans
            (le_max_left _ _))
  · exact (hphi.dist_le_mul p.space hp.2 q.space hq.2).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) L.coe_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicMap ``Submission.DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicMap

theorem lipschitzOnWith_parabolicToProduct_Icc
    (a b : Real) (Omega : Set X) :
    LipschitzOnWith (parabolicTimeSlabLipschitzConst a b)
      parabolicToProduct (parabolicCylinder (Set.Icc a b) Omega) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  change _root_.Dist.dist (p.time, p.space) (q.time, q.space) ≤
    (parabolicTimeSlabLipschitzConst a b : Real) * _root_.Dist.dist p q
  rw [Prod.dist_eq, Real.dist_eq, ← parabolicPoint_time_space p,
    ← parabolicPoint_time_space q, dist_parabolicPoint]
  let z := Real.sqrt |p.time - q.time|
  have htime : |p.time - q.time| ≤ b - a := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2],
      by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]⟩
  have hz_nonneg : 0 ≤ z := Real.sqrt_nonneg _
  have hz_le : z ≤ parabolicTimeSlabLipschitzConst a b := by
    exact (Real.sqrt_le_sqrt htime).trans
      (sqrt_sub_le_parabolicTimeSlabLipschitzConst a b)
  have hz_sq : z ^ 2 = |p.time - q.time| := by
    exact Real.sq_sqrt (abs_nonneg _)
  have hz_rpow : z = |p.time - q.time| ^ (1 / 2 : Real) := by
    exact Real.sqrt_eq_rpow _
  rw [← hz_rpow]
  apply max_le
  · calc
      |p.time - q.time| = z * z := by rw [← pow_two, hz_sq]
      _ ≤ (parabolicTimeSlabLipschitzConst a b : Real) * z :=
        mul_le_mul_of_nonneg_right hz_le hz_nonneg
      _ ≤ (parabolicTimeSlabLipschitzConst a b : Real) *
          max z (_root_.Dist.dist p.space q.space) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _)
          (parabolicTimeSlabLipschitzConst a b).coe_nonneg
  · calc
      dist p.space q.space ≤ _root_.Max.max z (_root_.Dist.dist p.space q.space) := le_max_right _ _
      _ = 1 * _root_.Max.max z (_root_.Dist.dist p.space q.space) := by rw [one_mul]
      _ ≤ (parabolicTimeSlabLipschitzConst a b : Real) *
          max z (_root_.Dist.dist p.space q.space) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast one_le_parabolicTimeSlabLipschitzConst a b)
          (hz_nonneg.trans (le_max_left _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicToProduct_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicToProduct_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicToProduct_Icc ``Submission.DifferentialGeometry.Analysis.Schauder.lipschitzOnWith_parabolicToProduct_Icc

theorem holderWith_restrict_comp_parabolicMap
    {Q : Set (ParabolicPoint X)} {R : Set (ParabolicPoint Y)}
    {L K alpha : NNReal} (hL : 1 ≤ L)
    (phi : X → Y) (f : ParabolicPoint Y → F)
    (hphi : LipschitzWith L phi) (hQR : _root_.Set.MapsTo (parabolicMap phi) Q R)
    (hf : HolderWith K alpha (R.domRestrict f)) :
    HolderWith (K * L ^ (alpha : Real)) alpha
      (Q.domRestrict (f ∘ parabolicMap phi)) := by
  exact holderWith_restrict_comp_of_lipschitzWith
    (parabolicMap phi) f (lipschitzWith_parabolicMap hL hphi) hQR hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_parabolicMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_parabolicMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_parabolicMap ``Submission.DifferentialGeometry.Analysis.Schauder.holderWith_restrict_comp_parabolicMap

theorem eHolderSeminormOn_comp_parabolicMap_le
    {Q : Set (ParabolicPoint X)} {R : Set (ParabolicPoint Y)}
    {L K alpha : NNReal} (hL : 1 ≤ L)
    (phi : X → Y) (f : ParabolicPoint Y → F)
    (hphi : LipschitzWith L phi) (hQR : _root_.Set.MapsTo (parabolicMap phi) Q R)
    (hf : eHolderSeminormOn alpha R f ≤ K) :
    eHolderSeminormOn alpha Q (f ∘ parabolicMap phi) ≤
      ((K * L ^ (alpha : Real) : NNReal) : ENNReal) := by
  exact eHolderSeminormOn_comp_le_of_lipschitzWith
    (parabolicMap phi) f (lipschitzWith_parabolicMap hL hphi) hQR hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_parabolicMap_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_parabolicMap_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_parabolicMap_le ``Submission.DifferentialGeometry.Analysis.Schauder.eHolderSeminormOn_comp_parabolicMap_le

end DifferentialGeometry.Analysis.Schauder

end
