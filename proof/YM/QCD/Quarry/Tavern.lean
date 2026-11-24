import YM.Next.STATIONARY.Joint.Symmetry
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
import YM.QCD.Quarry.Mask

/-! # Leading rooted prescriptions germs carried to any chart by tree shell -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Quarry.Tavern
open Function Filter Lattice Wilson Stationary Precision Gauge RG Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f}
-- local names with coarser translations angle

def spaceShift (b : Site n) : Link G n→L[ℝ] Link G n:= (arm G n 1).symm.toContinuousLinearMap ∘L YM.AnalyticNext.QuarticMatch.Joint.shifts 1 b ∘L (arm G n 1).toContinuousLinearMap
lemma spaceAt (b : Site n) (x : Link G n) (i) : arm G n 1 (spaceShift b x) i= arm G n 1 x (i.1+b,i.2):=by simp only [spaceShift,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]; exact YM.AnalyticNext.QuarticMatch.Joint.shift_one_apply ..
lemma spaceCon (b : Site n) (x : Link G n): spaceShift (-b) (spaceShift b x)=x:=by apply (arm G n 1).injective; ext1 i; rw [spaceAt,spaceAt]; simp
lemma input_run (b : Site n) (x : Link G n): input G n (spaceShift b x)=pull 1 b (input G n x):=by
  simp only [input,spaceShift,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]; exact YM.AnalyticNext.QuarticMatch.Joint.rep_shifts ..

def roadG (b : Site n) (u : Coats G n) : Coats G n:= u ∘ affine 1 b
def spaceG (b : Site n): BaseSites G n →L[ℝ] BaseSites G n:= gaugeColor.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (φ:=fun _ : Site n=> G.Color) (i+b)) ∘L gaugeColor.toContinuousLinearMap
lemma space_site (b : Site n) (x : BaseSites G n) (i : Site n): gaugeColor (spaceG b x) i=gaugeColor x (i+b):=by simp [spaceG]
lemma space_switch (b : Site n) (x : BaseSites G n): switchSite (spaceG b x)=roadG b (switchSite x):=by funext i; unfold roadG; rw [Function.comp_apply,switch_color,switch_color,space_site]; simp [affine]
lemma spaceGr (b : Site n) (x : BaseSites G n): spaceG (-b) (spaceG b x)=x:=by apply gaugeColor.injective; funext i; rw [space_site,space_site]; simp

variable (S)
def road (b : Site c) (x : Joint G c f): Joint G c f:= (pull 1 (S.ratio.embed b) x.1,roadG b x.2)
def spaceV (b : Site c): Vault G c f→L[ℝ] Vault G c f:= (spaceShift (S.ratio.embed b)).prodMap (spaceG b)
lemma road1 (b : Site c):road (G:=G) S b 1=1:=by refine Prod.ext ?_ rfl; change pull 1 (S.ratio.embed b) (1:Config G f)=1; rw [pull_one]; rfl
lemma road_diff {X: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {x:X} {U : X → Joint G c f} (b:Site c) (h : Thaw U x): Thaw (road S b ∘ U) x:=by
  refine ⟨fun i=>?_,fun _=> h.2 _⟩; simp_rw [Function.comp_apply,road,pull_one]; exact h.1 _
lemma spaceV_inv (b:Site c) (x : Vault G c f): spaceV S b (spaceV S (-b) x)=x:=by
  have he : S.ratio.embed (-b)= -S.ratio.embed b:=map_neg S.ratio.root b
  refine Prod.ext ?_ ?_
  · change spaceShift (S.ratio.embed b) (spaceShift (S.ratio.embed (-b)) x.1)=x.1; rw [he]; simpa only [neg_neg] using spaceCon (-S.ratio.embed b) x.1
  change spaceG b (spaceG (-b) x.2)=_; simpa only [neg_neg] using spaceGr (-b) x.2
lemma onward (b : Site c) (U : Joint G c f) (x:Vault G c f): road S b (Stationary.extend x * U)= Stationary.extend (spaceV S b x)*road S b U:=by
  refine Prod.ext ?_ ?_
  · change pull 1 _ (_*U.1)=input _ _ (spaceShift _ _)*_
    rw [input_run]; unfold road; dsimp only; simp_rw [pull_one]; rfl -- try
  change roadG b (switchSite x.2 * _)=switchSite (spaceG b x.2)*_
  rw [space_switch]; rfl
lemma loyalty (b:Site c)(U: Joint G c f) (V:Config G c) (t : S.Choices) (p : Clip) (R : PathData G) (hs:S.patch.Branches S.kernel G):
    muster S t p R (pull 1 b V) (road S b U)=muster S (S.withinChoice 1 b t) p R V U:= by
  exact YM.AnalyticNext.QuarticMatch.Joint.field_channel p R hs V U.1 U.2 1 b t
lemma updated (b : Site c) (U : Joint G c f) (V:Config G c) (t : S.Choices) (p:Clip)(R : PathData G)
    (hs:S.patch.Branches S.kernel G) (ht: Shell S (S.withinChoice 1 b t) p R V U):
    Shell S t p R (pull 1 b V) (road S b U):=by
  let L:= spaceV (G:=G) S (-b); let Q:= canon S (S.withinChoice 1 b t) p R V U
  have he: canon S t p R (pull 1 b V) (road S b U)= Q ∘ ⇑L := by
    funext x; rw [canon]; nth_rw 1 [← spaceV_inv S b x]; rw [← onward,loyalty _ _ _ _ _ _ _ hs]; rfl
  rw [Shell,he]
  have HH : ContDiffAt ℝ ω Q (L 0):= by rw [map_zero]; exact ht.1
  refine ⟨HH.comp (f:=L) _ L.contDiff.contDiffAt,?_⟩
  rw [fderiv_comp 0 (HH.differentiableAt (by simp)) L.differentiableAt,map_zero, show fderiv ℝ Q 0=0 from ht.2, ContinuousLinearMap.zero_comp]
end YM.QCD.Quarry.Tavern
