import YM.Gall.Shine
/-! Flat-Cartan tests, protected observations. One and two field probes exact even with support tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole
open Poised Poised.Display Poised.Beacon PCAC Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p w:ℕ}
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable {E Y:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y]
def crown (F:E→Y):E→L[ℝ]E→L[ℝ]Y:= fderiv ℝ (fderiv ℝ F) 0
lemma pairs (F:E→Y)(hF:ContDiffAt ℝ (k:ℕ∞ω) F 0) (hk: 2 ≤ k)(x y:E): crown F x y=crown F y x:= hF.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast) x y
def dawn (F:E→Y):E→Y:= fun y=> F 0+(fderiv ℝ F 0) y +(1/2:ℝ) • (crown F y y)
lemma dawn_c (F:E→Y) : ContDiff ℝ ω (dawn F):=by unfold dawn; fun_prop
lemma dawn_p (F:E→Y)(hF:ContDiffAt ℝ (k:ℕ∞ω) F 0)(hk: 2≤ k)(x:E): fderiv ℝ (dawn F) x=fderiv ℝ F 0+crown F x:=by
    let W:= crown F; let M:= fderiv ℝ F 0; change fderiv ℝ _ x=M + _; let H:= (hasFDerivAt_id (𝕜:=ℝ) x); have hv:= (((hasFDerivAt_const (𝕜:=ℝ) (x:=x) (F 0)).add M.hasFDerivAt).add ((W.hasFDerivAt.clm_apply H).const_smul (1/2:ℝ))).fderiv
    have hg : fderiv ℝ (dawn F) x=M+(1/2:ℝ) • (W x+W.flip x):=by change fderiv ℝ (dawn F) x= _ at hv; simpa only [zero_add,id_eq,ContinuousLinearMap.comp_id] using hv
    rw [show fderiv ℝ _ x=_ from hg]; apply congr_arg; ext y; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.flip_apply]; rw [show W y x= W x y from pairs F hF hk _ _]; change (1/2:ℝ) • (_+_)= W x y; module
lemma sameD (F:E→Y)(hF: ContDiffAt ℝ (k:ℕ∞ω) F 0)(hk:2≤k)(x:ℕ)(hx:x≤2): iteratedFDeriv ℝ x F 0= iteratedFDeriv ℝ x (dawn F) 0:=by
    apply ContinuousMultilinearMap.ext; intro v; interval_cases x
    · simp[dawn]
    · rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,dawn_p F hF hk,map_zero,add_zero]
    rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply,funext (dawn_p F hF hk)]; let W:=crown F; let M:= fderiv ℝ F 0; have he : fderiv ℝ (fun x=> M + W x) 0=W:=by exact (by simpa using! ((hasFDerivAt_const (x:= (0:E)) M).add W.hasFDerivAt).fderiv)
    rw [show fderiv ℝ _ _= _ from he]; rfl
-- curves
noncomputable def river (x y:E)(t:ℝ):E:= t^4 • x+t^6 • y
@[simp] lemma river0 (x y:E): river x y 0=0:=by simp[river]
lemma river_c (x y:E): ContDiff ℝ ω (river x y):=by unfold river; fun_prop
lemma shadowD(F:E→Y)(hF: ContDiffAt ℝ (k:ℕ∞ω) F 0)(hk:2≤k)(x y:E)(hn:n≤k)(h:n<12) : iteratedDeriv n (F∘river x y) 0=iteratedDeriv n (dawn F ∘ river x y) 0:=by
    let V:=river x y; have hV:V 0=0:=river0 ..
    have hu : ContDiffAt ℝ (k:ℕ∞ω) V 0:= (river_c x y).contDiffAt.of_le le_top
    change iteratedDeriv _ (F∘V) 0=iteratedDeriv _ (dawn F∘V) 0; rw[iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ _ F (V 0) from hV.symm ▸ hF) hu (Nat.cast_le.mpr hn),iteratedDeriv_vcomp_eq_sum_orderedFinpartition ((dawn_c F).contDiffAt.of_le le_top) hu (Nat.cast_le.mpr hn),hV]; refine Finset.sum_congr rfl fun p _=>?_ ; by_cases h:p.length ≤2; · rw [sameD F hF hk p.length h]
    obtain ⟨i,hi⟩:= (show ∃ i: Fin p.length, p.partSize i < 4 from by
        by_contra! hm; have hb:p.length*4 ≤ n:=by
            have he:= Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin p.length))) (fun i _=>hm i); have h:(∑ j,p.partSize j)=n:=by simpa using p.sum_sigma_eq_sum (fun _=>(1:ℕ))
            simpa [h] using he
            -- whitespace
        omega)
    let f:= fun i=> iteratedDeriv (p.partSize i) V 0; have H: f i=0:=by unfold f V river; rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_smul_const (by fun_prop),iteratedDeriv_smul_const (by fun_prop),iteratedDeriv_fun_pow_zero,iteratedDeriv_fun_pow_zero,if_neg (by omega),if_neg (by omega)]; simp
    exact ((iteratedFDeriv ℝ p.length F 0).map_coord_zero i H).trans ((iteratedFDeriv ℝ p.length (dawn F) 0).map_coord_zero i H).symm
noncomputable abbrev coin (F:E→Y)(x y:E)(m:ℕ):Y:=
    (if m=0 then F 0 else 0)+((if m=4 then fderiv ℝ F 0 x else 0)+(if m=6 then fderiv ℝ F 0 y else 0))+((if m=8 then (1/2:ℝ) • crown F x x else 0)+(if m=10 then crown F x y else 0))
lemma money (F:E→Y)(hF:ContDiffAt ℝ (k:ℕ∞ω) F 0)(hk:2≤k)(x y:E)(hn:n≤k)(h:n<12) : iteratedDeriv n (F∘river x y) 0= (n.factorial:ℝ) • coin F x y n:=by
    rw [shadowD F hF hk x y hn h]; let L:= fderiv ℝ F 0
    let W:= crown F; have hf : dawn F ∘ river x y= (fun t:ℝ=> (t^0) • F 0 + (t^4 • L x+t^6 • L y) + (t^8 • ((1/2:ℝ) • W x x)+t^10 • W x y+t^12 • ((1/2:ℝ) • W y y))):= by
      funext t; simp only [Function.comp_apply,dawn,river,map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]; change F 0+ (t^4 • L x+t^6 • L y) + _=_; rw [pairs F hF hk y x]; unfold W; module
    rw [hf]; have hm(m:ℕ)(x:Y): iteratedDeriv n (fun t:ℝ=> t^m • x) 0=(n.factorial:ℝ) • (if n=m then x else 0):=by rw [iteratedDeriv_smul_const (by fun_prop),iteratedDeriv_fun_pow_zero]; split <;> simp_all
    rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_fun_add (by fun_prop) (by fun_prop),hm,hm,hm,hm,hm,hm]; rw [if_neg (show ¬ n=12 from Nat.ne_of_lt h),smul_zero,add_zero]; unfold coin; simp only [smul_add]; rfl
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.money
