import YM.QCD.Tide.Seam
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Slice Slice.Link YM.Analysis
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology ComplexOrder
variable {n c f : Side} {F : ℕ} {C : Lat.Cut n F} {R : Cells.Cut n} {S P : Set (Site n)}
local notation "a"=> R.pos
local notation "Ω"=> Slice.Open R su
lemma clearsK (h : R.kind=.link) (hL : 2 ≤ R.half.val) (d : Rest R su) (f : Lat.Grid n → ℂ)
    (hi : GaugeInvariant f) :
    (∫ x : Free R, f (full R (d,x)) ∂freeM R) = ∫ x : Free R, f (full R (1,x)) ∂freeM R := by
  obtain ⟨k,hk⟩ := new_frame h hL d
  let U : Lat.Grid n := fun e => k e.1
  let V : Lat.Grid n := fun e => (k (e.1 + step e.2))⁻¹
  let L := (full R).symm U
  let S := (full R).symm V
  have ha (x : Free R) : Lattice.gauge k (full R (d,x)) = full R (L*(d,x)*S) := by rw [map_mul,map_mul]; simp only [L,S,MulEquiv.apply_symm_apply]; rfl
  have H : L.1*d*S.1=1 := by
    haveI := walls_link h
    apply Prod.ext
    · exact Subsingleton.elim ..
    funext i y
    let v : Free R := 1
    have ht := hk v i y
    rw [← full_at,ha,full_at,chain_time,checkpoint] at ht
    exact ht
  have hy (x : Free R) : f (full R (d,x)) = f (full R (1,L.2*x*S.2)) := by
    rw [← hi k (full R (d,x)),ha, show L*(d,x)*S=(L.1*d*S.1, L.2*x*S.2) from rfl,H] -- check hi order
  let g : Free R→ℂ := fun x => f (full R (1,x))
  simp_rw [hy]
  haveI : Measure.IsMulRightInvariant (freeM R) := by
    constructor
    intro u
    haveI : IsProbabilityMeasure ((freeM R).map (· * u)) := Measure.isProbabilityMeasure_map (measurable_mul_const u).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  exact (integral_mul_left_eq_self (μ:=freeM R) (fun x => g (x*S.2)) L.2).trans (integral_mul_right_eq_self g S.2)

lemma clearedR (h : R.kind=.link) (hL : 2≤ R.half.val) (f : Lat.Grid n → ℂ)
    (hf : Stays f) (hi : GaugeInvariant f) :
    (∫ x, f x ∂prior su n) = ∫ x : Free R, f (clear R x.1 x.2) ∂freeM R := by
  let u := fun x : Free R => (x.1,replace R x.2)
  let j := fun x : Free R => f (full R (1,x))
  have hm : MeasurePreserving u (freeM R) (freeM R) := (MeasurePreserving.id _).prod (twisted R)
  have hx : MeasurePreserving (full R) ((restM su R).prod (freeM R)) (prior su n) := (chain_volume _).comp (wiredVolume R)
  have hw := integral_map hx.aemeasurable (f:=f) (by rw [hx.map_eq]; exact hf.mes.aestronglyMeasurable)
  rw [hx.map_eq] at hw; rw [hw, integral_prod _ (show Integrable (fun x => f (full R x)) _ from hx.integrable_comp_of_integrable
    (hf.intg _))]
  change (∫ x, (∫ y : Free R, f (full R (x,y)) ∂freeM R) ∂restM su R) = ∫ x, j (u x) ∂freeM R
  simp_rw [clearsK h hL _ f hi]; rw [integral_const]; simp only [Measure.real, measure_univ,ENNReal.toReal_one,one_smul]
  have hj : Measurable j := hf.mes.comp (hx.measurable.comp (measurable_const.prodMk measurable_id))
  have He := integral_map hm.aemeasurable (f:=j) (by rw [hm.map_eq]; exact hj.aestronglyMeasurable)
  rw [hm.map_eq] at He; exact He
noncomputable def measureK (C:Lat.Cut n F)(x:Stud n F)(U:Grid n):ℂ:= (bare C.β U :ℂ)*ber _ (C.insertD U*x U)
lemma sure (x:Stud n F)(h:Stays x):Stays (measureK C x):= ((stays (show Continuous fun U:Grid n=> (bare C.β U:ℂ) by fun_prop))).mult (((stays C.insertD.continuous).mult h).flows ((ber _).continuous_of_finiteDimensional))
lemma sureN (x:Stud n F)(h:Neutral x):GaugeInvariant (measureK C x):=by
    intro k U; unfold measureK; rw [bare_gauge,← no_jac F k (C.insertD (gauge k U)*_),map_mul,invariant_weight,h]
lemma Nprod (x y:Stud n F)(h:Neutral x)(hh:Neutral y):Neutral (x*y):= by intro k U; simp [h,hh]
private lemma panelsP (h : R.kind=.link) (T : Matches C R) (hb : 0≤ C.β) (x : Stud n F) (H : Uses R.sector x) : NNKernel
    (fun X Y : Ω => measureK C (foldsT R x*x) (RP.clear R X Y)) := by
  let q (X:Ω):= chain R.pos (reader R 1 X)
  have hv(X:Ω):∃ v:Dirac (Lamp R F),x (q X)=pass (light R) v:= H.2 (q X)
  choose g hg using hv; let S := fun X : Ω=> exp (fence C h X)
  have h₁ (X) : Grass.Hom false (exp (fence C h X)) := by
    change grade (exp _)=exp _; rw [map_weight,(show grade (fence C h X)=_ from fence_even ..)]
  have he (X Y : Ω) : (foldsT R x*x) (RP.clear R X Y)=RP.hit R (g Y) (g X) := by
    unfold RP.clear; rw [Pi.mul_apply, foldsT,H.1 _ _ (first_eye R _),H.1 _ _ (second_eye R _)]; change theta _ (x (q Y))*x (q X)=_; rw [hg,hg]; rfl
  unfold measureK
  have hu (X Y : Ω) : RP.hit R (exp (fence C h Y)) (exp (fence C h X)) * RP.hit R (g Y) (g X) = RP.hit R (S Y*g Y) (S X*g X) := shuffle _ _ _ _ (h₁ _) (h₁ _)
  simp_rw [he,dress h T,mul_assoc,hu]; exact (gauge_rays h hb).times (all_rays h (joint_even F h).2 (fun X => S X*g X))
lemma sealed (h:R.kind=.link)(hL:2 ≤ R.half.val) (T: Matches C R)(hb: 0 ≤ C.β)(x:Stud n F)(H:Uses R.sector x)(hx:Stays x)(hp:Neutral x):0 ≤ ∫ U, measureK C (foldsT R x*x) U ∂prior su n:=by
    have he:= sure (C:=C) (foldsT R x*x) ((foldsPay x hx).mult hx)
    rw [clearedR h hL _ he (sureN _ (Nprod _ _ (floods x hp) hp))]
    let f:= fun p : Ω × Ω=> RP.clear R p.1 p.2
    have hv: Measurable f := clear_cont.measurable
    let g (X Y:Ω):= measureK C (foldsT R x*x) (RP.clear R X Y)
    have hp1:Integrable (fun i:Ω×Ω=>g i.1 i.2) ((fieldM su R).prod (fieldM su R)):= (he.travel hv).intg _
    have hp2:Measurable (fun X:Ω=> (X,X)):= measurable_id.prodMk measurable_id
    have hp3:Integrable (fun X:Ω=> g X X) (fieldM su R):=((he.travel hv).travel hp2).intg _
    exact flock (K:=g) hp1 hp3 (panelsP h T hb x H)
-- adapted cuts
noncomputable def crown (R:Cells.Cut n)(C:Lat.Cut n F)(x:Stud n F) : Stud n F:= let s:= mount R C; coat s (foldsT R (coat s x))
lemma crowned (h:R.kind=.link)(hL:2 ≤ R.half.val) (hb: 0 ≤ C.β)(x:Stud n F)(H:Uses R.sector x)(hx:Stays x)(hp:Neutral x): 0 ≤ ∫ U, measureK C (crown R C x*x) U ∂prior su n:=by
    let s:= mount R C; have hv:= sealed h hL (tuned R C) (show 0≤ (s.swap C).β from hb) (coat s x) (coatS s x H) (coating s x hx) (coated s x hp)
    refine hv.trans_eq ?_; apply integral_congr_ae; refine ae_of_all _ (fun U=>?_); let Y:= foldsT R (coat s x)
    change (bare C.β U:ℂ)*ber _ ((s.swap C).insertD U*(Y U* s.tape F (x U))) = (bare C.β U:ℂ)*ber _ (C.insertD U*(s.tape F (Y U)*x U)); rw [← s.tape_amp (C.insertD U * _), s.flexes _ rfl]; simp [s.rolled]
end YM.QCD.Tide
