import YM.QCD.Fog.Sun

/-! # silent after Signed orbits using vanishing deposit. Thus double lift from applied score. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free Placement
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {I:Type}{r A:ℝ}
def depositG (A:I→Rg su):ℝ:=∑' i,sharesG (A i)
lemma property_le (P:Rg su):|propertyG P|≤(Fintype.card PlaqAxes:ℝ)*P.magnitude:=by
  apply le_trans (Finset.abs_sum_le_sum_abs ..); apply le_trans (sum_le_sum (s:=univ) fun i _=> show |charge P (fun _=>i) (fun _=>lodging)|≤P.magnitude from ?_); rw [sum_const,nsmul_eq_mul,card_univ]
  unfold charge; split; exact coeff_le ..; simp [Atom.magnitude,sum_nonneg]
lemma heiress (P:Rg su)(hr:0<r): |sharesG P|≤P.budget r:=by
  rw [sharesG,abs_div,abs_of_nonneg ((show 0 ≤ (Fintype.card PlaqAxes:ℝ) from by positivity))]
  exact ((div_le_iff₀ (by positivity :0<(Fintype.card PlaqAxes:ℝ))).2 ((property_le P).trans (le_of_eq (mul_comm ..)))).trans (P.lower_budget _ hr)
lemma deposit_bound (U:I→Rg su)(h:Charged U r A)(hr:0<r):|depositG U| ≤ A:=by
  have H : SumBudget (fun i=> |sharesG (U i)|) A := Cost.mono h (fun i=>abs_nonneg (sharesG (U i))) fun i=> heiress (U i) hr; exact (norm_tsum_le_tsum_norm (f:=fun i=> sharesG (U i)) H.2.1).trans H.2.2
lemma sharesSum (U:I→Rg su)(h:Charged U r A)(hr:0<r): Summable (fun i => sharesG (U i)):=Summable.of_norm_bounded h.2.1 (fun i=> heiress (U i) hr)
def firmG (i:View)(x:Cink):ℝ:= if i 0=i 1 then inkMark x else 0
lemma saleEach (P:Rg su)(h:P.Invariant)(p:View)(x:Cink): ∑ i:Signed,charge (planish P i) p x= sharesG P*firmG p x:=by
  unfold firmG; split <;> rename_i he
  · rw [show p=(fun _=>p 0) from funext fun i=>by fin_cases i <;> first | rfl | exact he.symm, same_side P h,mul_comm]
  obtain ⟨a,ha⟩:=unequal_flux p he; have h:= label_sum P p x (Signed.mirror a); simp_rw [ha,mirror_axes] at h; linarith
lemma deposit_lemma (U:I→Rg su)(h:Charged U r A)(hr:0<r)(hp:SymmetricAtoms U)(p:View)(x:Cink): HasSum (fun i=>charge (whiff U i) p x) (depositG U*firmG p x):= by
  have hs:= (moments_summable hr (whiff_budget h hr.le) p x).1
  let F i:=charge (whiff U i) p x; have hv: HasSum F (∑' i,F i):= hs.hasSum; let E:=Equiv.prodComm I Signed
  have hT : Summable (fun i=>F (E i)) := (E.summable_iff (f:=F)).mpr hs
  rw [show depositG U*firmG p x=∑' i,F i from ?_]; exact hv
  rw [← E.tsum_eq F,hT.tsum_prod,depositG, ← tsum_mul_right]; refine tsum_congr fun i=>?_ ; rw [tsum_fintype]; exact (saleEach (U i) (hp i) p x).symm
lemma seale (s:Signed)(P:Rg su)(p:View)(x:Cink)(d:Axis):
    charge (planish P s) p x*(delta (planish P s) d) + charge (planish P (reverseG*s)) p x* (delta (planish P (reverseG*s)) d:ℝ) = charge (planish P s) p x*((debitG (p 0)-debitG (p 1)) d):=by
  have hh:=charge_trans P reverseG s p x; simp_rw [reversed,prod_const_one,one_mul,reverse_axes] at hh
  rw [hh]; simp_rw [plan_charge]; split
  next he=> rw [show p 0=viewG P s 0 from (congr_fun he _).symm,show p 1=viewG P s 1 from (congr_fun he _).symm,← mul_add, ← Int.cast_add]
            congr 2
            simp only [delta, planish,relocate,slot_offset,planG,viewG,offsetX,Pi.sub_apply,Pi.neg_apply]; ring -- inspect
  rw [zero_mul,zero_mul,zero_mul,add_zero]
lemma digestG (U:I→Rg su)(h:Charged U r A)(hr:0<r)(hp:SymmetricAtoms U)(he:depositG U=0): Silent (whiff U):=by
  intro p x
  have hh:=deposit_lemma U h hr hp p x; rw [he,zero_mul] at hh
  refine ⟨hh,fun d=>?_⟩
  let f (i:Signed×I):=charge (whiff U i) p x* ↑(delta (whiff U i) d)
  have hs:Summable f:=(moments_summable hr (whiff_budget h hr.le) p x).2 d
  let E:= Equiv.prodCongr (Equiv.mulLeft reverseG) (Equiv.refl I)
  let X:=∑' i,f i
  have hh': HasSum (fun i=> f i+f (E i)) 0:=by
    have he i : f i+f (E i)=charge (whiff U i) p x* ↑((debitG (p 0)-debitG (p 1)) d) :=seale i.1 (U i.2) p x d
    simp_rw [he]; have hu:= hh.mul_right (↑((debitG (p 0)-debitG (p 1)) d):ℝ); rw [zero_mul] at hu; exact hu
  have hp:=hh'.unique (hs.hasSum.add ((E.hasSum_iff (f:=f)).2 hs.hasSum)); change (0:ℝ)=X+X at hp; convert hs.hasSum using 1; linarith only [hp]
end YM.QCD.Fog
