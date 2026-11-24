import YM.QCD.Fog.Lens

/-! # mass-channel projector. Silent through the first cochain derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid YM.Next.Free
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {I:Type}{G:Gauge}{r A:ℝ}
abbrev Cink:= Fin 2→su.ColorIndex
def lodging : su.ColorIndex:= letI:= Sparks.c_inh; Classical.arbitrary _
def coeff0 (A:Rg su):= A.coeff fun _=>lodging
def inkMark (i:Cink) :ℝ:= if i 0=i 1 then 1 else 0
lemma trait_eq (x:Cink): (fun i=>x i)=![x 0,x 1]:=funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
lemma ore (V:Rg su)(a b : su.ColorIndex): V.poly ![EuclideanSpace.single a 1,EuclideanSpace.single b 1]=V.coeff ![a,b]:=by
  unfold Atom.poly; rw [sum_eq_single ![a,b]]; · simp [Fin.prod_univ_two]
  · intro i h he; by_cases hx : i 0=a ∧ i 1=b; · apply False.elim (he (by nth_rw 1 [← show (fun j=>i j)=i from rfl]; rw [trait_eq i,hx.1,hx.2]))
    by_cases hz:i 0=a
    · have hh:i 1≠b:=fun e=>hx ⟨hz,e⟩; simp [Fin.prod_univ_two,hz,hh]
    simp [hz,Fin.prod_univ_two]
  simp
lemma furnace (P:Rg su): ∃ L: su.Color→ₗ[ℝ] su.Color→ₗ[ℝ] ℝ,∀ a b,L a b=P.poly ![a,b]:=by
  let T (x:su.Color) : su.Color→ₗ[ℝ] ℝ:= {
    toFun a:= P.poly ![x,a]
    map_add':=fun v w=>by simp [Atom.poly,Fin.prod_univ_two, Finset.sum_add_distrib,mul_add]
    map_smul':=by intro i v; simp [Atom.poly,Fin.prod_univ_two, Finset.mul_sum]; apply sum_congr rfl; intros; ring }
  let L: su.Color→ₗ[ℝ] su.Color→ₗ[ℝ] ℝ:= {
    toFun:= T,map_add':=fun v w=>LinearMap.ext (fun i=>by simp [T,Atom.poly,Fin.prod_univ_two, Finset.sum_add_distrib,mul_add,add_mul]),map_smul':= fun i a=>LinearMap.ext (fun v=>by simp [T,Atom.poly,Fin.prod_univ_two, Finset.mul_sum]; apply sum_congr rfl; intros; ring) }
  exact ⟨L,fun _ _=>rfl⟩
lemma metallurgy (P:Rg su)(h:P.Invariant)(v:Cink): P.coeff v=coeff0 P * inkMark v:=by
  obtain ⟨L,H⟩:= furnace P
  obtain ⟨r,hr⟩:= Push.Loops.scalar_form simple L (fun i x y=>by rw [H,H,show ![su.adjoint i x,su.adjoint i y]=(fun j=>su.adjoint i (![x,y] j)) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩),h])
  have hv (a b:su.ColorIndex): P.coeff ![a,b]= r * if a=b then 1 else 0:=by
    rw [← ore, ← H,hr]; congr 1; rw [Work.F03.inner_color]; by_cases h:a=b <;> simp [h,Ne.symm,eq_comm (a:=a)]
  unfold coeff0 inkMark; rw [show (fun (_:Fin 2)=>lodging)=![lodging,lodging] from trait_eq _,hv lodging,if_pos rfl,mul_one]; calc
    P.coeff v=P.coeff ![v 0,v 1]:=by rw [← trait_eq]
    _=_:= hv ..
lemma plan_charge (P:Rg su)(s : Signed)(x : View)(v:Cink):charge (planish P s) x v=if viewG P s=x then toll * marginG P s * P.coeff v else 0:=rfl
-- rotated charge to rotated request
lemma charge_trans (P:Rg su)(s r:Signed)(x:View)(k:Cink): charge (planish P (s*r)) (fun i=>(x i).rotate s) k=(∏ i,turned s (x i))*charge (planish P r) x k:=by
  have he:viewG P (s*r)=(fun i=>(x i).rotate s) ↔ viewG P r=x:=by
    simp_rw [funext_iff,viewG,← card_side]; exact forall_congr' fun i=> (PlaqAxes.transform s).injective.eq_iff
  simp only [plan_charge,he]; split; swap; next hx=> rw [mul_zero]
  rename_i hg
  have hx:∏ i,turned s (x i)=∏ i,turned s (PlaqAxes.rotate r (P.leg i).plaq):=by rw [← hg]; rfl
  unfold marginG; simp_rw [face_fee,prod_mul_distrib,hx]; ring
lemma label_sum (P:Rg su)(x:View)(b:Cink)(s:Signed): ∑ i:Signed,charge (planish P i) (fun j=> (x j).rotate s) b=(∏ i,turned s (x i))*∑ i:Signed,charge (planish P i) x b :=by
  rw [← Equiv.sum_comp (Equiv.mulLeft s)]; change ∑ i,charge (planish P (s*i)) _ _=_; simp_rw [charge_trans,mul_sum]
lemma unequal_flux (i:View)(h:i 0≠i 1):∃ b:Axis,∏ j,turned (Signed.mirror b) (i j)=-1:=by
  have he:(plaquette (i 0)).val≠ (plaquette (i 1)).val:=fun H=>h ((plaqEquiv).injective (Subtype.ext H))
  by_contra! hv; apply he; ext b; have hx:=hv b; simp_rw [mirror_stamp,Fin.prod_univ_two] at hx; split_ifs at hx <;> simp_all
-- mass sum raw directly then equate rotated Fourier at zero
def propertyG (P:Rg su):ℝ:=∑ p:PlaqAxes, charge P (fun _=>p) (fun _=>lodging)
def sharesG (P:Rg su):ℝ:=propertyG P/(Fintype.card PlaqAxes:ℝ)
lemma same_side (P:Rg su)(h:P.Invariant) (x:PlaqAxes)(v:Cink): ∑ i:Signed,charge (planish P i) (fun _=>x) v= inkMark v *sharesG P :=by
  let Q (p:PlaqAxes):= fun s:Signed=>charge (planish P s) (fun _=>p) (fun _=>lodging)
  have hp (p:PlaqAxes): ∑ i,Q p i=∑ i,Q x i:=by obtain ⟨k,h⟩:=spots x p; rw [← h,label_sum P (fun _=>x) (fun _=>lodging) k]; simp only [Fin.prod_univ_two,turned_sq,one_mul]; rfl
  have hv (i: Signed):∑ p,Q p i=toll*propertyG P:=by
    rw [← Equiv.sum_comp (PlaqAxes.transform i)]; unfold Q propertyG; rw [Finset.mul_sum]; refine sum_congr rfl fun p _=>?_
    have hh:= charge_trans P i 1 (fun _=>p) (fun _=>lodging); rw [mul_one, Fin.prod_univ_two, turned_sq,one_mul] at hh
    change charge (planish P i) (fun _=> PlaqAxes.rotate i p) _= _
    have hs : marginG P (1:Signed)=1:=by unfold marginG; simp [turned,fun i=>(P.leg i).plaq.property]
    have he : viewG P 1=(fun i=> (P.leg i).plaq):=funext fun i=>mirror_axes 0 (P.leg i).plaq
    rw [hh,plan_charge,hs,he]; unfold charge; split <;> ring
  have hq : ∑ i,Q x i=sharesG P:=by
    have ht:= sum_comm (s:=univ) (t:=univ) (f:=fun i s=>Q i s); simp_rw [hv,hp,sum_const,card_univ,nsmul_eq_mul] at ht -- hp simp infinite
    rw [toll, ← mul_assoc, mul_inv_cancel₀ (by positivity),one_mul,mul_comm] at ht; exact (eq_div_iff (by positivity)).2 ht
  rw [← hq,mul_sum]; apply sum_congr rfl; intro i _; unfold Q; rw [plan_charge,plan_charge]; split; next hP=> rw [metallurgy P h]; unfold coeff0; ring
  rw [mul_zero]
end YM.QCD.Fog
