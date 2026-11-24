import YM.Kwick.FeeB
/-!
   Row inspection inserted through the real Mire trajectory: a traceless,
   single sided spin rotation. Probe transports the full row, thus can buy
   a relative local derivative even when estimating a true *total* response.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical Kronecker TensorProduct
open Revolve Onsite UV PCAC.Oren Finset Poised Poised.Beacon Poised.Plans Poised.Stative Massive.Patria
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
variable (a:Flavor 6)(u:Site c)(P:BudgetPoint)(p:Spike)
local notation "J"=> gamma 0
noncomputable def veer : Grid c→ Lat.Fields c 6→L[ℂ] Lat.Fields c 6:=mixΛ (fun _=>localF u 0 a a) (fun _=>localF u J a a)
lemma nullSpot: localF u (0:Spike) a a=0:=by unfold localF flavorW; ext i j; rw[zleft]; split<;> simp [Lat.onSpin, Lat.rides, wave_zero]
lemma trace_row : Matrix.trace (localF u J a a)=0:=by
       have he(J':Spike)(b:Site c): Matrix.trace (localF b J' a a)=Matrix.trace (wave J'):=by
            unfold Matrix.trace; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single b]; swap
            · intro i _ h; apply sum_eq_zero; intro _ _; apply sum_eq_zero; intro q _; exact focusL a a b J' _ _ h -- ellipsis binder
            rotate_right; · simp
            apply sum_congr rfl; intro j _; rw [sum_eq_single a]; change localF b _ _ _ _ _=_; rw[localF,zleft]; simp[flavorW,spot,onSpin,rides]
            intro p _ h; change localF _ _ _ _ _ _=0; rw[localF,zleft]; simp [flavorW,spot,onSpin,rides,h]
            simp
       rw [he]; let V:= wave g5; let B:= wave J; have ht: V*B=-(B*V):=by rw [show V*B=_ from wave_mul ..,show B*V=_ from wave_mul ..,show Lat.g5*J= -(J*Lat.g5) from ?_,QCD.Revolve.wave_neg]; rw [Lat.five,neg_neg]
       have hv:V*V=1:=by unfold V; rw[wave_mul,g5_sq,wave_one]
       apply neg_eq_self.mp; change -B.trace=B.trace; rw [←Matrix.trace_neg]; have h: V*(B*V)=-B:=by rw [←mul_assoc,ht,neg_mul,mul_assoc,hv,mul_one]
       rw [← h,Matrix.trace_mul_comm,mul_assoc,hv,mul_one]
local notation "η"=> veinFare 0+ veinFare J
lemma verify : Suit u P (veinFare 0+veinFare J) (veer a u):=populate _ _ (poleBoth ..) (poleBoth ..) (fun x=>by rw[nullSpot,Matrix.trace_zero,trace_row])
lemma version (U:Grid c)(X:Lat.Fields c 6) : veer a u U X= - applyMark true (localF u J a a) X:=by
       change applyMark false _ X-_=_; rw [nullSpot,show applyMark false (0:Sour (Modes c 6)) X=0 from ?_,zero_sub]; simp [column]
local notation "L" p:arg=> localF p J a a
open PCAC.Oren Entr Entr.Meridian Stew Massive.Patria.Depth TorusPCAC.Geometry
lemma smokeH(t: Cover)(X:Lat.Fields c 6)(U:Grid c): let v:=wrap c t; 
      let W:=hues v 1 (heat t) 1; let K:=copies 6 W; Kit.disguise K (veer a u U X)= veer a (u+v) U (Kit.disguise K X):=by
       intro v W K; rw [version, version,map_neg]; congr 1
       let x:=shiftE 1 v u; have hx : x=u+v:=by simp [x,shiftE,Signed.actEquiv]
       suffices H : Kit.disguise K (applyMark true (L u) X)=(1:ℂ) • applyMark true (L x) (Kit.disguise K X) by simpa only [one_smul,hx] using H
       apply Oren.keyζ; exact Lat.copies_unitary 6 W (colour_wheel (TorusPCAC.Geometry.glares t) Revolve.Swing.none); rw [one_smul]; apply w_herd ..; simp -- order
variable (A:Massive.Run S n R 6)(hA:A.Actual)
local notation "M"=> S.side R i
local notation "Ξ"=> actor A i
noncomputable def ms (b:Cover): Insertion (S.side R i) 6 :=⟨fun V=> veer a (wrap _ b) V (Ξ V), ContinuousLinearMap.continuous (_:Lat.Fields _ _ →L[ℂ] Lat.Fields _ _) |>.comp ((Ξ).continuous)⟩ -- simplify
local notation "I"=> ms (i:=i) a A
include hA
lemma m_start (u:Averaging)(hi:i ≤ n): TideT A u i (report A I u):=by
       apply stampF A _ u; intro b d; funext V
       let p:= wrap M d; let G:= hues p 1 (heat d) 1; let K:= Kit.disguise (copies 6 G); change K (veer a (wrap M b) _ (Ξ (pull 1 p V)))=veer a _ V (Ξ V); have hv: march d (⇑Ξ)= ⇑Ξ:=by rw[act A hA hi,pier A hA hi]; exact Patria.Depth.first A i hi d
       let x:=wrap M b; change K (veer a x V (Ξ (pull 1 p V)))=_; rw [show K (veer a x V _)=_ from smokeH a x d (Ξ (pull 1 p V)) V]; rw [map_add,show K (Ξ (pull 1 p V))= Ξ V from congr_fun hv V]
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.m_start
#print axioms YM.Massive.PCAC.verify
