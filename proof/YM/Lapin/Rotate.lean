import YM.Oriole.Tree
import YM.Patria.Scene
import YM.Poised.Reins
/-! rotate Rod estimates to other axes in same lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {c:Side}(Q:Sheet c)(i j:Axis)(s:Equiv.Perm Axis)(B:Spike) -- Taper namespace
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder QCD.Entr.Goals
variable (F:SourceRead.Taper)(h:Globe.Tempo Q)(V:Spike)(ht: Swing (Swing.pure s) V)
open QCD.Flume QCD.Bay
private lemma swing_up (v:Site c) : Lattice.lift ((Swing.pure s).act v)=(Swing.pure s).act (Lattice.lift v):=by
     ext x; obtain ⟨p,rfl⟩:=s.surjective x; unfold Lattice.lift; have h (i:Axis):(Swing.pure s).perm i=s i:=rfl
     simp_rw[← h, Signed.act_at]; simp[Swing.pure]
private lemma occS (x:Cover): ap c x=occ (0:Site c) x:= by simpa only [map_zero, Lining.Ferry.ap_origin, one_mul,zero_add] using (Poised.Steed.rollAP c 0 x).symm
local notation "T"=> Swing.pure s
local notation "W"=>wave V
local notation "O"=> (0:Site c)
include h ht
lemma ritual : Rod c F (s i) Q= W*(Rod c F i Q)*star W:=by
     obtain ⟨l,hl⟩:= shades T 0 0 O
     have hp(w:Cover):Globe.onset Q O ((T).act w)=W*Globe.onset Q O w*star W:=by
            have hv:= h.visit O w (T,O) _ _ (show QCD.Bay.Strut.Warrant (T,O) l V from ⟨hl,ht⟩); rw [show QCD.Bay.Strut.act (T,O) O=O from (by change affine (Swing.pure s) (0:Site c) 0=0; simp[affine])] at hv
            change Globe.onSet Q O ((T).act w)= _ at hv; rw [h.giltV,h.giltV, hv,wave_star,wave_mul,wave_mul]
     let tℓ(x:Cover):ℂ:= F.χ ((c.val:ℝ)⁻¹ • vector x); have hx(j:Axis)(v:Site c): Nw F (first j) v • QCD.Run.cell Q O v= (tℓ (lift v)*(Lattice.lift v j:ℂ)) • Globe.onset Q O (lift v):=by
            unfold Globe.onset; rw [wrap_lift,zero_add,smul_smul, N_one]; congr 1; unfold Np tℓ; rw [occS,mul_right_comm]
     change (∑ v:Site c,_)= _ * (∑ v:Site c,_) * _; rw [← Equiv.sum_comp ((T).actEquiv (R:=Per c)).toEquiv (fun p:Site c=> Nw F (first (s i)) p • QCD.Run.cell Q O p), Matrix.mul_sum,Matrix.sum_mul]
     apply sum_congr rfl; intro p _; change Nw F (first _) ((T).act p) • QCD.Run.cell Q 0 ((T).act p)=_; rw[hx, swing_up, hp, hx, Matrix.mul_smul,Matrix.smul_mul]; let w:= Lattice.lift p; have hu:tℓ ((T).act w)=tℓ w:=by unfold tℓ; rw [← Canvas.motion_site, ← map_smul, Ortho.motion_at, F.even]
     change (tℓ ((T).act w) * (((T).act w (s i):ℤ):ℂ)) • _=_; rw [hu,show (T).act w (s i) = w i from ?_]; change (T).act w ((T).perm i)= _; rw [Signed.act_at,if_neg (by simp [Swing.pure])]
omit ht
local notation "Y"=> wave (gamma i)
local notation "G"=> wave (gamma j)
include h
lemma lit (η:ℝ)(hv:‖Rod c F i Q - Y‖ ≤ η):‖Rod c F j Q-G‖ ≤ η :=by
     let s:= Equiv.swap i j; have ht:s i=j:=Equiv.swap_apply_left ..; obtain ⟨V,hP⟩:= Swing.goes (Swing.pure s); let X:=wave V
     have hx: X*Y*star X=G:=by
           unfold X; rw[wave_star,wave_mul,wave_mul,hP.sends]; simp only [Swing.pure,Bool.false_eq_true,↓reduceIte,mul_assoc,hP.unit.2,mul_one,ht]
     have hQ:‖X‖=1:=primeU _ (W_unit _ hP.unit); rw[← hx,show Rod c F j Q= X*_ * star X from ht ▸ ritual Q i s F h V hP, ←sub_mul,←mul_sub]; refine (norm_mul_le ..).trans ?_; change ‖X * _‖*‖star X‖ ≤ _; rw [norm_star,hQ,mul_one]; exact (norm_mul_le ..).trans (by rw [hQ,one_mul]; exact hv)
lemma paid_j (η:ℝ)(hv:‖Rod c F i Q-Y‖ ≤ η): ‖Rv F i Q+Y‖ ≤ η:=by
     rw [coil Q F h i]; let S:=wave Lat.g5; have he: S* star Y*S= -Y:=by unfold S; rw [wave_star,gamma_star,wave_mul,wave_mul,mul_assoc,Lat.five,mul_neg,← mul_assoc, g5_sq,one_mul,QCD.Revolve.wave_neg]; -- order
     have hp: ‖S‖=1:= primeU S (W_unit Lat.g5 ⟨by simp,by simp⟩); change ‖S * _ * S + Y‖ ≤ _; rw[show S *_ *S+ Y=S*star (Rod c F i Q - Y)*S from (by rw [star_sub,mul_sub,sub_mul,he,sub_neg_eq_add])]; apply (norm_mul_le ..).trans; rw[hp,mul_one]; exact (norm_mul_le ..).trans ((le_of_eq (by rw [hp,norm_star,one_mul])).trans hv)
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.lit
#print axioms YM.Massive.Oriole.paid_j
