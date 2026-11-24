import YM.Lapin.Zass
/-!
 Sums of genuine displays. Tally projects every read value using these views.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Run S n R 6)(hA:A.Actual)(hi:i ≤ n)
variable (a b:Flavor 6)(j:Axis)(w:Averaging)
local notation "M"=> S.side R i
local notation "φ"=> A.density i
local notation "Ξ"=> actor A i
local notation "G"=> sprigs (i:=i) A a
local notation "X"=> report A (G j) w
open QCD.Cove QCD.Creek
local notation "L"=> Gall.viaP A
include hA hi
lemma nour : TideT A w i (report A (G j) w):=by
        apply stampF A _ w; intro b t; funext U
        let p:=wrap M t; let V:=pull 1 p U; let K:=Kit.disguise (copies 6 (hues p 1 (heat t) 1)); change K (_*_)= Ξ U * _; have he: K (Ξ V)= Ξ U:=by
            apply congr_fun (g:=⇑Ξ) (f:=march t (⇑Ξ)) _ U; rw[act A hA hi,pier A hA hi]; exact Patria.Depth.first A i hi t
        let v:= wrap M b; rw [map_mul K, he,show K _=_ from shineJ a j v V U p 1 (heat t) 1 (TorusPCAC.Geometry.glares t) Revolve.Swing.none, show shiftE 1 p v=wrap M (b+t) from (by rw [map_add]; simp[p,v,Signed.actEquiv,shiftE]), show signT 1 j=1 from (by simp[signT]),Complex.ofReal_one,one_smul]; rfl
lemma spoke : Roars (sprigs (i:=i) A a):=by
     let p:= actor A i; have ht:= act A hA hi; rw[pier A hA hi] at ht
     have he : Action.charge (⇑p)=⇑p:=by rw [show (⇑p : Density _ 6) =_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.1
     constructor
     · intro b j; rw [charge_west]; funext x; let y:= TorusPCAC.Stencil.conjGrid x; let v:= p y; let u:= wrap (S.side R i) j
       have ht:TorusPCAC.Stencil.charge _ v=p x:=by rw[charge_west] at he; exact congr_fun he x
       change TorusPCAC.Stencil.charge _ (v*((2:ℂ)⁻¹ • ((mote a _ _).val-(mote a _ _).val)))=_; rw [map_mul,ht,map_smul,map_sub,epoch_z,epoch_z]; rfl
     · intro b j u; have he : Action.flavor u (⇑p)= ⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.1 _
       rw [flavor_show] at he; rw [flavor_show]; funext x; let z:=wrap (S.side R i) j; let Q:=TorusPCAC.Ward.acts (proclaim u) (S.side R i)
       have hx:Q (p x)=p x:= congr_fun he x
       change Q ((p x)*((2:ℂ)⁻¹ • ((mote a _ _).val-(mote a _ _).val)))=_; rw[map_mul,hx,map_smul,map_sub,show Q _= _ from rhyme a (z+step b) x u,show Q _= _ from rhyme a (z-step b) x u]; rfl
     · intro b j; funext x; have he':Action.parity (⇑p)= ⇑p:=by rw[show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.2
       let v:= sprig a b (wrap M j) x; change QCD.Grass.grade ((p x)*v.val)=(p x)*v.val; rw [map_mul,show QCD.Grass.grade (p x)=p x from congr_fun he' x]; rw [show QCD.Grass.grade v.val=v.val from v.property]
     intro b j s v h; have he : Action.pin v s (⇑p)=⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).1 _ _ h
     rw [Patria.pinned]; rw[Patria.pinned] at he; funext U; let S':= S.side R i; let H':= pull s 0 U; let P:=Kit.disguise (copies 6 (hues (0:Site S') s (Patria.prism s) v.matrix.val)); change P (p H'* ((sprig a _ _ _).val))=(↑(signT s b):ℂ) • ((p U)*_); rw [map_mul P,show P _= _ from congr_fun he U,show P _= _ from shineJ a b (wrap M j) H' U 0 s (Patria.prism s) v.matrix.val (Patria.smoke s) (EuPin.retains s h),mul_smul_comm,show shiftE (n:=S') s 0 (wrap S' j)= wrap S' (s.act j) from ?_ ] -- rare phi
     rw[← wrap_signed]; simp [shiftE,Signed.actEquiv]
lemma sym_Q (u:Cover): Gall.SungP (⇑(G j u)):=by
       intro k V; let X':=Lattice.gauge k V; let Y:=slots 6 k; let P:=wrap M u; change Y (Ξ X'* ((2:ℂ)⁻¹ • ((mote a _ X').val-(mote a _ X').val)))=_; have he:Y (Ξ X')= Ξ V:=by rw [show Ξ X'= φ X' from congr_fun (act A hA hi) _, show Ξ V= φ V from congr_fun (act A hA hi) V]; exact Gall.dSung A hA hi k V
       rw [map_mul,he,map_smul,map_sub,show Y _= _ from κmolt a (P+step j) X' k,show Y _= _ from κmolt a (P-step j) X' k]; rfl
omit hA hi
lemma algeT : (∑ x: Site c,sprig a j x)=0:=by
        funext U; unfold sprig; rw [Finset.sum_apply,←smul_sum,sum_sub_distrib,show (∑ x:Site c, mote a (x+step j) U)=_ from Equiv.sum_comp (Equiv.addRight (step j:Site c)) (fun i=>mote a i U), show (∑ x:Site c,mote a (x-step j) U)=_ from Equiv.sum_comp (Equiv.subRight (step j:Site c)) (fun i=>mote a i U),sub_self,smul_zero]; rfl
lemma sailsZ : Gall.viaP A (G j) w i=0:=by
        unfold Gall.viaP; simp_rw [arrivesHere]; ext1 U; rw[ContinuousMap.sum_apply]; let F(i:Site M):= sprig a j i U; have h :∑ i:Site M,F i=0:= (Finset.sum_apply U Finset.univ (sprig a j)).symm.trans (congr_fun (algeT ..) U)
        change (∑ x:Site M,(Ξ U)*(sprig a j (wrap M (lift x)) U).val)=0; simp_rw[wrap_lift,←mul_sum]; rw[show (∑ x:Site M,(sprig a j x U).val)=0 from ?_,mul_zero]
        change (∑ x:Site M,(light _) (F x))=_; rw [← map_sum,h,map_zero]
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.sailsZ
#print axioms YM.Massive.PCAC.Oren.spoke
#print axioms YM.Massive.PCAC.Oren.nour
#print axioms YM.Massive.PCAC.Oren.sym_Q
