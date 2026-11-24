import YM.Clink.Angle
/-!
  Complete genuine observations.Extra insert.
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
open Next.Free QCD.Flume TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector Switch AxisB
variable {S: Scheme}{c R:Side}{i n:ℕ}(A: Run S n R 6)(hA:A.Actual)(hi:i ≤ n)(d:ℕ)(P:Plan d)(H:Train d)(m:ℝ)(a:Flavor 6)(x:Axis)(u:Averaging)
local notation "M"=> S.side R i
local notation "Ξ"=> actor A i
local notation "P!"=> cedar d P H m M
noncomputable def barb (b:Cover): Insertion (S.side R i) 6:=⟨fun V=> Ξ V * (forkT a (wrap M b) x P! V).val,(Ξ).continuous.mul (Continuous.subtype_val (fogue d P H m (wrap M b) a x))⟩ -- instance maybe topology
local notation "R!"=> barb (i:=i) A d P H m a
local notation "G"=> marque (i:=i) A true a
noncomputable def corm : Axis→ Cover→Insertion (S.side R i) 6:= marque A true a+barb A d P H m a
local notation "Z"=> corm (i:=i) A d P H m a
-- linear bodies.T for future
variable (F D:Axis→ Cover →Insertion (S.side R i) 6)
namespace Roars
lemma addition (h:Roars F)(hp:Roars D): Roars (F+D):=by
       have he(F D:Insertion M 6): (⇑(F+D):Density M 6)=(⇑F+⇑D):=rfl
       constructor<;> simp only [Pi.add_apply]
       · intro a b; have hx:=h.color a b; have hh:= hp.color a b; rw[he,charge_west]; rw [charge_west] at hx hh; funext V; let L:= TorusPCAC.Stencil.charge M (N:=6); change L (_+_)=_; rw [map_add]; exact congr_arg₂ HAdd.hAdd (congr_fun hx V) (congr_fun hh V)
       · intro a b p; have hx:=h.charm a b p; have hh:=hp.charm a b p; rw[he,flavor_show]; rw [flavor_show] at hx hh; funext V; let L:=TorusPCAC.Ward.acts (proclaim p) M; change L (_+_)=_; rw [map_add]; exact congr_arg₂ HAdd.hAdd (congr_fun hx V) (congr_fun hh V)
       · intro a b; rw[he]; funext U; change QCD.Grass.grade (_+_)=_; rw[map_add]; exact congr_arg₂ HAdd.hAdd (congr_fun (h.still a b) U) (congr_fun (hp.still a b) U)
       intro a b s v H; have hx:= h.pin a b s v H; have hh:=hp.pin a b s v H; rw[he,he,Patria.pinned]; rw [Patria.pinned] at hx hh; funext V; let L:= Kit.disguise (copies 6 (hues (0:Site M) s (Patria.prism s) v.matrix.val)); change L (_+_)= (_:ℂ) • (_+_); rw [smul_add,map_add]; exact congr_arg₂ HAdd.hAdd (congr_fun hx V) (congr_fun hh V)
end Roars
lemma blendT (F D:Cover→Insertion M 6)(h:TideT A u i (report A F u))(hp:TideT A u i (report A D u)): TideT A u i (report A (F+D) u):=by
       apply stampF; intro a b; have hV:= (h.moves i le_rfl).trans b a; have hf:=(hp.moves i le_rfl).trans b a; simp_rw[arrivesHere] at hV hf; funext U; let v:= wrap M b; let Q:=Kit.disguise (copies 6 (hues v 1 (heat b) 1)); change Q (_+_)= _+_; rw[map_add]; exact congr_arg₂ HAdd.hAdd (congr_fun hV U) (congr_fun hf U)
include hA hi
lemma b_stem : TideT A u i (report A (R! x) u):=by
        apply stampF A _ u; intro b t; funext U
        let p:=wrap M t; let V:=pull 1 p U; let K:=Kit.disguise (copies 6 (hues p 1 (heat t) 1)); change K (_*_)= Ξ U * _; have he: K (Ξ V)= Ξ U:=by
            apply congr_fun (g:=⇑Ξ) (f:=march t (⇑Ξ)) _ U; rw[act A hA hi,pier A hA hi]; exact Patria.Depth.first A i hi t
        let v:=wrap M b; rw[map_mul K,he,show K _= _ from favors d P H m v a x U p 1 (heat t) 1 (glares t) Revolve.Swing.none, show shiftE 1 p v=wrap M (b+t) from (by rw [map_add]; simp[p,v,Signed.actEquiv,shiftE]), show signT 1 x=1 from (by simp[signT]),Complex.ofReal_one,one_smul]; rfl
lemma angieP : Roars R!:=by
     let p:= actor A i; have ht:= act A hA hi; rw[pier A hA hi] at ht
     have he : Action.charge (⇑p)=⇑p:=by rw [show (⇑p : Density _ 6) =_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.1
     constructor
     · intro b j; rw [charge_west]; funext x; let y:= TorusPCAC.Stencil.conjGrid x; let v:= p y; let u:= wrap (S.side R i) j
       have ht:TorusPCAC.Stencil.charge _ v=p x:=by rw[charge_west] at he; exact congr_fun he x
       change TorusPCAC.Stencil.charge _ (v*(forkT a u b P! y).val)=_; rw [map_mul,ht,coreB]; rfl
     · intro b j u; have he : Action.flavor u (⇑p)= ⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.1 _
       rw [flavor_show] at he; rw [flavor_show]; funext x; let v:=wrap (S.side R i) j; let Q:=TorusPCAC.Ward.acts (proclaim u) (S.side R i)
       have hx:Q (p x)=p x:= congr_fun he x
       change Q ((p x)*(forkT a v b P! x).val)= _; rw[map_mul,hx,show Q _= _ from σeve d P H m v a b x u]; rfl
     · intro b j; funext x; have he':Action.parity (⇑p)= ⇑p:=by rw[show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.2
       let v:= forkT a (wrap M j) b P! x; change QCD.Grass.grade ((p x)*v.val)=(p x)*v.val; rw [map_mul,show QCD.Grass.grade (p x)=p x from congr_fun he' x]; rw [show QCD.Grass.grade v.val=v.val from v.property]
     intro b j s v h; have he : Action.pin v s (⇑p)=⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).1 _ _ h
     rw [Patria.pinned]; rw[Patria.pinned] at he; funext U; let S':= S.side R i; let H':= pull s 0 U; let Q:=Kit.disguise (copies 6 (hues (0:Site S') s (Patria.prism s) v.matrix.val)); let K:= forkT a (wrap M j) b P! H'; change Q (p H'* K.val)=(↑(signT s b):ℂ) • ((p U)*_); rw [map_mul Q,show Q _= _ from congr_fun he U,show Q _= _ from favors d P H m (wrap M j) a b U 0 s (Patria.prism s) v.matrix.val (Patria.smoke s) (EuPin.retains s h),mul_smul_comm,show shiftE (n:=S') s 0 (wrap S' j)= wrap S' (s.act j) from ?_ ]
     rw[← wrap_signed]; simp [shiftE,Signed.actEquiv]
lemma smolt (o:Cover) : Gall.SungP (⇑(R! x o)):=by
       intro k V; let X':=Lattice.gauge k V; let Y:=slots 6 k; let Q:=wrap M o; change Y (Ξ X'* (forkT a Q x P! X').val)=_; have he:Y (Ξ X')= Ξ V:=by rw [show Ξ X'= A.density i X' from congr_fun (act A hA hi) _,show Ξ V= A.density i V from congr_fun (act A hA hi) V]; exact Gall.dSung A hA hi k V -- error notation
       rw [map_mul,he,show Y _= _ from anthem d P H m Q a x V k]; rfl
omit hA hi
lemma sumA : ∑ o:Site c,forkT a o x (cedar d P H m c)=0:=by funext V; unfold forkT; simp_rw [Finset.sum_apply,Pi.sub_apply,sum_sub_distrib, hands, sub_self]; rfl
lemma port : Gall.viaP A (Z x) u i= Gall.viaP A (G x) u i:=by
       unfold Gall.viaP; have he: (Z x)=G x+ R! x:=rfl; rw[he]; simp_rw [arrivesHere, Pi.add_apply,sum_add_distrib, add_eq_left]; ext1 U; rw [ContinuousMap.sum_apply]; let L:=cedar d P H m M; let b(x':Site M):= forkT a x' x L; have hh:∑ o:Site M,QCD.Cove.light _ (b o U)=0:=by rw [← map_sum, ← Finset.sum_apply]; rw [show ∑ i,b i= _ from sumA ..]; simp
       change ∑ b':Site M,(Ξ U)*(QCD.Cove.light _ (b _ U))=0; simp_rw[wrap_lift,←mul_sum]; rw [hh,mul_zero]
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.angieP
#print axioms YM.Massive.PCAC.Oren.Roars.addition
#print axioms YM.Massive.PCAC.Oren.b_stem
#print axioms YM.Massive.PCAC.Oren.port
#print axioms YM.Massive.PCAC.Oren.smolt
