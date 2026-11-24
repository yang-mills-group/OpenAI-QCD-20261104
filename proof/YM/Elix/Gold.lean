import YM.Avian.Rifts
/-! Triaxial families genuine count. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}
private lemma has_lot {d:ℕ}(hd:d≤3)(p:Pol G)(h:p∈ limited G d):∃ c:ℂ, ∃ l: Jet G →ₗ[ℝ] ℂ,∀ J,read J p=c+l J:=by
     rw [limited, MvPolynomial.restrictSupport_eq_span] at h
     induction h using Submodule.span_induction with
     | zero=>exact ⟨0,0,fun J=>by simp⟩
     | add p q _ _ hp hq=> obtain ⟨x,f,h⟩:=hp; obtain ⟨y,g,hg⟩:=hq; exact ⟨x+y,f+g,fun J=>by rw [map_add,h,hg,LinearMap.add_apply]; ring⟩
     | smul z p _ hp=> obtain ⟨x,f,h⟩:=hp; exact ⟨z*x,z • f,fun J=>by simp[h,mul_add]⟩
     | mem q h=> obtain ⟨M,hM,rfl⟩:=h; by_cases hp:M=0
                 · subst M; exact ⟨1,0,fun J=>by simp [Labels.read]⟩
                 obtain ⟨i,Q,hQ,hK⟩:= peel_weight hp
                 have hm: height M ≤d:=hM; have hR: Q=0:=by by_contra h; obtain ⟨p,i,-,he⟩:=peel_weight h; unfold generation at *; omega
                 rw [hR,add_zero] at hQ; rw [hQ]
                 let x:= (Complex.ofRealAm.toLinearMap.comp ((axes G i.1).coord i.2)).comp (LinearMap.proj (R:=ℝ) (φ:=Taylor G) i.1); refine ⟨0,x,fun J=>?_⟩; change read J (MvPolynomial.X i)=_; simp only [Labels.read,MvPolynomial.aeval_X,zero_add]; rfl
lemma read_tilt {d:ℕ}(H:G.Simple)(hd:d≤3)(p:Label G d) : ∃ c:ℂ,∀ J,read J p.val=c:=by
     obtain ⟨c,l,h⟩:= has_lot hd _ p.property.1; let t:Low G:=⟨c,l,0,0⟩; have he(J) :read J p.val=t.eval J:=by rw [h]; simp only[t,Low.eval,LinearMap.zero_apply,add_zero]
     have hl:l=0:= Low.linear_invariant (A:=t) H (Low.covariance (p:=p) (fun _ _=>rfl) he); exact ⟨c,fun J=>by rw[h,hl]; simp⟩
lemma squat {d:ℕ}(H:G.Simple)(hd:d≤3)(p:Label G d)(s:Signed)(hv:tensor s.ortho p=-p): p=0:=by
     obtain ⟨c,h⟩:= read_tilt H hd p; have he: changed (fun _=>Taylor.turn (s.ortho)⁻¹) p.val= -(p.val):= congr_arg Subtype.val hv; have hc: c=0:=by
            have ht:= eval_changed (fun _=>Taylor.turn (s.ortho)⁻¹) (0:Jet G) p.val; rw[he,map_neg, h,h] at ht; exact neg_eq_self.mp ht -- orientation
     apply label_ext; intro J; rw [h,hc]; exact Eq.symm (map_zero _)
end YM.StressFlux
namespace YM.Massive.Patria.Gall.Onyx
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
namespace Gourd
-- use computed test with inst consistency
abbrev Triple:=Axis × Axis × Axis
def fresh(x:Triple): Bool:= decide (x.1≠x.2.1 ∧ x.2.1≠x.2.2 ∧ x.2.2≠x.1)
abbrev Three:= {x:Triple//fresh x=true}
noncomputable def trot (P:Equiv.Perm Axis): Equiv.Perm Triple := Equiv.prodCongr P (Equiv.prodCongr P P)
lemma sealsQ(P:Equiv.Perm Axis)(i:Triple): fresh (trot P i)=fresh i:=by
     rcases i with ⟨i,j,k⟩; change fresh (P i,P j,P k)=_; unfold fresh; simp
noncomputable def troop(s:Signed):Equiv.Perm Three:= Equiv.subtypeEquiv (trot s.perm) (fun i=> by rw[sealsQ])
noncomputable def goodP (s:Signed)(k:Three):ℝ:= signT s k.val.1*signT s k.val.2.1*signT s k.val.2.2
noncomputable def beast : Nest Three:= { Q:=troop,c:=goodP,w:=fun s i=>by unfold goodP signT; split <;> split <;> split <;> norm_num,t:=Equiv.refl _, e:=1 }
lemma ncert (s:Signed)(k:Three): (goodP s k:ℂ)≠0:=by intro h; have hh:= Complex.ofReal_eq_zero.mp h; have he:= beast.w s k; change goodP s k*goodP s k=1 at he; rw[hh,zero_mul] at he; exact zero_ne_one he
local notation "Y"=> Plain beast 6
noncomputable abbrev lamp (a:Flavor 6)(i: Triple):= gamma6 a i.1 i.2.1 i.2.2
lemma pin_lamp(a:Flavor 6)(s:Signed)(p:EuPin)(h:p.Lifts s)(i j k:Axis) : pinAct p (gamma6 a i j k).val=(↑(signT s i*signT s j*signT s k):ℂ) • (gamma6 a (s.perm i) (s.perm j) (s.perm k)).val:=by
     let z:= trio i j k; let L:= (0:Multi 6)
     have hp:= ringM a z L L (by rw [cost_root]) s p h _ _ (trio_t i j k s p h)
     unfold L at hp; simp only [marked_root,mul_one,Complex.ofReal_one,one_mul,hem_ground] at hp; push_cast; exact hp
lemma sober(a:Flavor 6)(i j k:Axis): Quiet (gamma6 a i j k).val ∧ chargeAct (gamma6 a i j k).val=(gamma6 a i j k).val:=by
     let v:= (0:Multi 6); refine ⟨flora a _ (0:Multi 6) (0:Multi 6) (by rw [cost_root]),?_⟩; change chargeAct (bilinear _ _ _ v v)=_; rw [Oriole.breeze, show -(chargeMatrix*(trio i j k).transpose*chargeMatrix)=_ from trio_c i j k]; rfl
noncomputable def lamps(a: Flavor 6) : Plain beast 6:=⟨fun i=>lamp a i.val,by
    refine (show Meaning (fun s i=>troop s i) goodP id 1 6 (fun i:Three=>lamp a i.val) from ?_); exact ⟨fun i=>(sober ..).1,fun i=>(sober ..).2,fun s w h i=>pin_lamp a s w h ..,fun i=> (one_smul ℂ _).symm⟩⟩ -- troop_
local notation "b"=> ((⟨(0,1,2), by decide⟩):Three)
lemma taxP (s:Signed)(i j k:Axis)(h:fresh (i,j,k)=true): (goodP s ⟨(i,j,k),h⟩:ℂ)=visa [i,j,k] s:=by unfold goodP visa; push_cast; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rw [mul_assoc]
noncomputable def remnant:Y →ₗ[ℂ](Flavor 6→ℂ):= LinearMap.pi fun a=> feeP [0,1,2] ∘ₗ prism0 a (0:Multi 6) 0 ∘ₗ (UV.labels 6).subtype ∘ₗ LinearMap.proj b ∘ₗ (Plain beast 6).subtype
variable (x:Y)
local notation "L"=> (0: Multi 6)
lemma blank(x: StressFlux.Offer.spectral (G:=su) (d:=3) (fun s t=>troop s t) goodP)(i:Three): x.val i=0:=by
     rcases i with ⟨⟨i,j,k⟩,h⟩; let a:Three:=⟨(i,j,k),h⟩; let v:= x.val a; let s:= Signed.mirror i; apply StressFlux.squat (p:=v) QCD.simple le_rfl s -- arg
     have hz:Labels.tensor s.ortho v=(goodP s a:ℂ) • v:=x.property s a
     have hc:goodP s a= -1:=by have hp: i≠j ∧ j≠ k ∧ k≠i:= of_decide_eq_true h; simp only [goodP,a,s,signT,Signed.mirror]; simp [hp.1, Ne.symm hp.2.2] -- debug
     rw [hz,hc,Complex.ofReal_neg, Complex.ofReal_one]; apply Subtype.ext; exact neg_one_smul ℂ v.val
lemma tguardY (a:Flavor 6)(h:remnant x a=0)(i:Three): prism0 a L L (x.val i).val=0:=by
     let v(i:Three):= prism0 a L L (x.val i).val; have hb:v b=0:=germ _ _ h ?_; swap
     · refine roleS a _ _ _ _ _ _ _ (show 6≤10 by decide) b [0,1,2] (fun _=>rfl) (fun i=>?_) (fun i=>ncert _ _)
       let s:= Signed.mirror i; change (goodP s b:ℂ)*visa [0,1,2] s = (↑(marked s L*marked s L):ℂ); rw [taxP _ _ _ _,vpaid,marked_root,one_mul,Complex.ofReal_one]
     rcases i with ⟨⟨i,j,k⟩,h₁⟩; have he : i≠j ∧ j≠ k ∧ k≠i:=of_decide_eq_true h₁; obtain ⟨P,hP,hT,hK⟩:= StressFlux.extend_three i j k he.1 he.2.2.symm he.2.1
     let s:=flag P; obtain ⟨w,hw⟩:=EuPin.choice s; let G:Signed→Three→Three:= fun s i=> troop s i; have hJ:= roleP a L L 1 G goodP id x (by decide) b P w hw (show goodP s b=1 from by simp[goodP,signT,s,Cast.flag]); rw [hem_ground] at hJ
     let p:Three:=⟨_,h₁⟩; have hf:G s b=p:=Subtype.ext (show (P 0,P 1,P 2)=(i,j,k) by rw[hP,hT,hK]); change v (G s b)=conjug w (v b) at hJ; change v p=0; rw [←hf,hJ,hb]; simp[conjug]
local instance : AddCommGroup ↥Y:=Submodule.addCommGroup (R:=ℂ) (M:=Three→ Label 6) (p:=Plain beast 6)
lemma lightS : Injective remnant:=by
     have h(x:Y) : remnant x=0→ x=0:=by
         intro he; apply Subtype.ext; funext i; have hz:= congr_arg Subtype.val (blank (valet (fun s i=>troop s i) goodP id 1 (show 6 ≤ 10 by decide) x) i); exact denovo _ ((show Meaning _ _ _ _ _ _ from x.property).light i) (by decide) hz (fun a p q h=>by have hp:=Oriole.low p; have hq:=Oriole.low q; rw [Oriole.ground p (by omega),Oriole.ground q (by omega)]; exact tguardY x a (congr_fun he a) i) (fun _ p q h=> by have hx:= Oriole.low p; have ht:=Oriole.low q; omega)
     intro x y hP; refine sub_eq_zero.mp (h _ ?_); rw [map_sub,hP,sub_self]
noncomputable def bornT : (Flavor 6→ℂ)→ₗ[ℂ] Y:= {
  toFun:=fun x=>∑ i:Flavor 6,x i • lamps i,map_add':=fun x y=>by simp only [Pi.add_apply,add_smul,sum_add_distrib]
  map_smul':=fun c x=>by simp only [Pi.smul_apply, Finset.smul_sum,RingHom.id_apply,smul_smul,smul_eq_mul] }
lemma recenter (x:Flavor 6→ℂ): remnant (bornT x)=x:=by
    have ht(a i:Flavor 6): remnant (lamps a) i= if i=a then 1 else 0:=by
         let F:= flair [0,1,2]; have hh:trio 0 1 2=F:=by unfold trio; rw [if_neg (by decide)]; simp[F,flair,mul_assoc]
         change feeP _ (prism0 i L L (bilinear a a (trio 0 1 2) _ _))=_; rw [bareB]; by_cases he:i=a
         · simp only[he,and_self, if_true,hh,show feeP [0,1,2] F=1 from chosen _]
         simp [he]
    funext i; let g(a):= x a • lamps a
    change remnant (∑ a:Flavor 6,g a) i=_; rw [map_sum,Finset.sum_apply]; unfold g; simp only[map_smul, Pi.smul_apply, ht, smul_eq_mul]; simp
lemma on_demand: Surjective bornT:=fun i=> ⟨remnant i, lightS (recenter _)⟩
end Gourd
end YM.Massive.Patria.Gall.Onyx
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.on_demand
