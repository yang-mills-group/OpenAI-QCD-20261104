import YM.Clays.Rates
import YM.MassiveQCD.Cupola.Shutter
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical
variable {A B:Type} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
open Onsite Tide QCD.Cove Creek
open Finset
open MassiveQCD MassiveQCD.Ribbon MassiveQCD.Cupola

variable {o:Site c}{p:Lat.Fields c N→L[ℂ]Lat.Fields c N}
-- pure linear algebra
structure Bean (p:Lat.Fields c N→L[ℂ]Lat.Fields c N) : Prop where
 grade (x): p (Grass.grade x)=Grass.grade (p x)
 product (x y): p (x*y)=p x*y+x*p y
variable {I:Type}[Fintype I](h:Bean p)
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
namespace Bean
include h
lemma vanishes: p 1=0:=by have hf:= h.product 1 1; rw [one_mul,one_mul,mul_one] at hf; exact (add_left_cancel (by simpa only [add_zero] using (show _ = _ from hf.symm : p 1+p 1=p 1) : p 1+p 1=p 1+0)) -- lemma name
variable (I)
noncomputable def twirl : Patio (Keys c N⊕Spine I) →L[ℂ] Patio (Keys c N⊕Spine I):=by
    let v:= carry S p; let f:= LinearMap.comp v.toLinearMap (light _).toLinearMap; exact LinearMap.toContinuousLinearMap (f.codRestrict ((roomA _).toSubmodule) fun x=>evenCarry S p h.grade x.val (bright x))
lemma onPiece (x:P)(s:Finset S): pluck X s (h.twirl I x)=p (pluck X s x):=wing S p _ _ -- order h?
lemma twirlOne : h.twirl I 1=0:=by
    apply Subtype.ext; change carry S p 1=0; rw [← map_one (fiber S (A:=X)),← quiet,speaks,h.vanishes,map_zero]
lemma twirls (x y:P): h.twirl I (x*y)=h.twirl I x*y+x*h.twirl I y:= Subtype.ext (throughProd p h.grade h.product x.val y.val)
end Bean
local notation "B!"=>traceI I
local notation "Ξ"=>burst B!
local notation "θ"=>echoI X
namespace Bean
variable (b:ℂ)(i:I)
noncomputable def dies : P →L[ℂ] P:= b • ((LinearMap.mulLeft ℂ (echoI X i)).toContinuousLinearMap.comp (h.twirl I))
lemma fate (x:P): h.dies b i x=b • (θ i*h.twirl I x):=rfl
set_option maxHeartbeats 640000 in
noncomputable def incline : P→ₐ[ℂ] P:= AlgHom.ofLinearMap ((ContinuousLinearMap.id ℂ P+h.dies b i).toLinearMap) (by change 1+b • (echoI _ i * h.twirl I 1)=1; rw [twirlOne I h,mul_zero,smul_zero,add_zero]) fun x y=> by
     let F:=h.twirl I; let s:= θ i; have hs : s*s=0:= (itOwn i).nilpotent (itOwn i) (by simp); change x*y+b • (s*F (x*y))=(x+b • (s*F x))*(y+b • (s*F y)); rw [show F (x*y)=F x*y+x*F y from twirls I h x y]; have hf: b • (s*F x)*(b • (s*F y))=0:=by rw [mul_smul_comm,smul_mul_assoc,show s*F x*(s*F y)=0 by rw [show _*(s*F y)=s*s*(F x*F y) from by ring,hs,zero_mul],smul_zero,smul_zero]
     rw [mul_add,mul_add,add_mul,add_mul,hf,add_zero,smul_add,mul_smul_comm,smul_mul_assoc,show s*(x*F y)=x*(s*F y) from by ring, mul_assoc s (F x) y]; abel
lemma inclined (x:P): h.incline b i x=x+h.dies b i x:=rfl
lemma diesPiece {A:Finset I} {x:P}(hp:Polite B! A x): Polite B! ({i}∪A) (h.dies b i x):=((itOwn _).attached (politeStep _ hp rfl)).smooch b
lemma twirlPol (u:P)(t:Finset I){s:I→ℝ} : Cupola.scaler X s (h.twirl I u)= h.twirl I (scaler X s u):=pluckVisible _ _ _ fun i=>by rw [Cupola.pulse,onPiece,onPiece,Cupola.pulse,map_smul] -- t dummy
lemma restrict_at {M:Finset I} (x:P): shutter X M (h.dies b i x) = if i∈ M then h.dies b i (shutter X M x) else 0:=by
    rw [fate,map_smul,map_mul,stamen_h X B! {i} M _ (itOwn i),show shutter _ M (h.twirl I x)=h.twirl I _ from twirlPol h x M]; by_cases hi:i∈M
    · rw [if_pos (singleton_subset_iff.mpr hi),if_pos hi,fate]; rfl
    rw [if_neg (fun hh=>hi (singleton_subset_iff.mp hh)),if_neg hi,zero_mul,smul_zero]
end Bean
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Bean.incline
#print axioms YM.Massive.PCAC.Bean.restrict_at
