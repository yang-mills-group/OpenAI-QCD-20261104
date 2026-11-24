import YM.Clays.Mica
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
variable {C:ℝ}
variable {o:Site c}{p:Lat.Fields c N→L[ℂ]Lat.Fields c N}
lemma throughProd (s: Alg A→L[ℂ]Alg A)(hs:∀ x:Alg A,s (grade x)=grade (s x))(ht:∀ x y:Alg A,s (x*y)=s x*y+x*s y)(x y:Alg (A⊕B)): let q:=carry B s; q (x*y)=q x*y+x*q y:=by
   intro q; rw [← rewriteR A x,← rewriteR A y]; simp only [Finset.mul_sum,sum_mul,map_sum, ← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   unfold q; rw [wheel,speaks,speaks,wheel,wheel,carries_r,← quiet,speaks,quiet,ht,map_add,add_mul]; apply congr_arg₂ (·+·) rfl; split; rw [hs]; rfl
variable {I:Type}[Fintype I](h:Veins o p C)
local notation "X"=> Keys c N
local notation "S"=> Spine I
local notation "P" => Patio (Keys c N⊕Spine I)
namespace Veins
include h
lemma vanishes: p 1=0:=by have hf:= h.product 1 1; rw [one_mul,one_mul,mul_one] at hf; exact (add_left_cancel (by simpa only [add_zero] using (show _ = _ from hf.symm : p 1+p 1=p 1) : p 1+p 1=p 1+0)) -- lemma name
variable (I)
noncomputable def twirl : Patio (Keys c N⊕Spine I) →L[ℂ] Patio (Keys c N⊕Spine I):=by
    let v:= carry S p; let f:= LinearMap.comp v.toLinearMap (light _).toLinearMap; exact LinearMap.toContinuousLinearMap (f.codRestrict ((roomA _).toSubmodule) fun x=>evenCarry S p h.grade x.val (bright x))
lemma onPiece (x:P)(s:Finset S): pluck X s (h.twirl I x)=p (pluck X s x):=wing S p _ _ -- order h?
lemma twirlOne : h.twirl I 1=0:=by
    apply Subtype.ext; change carry S p 1=0; rw [← map_one (fiber S (A:=X)),← quiet,speaks,h.vanishes,map_zero]
lemma twirls (x y:P): h.twirl I (x*y)=h.twirl I x*y+x*h.twirl I y:= Subtype.ext (throughProd p h.grade h.product x.val y.val)
end Veins
-- all even support.Seam.Syntax
abbrev traceI (I:Type) := fun _i:I=>false -- q
local notation "B!"=>traceI I
local notation "Ξ"=> burst B!
-- unary mark generator one
noncomputable def echoI (A:Type)[Fintype A](i:I) : Patio (A⊕Spine I):= ⟨stake A (Ξ {i}) 1,even_stake _ _ ((flavor (traceI I) _).symm ▸ (show Hom false _ from (show Grass.grade (1:Alg A)=1 from map_one _)))⟩ -- casts
local notation "θ"=> echoI X
lemma itOwn (i:I): Polite B! {i} (echoI A i):= ⟨1,rfl⟩
lemma echoColor (i:I)(g: Frame c) : Cupola.parcelColor N g I (echoI (Keys c N) i)=echoI (Keys c N) i:=by
    apply Subtype.ext; change carry (Spine I) (slots N g).toLinearMap.toContinuousLinearMap (stake _ (Ξ {i}) 1)=_; rw [speaks,show (slots N g).toLinearMap.toContinuousLinearMap 1=1 from map_one (slots N g)]; rfl
namespace Veins
variable (b:ℂ)(i:I)
noncomputable def dies : P →L[ℂ] P:= b • ((LinearMap.mulLeft ℂ (echoI X i)).toContinuousLinearMap.comp (h.twirl I))
lemma fate (x:P): h.dies b i x=b • (θ i*h.twirl I x):=rfl
set_option maxHeartbeats 640000 in
noncomputable def incline : P→ₐ[ℂ] P:= AlgHom.ofLinearMap ((ContinuousLinearMap.id ℂ P+h.dies b i).toLinearMap) (by change 1+b • (echoI _ i * h.twirl I 1)=1; rw [twirlOne I h,mul_zero,smul_zero,add_zero]) fun x y=> by
     let F:=h.twirl I; let s:= θ i; have hs : s*s=0:= (itOwn i).nilpotent (itOwn i) (by simp); change x*y+b • (s*F (x*y))=(x+b • (s*F x))*(y+b • (s*F y)); rw [show F (x*y)=F x*y+x*F y from twirls I h x y]; have hf: b • (s*F x)*(b • (s*F y))=0:=by rw [mul_smul_comm,smul_mul_assoc,show s*F x*(s*F y)=0 by rw [show _*(s*F y)=s*s*(F x*F y) from by ring,hs,zero_mul],smul_zero,smul_zero]
     rw [mul_add,mul_add,add_mul,add_mul,hf,add_zero,smul_add,mul_smul_comm,smul_mul_assoc,show s*(x*F y)=x*(s*F y) from by ring, mul_assoc s (F x) y]; abel
lemma inclined (x:P): h.incline b i x=x+h.dies b i x:=rfl
lemma diesPiece {A:Finset I} {x:P}(hp:Polite B! A x): Polite B! ({i}∪A) (h.dies b i x):=((itOwn _).attached (politeStep _ hp rfl)).smooch b
lemma spins {g:Frame c} (x:P) : h.dies b i (Cupola.parcelColor N g I x)=Cupola.parcelColor N g I (h.dies b i x):=by
   rw [fate,fate,map_smul,map_mul,echoColor]; apply congr_arg; apply congr_arg; apply pluckVisible; intro j; rw [onPiece I h,partColor,partColor,onPiece,h.reflects] -- inspector
lemma diesClad (x:P)(Y:Support c)(hx: clad (limits Y) x.val): clad (limits Y) (h.dies b i x).val :=( (clad.gates _ ((region _).one_mem) _).mul (reCarry p _ _ (h.localize _) _ hx)).scale b -- first clad.Y inference w. Gates proof needs types
lemma diesOff {Y:Support c} (x:P)(hx:clad (limits Y) x.val)(he:o∉Y): h.dies b i x=0:=by
    rw [fate,hshow,mul_zero,smul_zero]
 where hshow : h.twirl I x=0:=pluckVisible _ _ _ fun j=>by rw [onPiece I h,map_zero]; exact h.empty_set Y he _ (hx _)
lemma twirlPol (u:P)(t:Finset I){s:I→ℝ} : Cupola.scaler X s (h.twirl I u)= h.twirl I (scaler X s u):=pluckVisible _ _ _ fun i=>by rw [Cupola.pulse,onPiece,onPiece,Cupola.pulse,map_smul] -- t dummy
lemma restrict_at {M:Finset I} (x:P): shutter X M (h.dies b i x) = if i∈ M then h.dies b i (shutter X M x) else 0:=by
    rw [fate,map_smul,map_mul,stamen_h X B! {i} M _ (itOwn i),show shutter _ M (h.twirl I x)=h.twirl I _ from twirlPol h x M]; by_cases hi:i∈M
    · rw [if_pos (singleton_subset_iff.mpr hi),if_pos hi,fate]; rfl
    rw [if_neg (fun hh=>hi (singleton_subset_iff.mp hh)),if_neg hi,zero_mul,smul_zero]
end Veins
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Veins.incline
#print axioms YM.Massive.PCAC.Veins.restrict_at
