import YM.Massive.Papyrus.Purl
import YM.QCD.Door.Twig
/-! # Frame calculus for physical sampling on the cap (complex fiber matrices). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining
open QCD QCD.Lat Lattice Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker
variable {A B C: Type*}{d u:ℕ}
local notation "K" => starRingEnd ℂ
abbrev Hands (A:Type*) := (A×Lat.Fiber) × Flavor 6
abbrev Clap (A B: Type*) := A→ B→ Bundle
abbrev Whorl (A B: Type*):= Matrix (Hands A) (Hands B) ℂ
def advert (T:Clap A B): Matrix (A×Lat.Fiber) (B×Lat.Fiber) ℂ:= of fun i j=> T i.1 j.1 i.2 j.2
def nacre (T:Clap A B): Whorl A B:= Matrix.blockDiagonal (fun _: Flavor 6=> advert T)
variable (T:Clap A B)
lemma imprints (i:Hands A)(j:Hands B): nacre T i j= if i.2=j.2 then T i.1.1 j.1.1 i.1.2 j.1.2 else 0:=by unfold nacre; rw [blockDiagonal_apply]; rfl
lemma mark_star : Mstar (nacre T)= nacre (fun x y=> Mstar (T x y)):=by ext i j; rw [mstar,imprints,imprints]; split <;> first|rfl| simp
lemma nacre_flavor [Fintype A][Fintype B][DecidableEq A][DecidableEq B] (u:UV.FlavorTorus): UV.byFlavor u (fun i:Hands A=>i.2)*nacre T=nacre T* UV.byFlavor u (fun i=>i.2):=run_coil u Prod.snd Prod.snd (nacre T) (fun i j h=>by rw [imprints,if_neg h])
lemma nacre_mul [Fintype B](V:Clap B C): nacre T*nacre V = nacre (fun x y=>∑ j,T x j*V j y):=by
   unfold nacre; rw [←blockDiagonal_mul]; congr 1; funext i; ext ⟨p,a⟩ ⟨q,b⟩; simp only [Fintype.sum_prod_type, advert, Matrix.of_apply, Matrix.sum_apply, mul_apply]
@[simp] lemma nacre_one [DecidableEq A]: nacre (fun i j:A=> if i=j then 1 else 0)=1:=by ext ⟨⟨i,a⟩,w⟩ ⟨⟨j,b⟩,t⟩; by_cases h:a=b <;> by_cases he:i=j <;> by_cases hv:w=t <;> simp [imprints, one_apply,h,he,hv]
section sparse
variable [DecidableEq B]
def spar (p:A→B)(f:A→Bundle): Whorl A B:= nacre (fun x y=>if p x=y then f x else 0)
lemma spar_color (p:A→B)(f:A→Bundle): Mstar (spar p f)=spar p (fun i=> Mstar (f i)):=by unfold spar; rw [mark_star]; congr 1; funext i j; split; rfl; simp only [Mstar, Matrix.map_zero _ (show K 0=0 from map_zero _)]; -- notation
lemma spar_intro (p:A→B)(f:A→Bundle)(x:Hands A)(y:Hands B): spar p f x y= if p x.1.1 = y.1.1 ∧ x.2=y.2 then f x.1.1 x.1.2 y.1.2 else 0:=by by_cases hv:p x.1.1=y.1.1 <;> by_cases hh:x.2=y.2 <;> simp [spar,imprints,hv,hh]
lemma spar_mul [Fintype B](p:A→B)(f:A→Bundle)(U:Clap B C): spar p f*nacre U=nacre (fun x y=> f x* U (p x) y):=by
   unfold spar; rw [nacre_mul]; congr 1; funext i j; rw [sum_eq_single (p i)]; simp only [if_true]; intro y _ h; rw [if_neg h.symm, zero_mul]; simp
lemma spar_spar [Fintype B][DecidableEq C](p:A→B)(q:B→C)(f:A→Bundle)(g:B→Bundle): spar p f*spar q g=spar (fun i=>q (p i)) (fun i=> f i*g (p i)):=by rw [show spar q g=nacre (fun i j=> if q i=j then g i else 0) from rfl, spar_mul]; unfold spar; congr 1; funext i j; split; rfl; rw [mul_zero]
lemma spar_after [Fintype B](p:C≃B)(f:C→Bundle) [DecidableEq C] [Fintype C](T:Clap A C) : nacre T*spar (⇑p) f=nacre (fun x y=> T x (p.symm y)* f (p.symm y)):=by
    unfold spar; rw [nacre_mul]; congr 1; funext i j; rw [sum_eq_single (p.symm j)]; rw [if_pos (p.apply_symm_apply _)]; intro v _ h; rw [if_neg (fun hv=> h (by rw [← hv,p.symm_apply_apply])), mul_zero]; simp
-- id version & unit
@[simp] lemma spar_refl : spar (id:B→B) (fun _=>1)=1:=nacre_one
lemma spar_dex (f:B→ℂ) : spar id (fun i:B=>f i • 1)= diagonal (fun i=> f i.1.1):=by
    ext ⟨⟨i,a⟩,c⟩ ⟨⟨j,b⟩,d⟩; by_cases hh:i=j <;> by_cases he:a=b <;> by_cases hv:c=d <;> simp [spar_intro, one_apply,hh,he,hv]
end sparse
lemma mstar_smul (z:ℂ)(U:Bundle): Mstar (z • U)= star z • Mstar U:=by ext i j; simp [Mstar]
lemma mstar_touch (S:Mat): Mstar (touch S)=touch (Mstar S):=by
    ext ⟨i,a⟩ ⟨j,b⟩; by_cases h:i=j <;> simp [Mstar,Lat.touch,h]
lemma mstar_bulk : Mstar (1:Bundle)=1:=by rw [mstar_sq,star_one, transpose_one]
end YM.Massive.Lining
#print axioms YM.Massive.Lining.spar_after
