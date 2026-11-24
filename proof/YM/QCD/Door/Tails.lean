import YM.QCD.Door.Pioneer
/-! # exact motion on short and long bark. Shears even. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Grass Creek Ledge Function NormedSpace Finset Lat Kit
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
variable {A B C D:Type*}[Fintype A][Fintype B]

-- auxiliary algebra gamma star on ring carrier, even

def rib (A: Type*) [Fintype A]: Dirac A→+*Dirac A :=
 { (surf A).toAddMonoidHom with map_one' := surf_one, map_mul' := surf_mul }
lemma surf_cont (A: Type*)[Fintype A]:Continuous (rib A):=(changeVars (tide A)).toLinearMap.continuous_of_finiteDimensional.comp continuous_cc
lemma surf_rib (x:Dirac A): surf _ x=rib A x:=rfl
lemma surf_grade (x:Dirac A): surf _ (grade x)=grade (surf A x):= by rw [← scud,← scud _] -- rw multiple?

lemma lift_p (F: Alg A→+* Alg A) (h:Continuous F) (X Y : EndA A) (H : ∀ x,F (X x)=Y (F x))(x): F (excess X x)= excess Y (F x):=by
 -- maps ring, series scalars rational coeff.
 let xX (i:ℕ) := ((((i.factorial:ℂ)⁻¹) • X^i):EndA A) x
 let yY (i:ℕ) := ((((i.factorial:ℂ)⁻¹) • Y^i):EndA A) (F x)
 have hx n: F (xX n)= yY n:=by
   have hv (c:Alg A): F ((↑n.factorial:ℂ)⁻¹ • c)=(↑n.factorial:ℂ)⁻¹ • F c:= by
     let H : ℚ:= ((n.factorial:ℚ)⁻¹)
     have hP (c: Alg A): H • c=((n.factorial:ℂ)⁻¹) • c:=by unfold H; change (((algebraMap ℚ ℂ) ((n.factorial:ℚ)⁻¹)) • c)=_; rw [map_inv₀,map_natCast]
     rw [← hP,← hP]; exact map_rat_smul F H c
   unfold xX yY; simp only [ContinuousLinearMap.smul_apply]; rw [hv]; refine congr_arg _ ?_; clear hv; induction n with
     | zero=> simp
     | succ n ih=> rw [pow_succ',ContinuousLinearMap.mul_apply,H,pow_succ',ContinuousLinearMap.mul_apply]; -- ih may depend envelop
                    rw [ih]
 have hm: HasSum yY (F (birth X x)):=by
     rw [show yY=(fun i=>F (xX i)) from funext fun i=> (hx i).symm]; exact (Stays.birther X x).map F.toAddMonoidHom h
 rw [excess,ContinuousLinearMap.sub_apply,map_sub,show F (birth X x)=_ from hm.unique (Stays.birther Y (F x)),excess]; rfl

variable [DecidableEq A][DecidableEq B]
lemma chop (X : Matrix A A ℂ)(Y: Matrix B B ℂ)(F:Matrix A B ℂ)(G:Matrix B A ℂ) (U V : Matrix (Pairs A) (Pairs B) ℂ) -- ignore
 (h:X∈ unitary _)(ht:Y∈unitary _)(x:Dirac (A⊕B)) :
    disguise (whole X Y) (shear (X*F*star Y) (Y*G*star X) x)= shear F G (disguise (whole X Y) x):=by
 unfold disguise shear; rw [adapt_together,adapt_together] 
 rw [whole_star]; simp [whole,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,← Matrix.transpose_mul, Matrix.mul_assoc,h.1,ht.1] -- check loops
 rw [← Matrix.mul_assoc (star Y),ht.1, Matrix.one_mul]

lemma chili (x: Dirac (A⊕B)): ∀ F:Matrix A B ℂ,∀ G: Matrix B A ℂ, surf _ (shear F G x)=shear Gᴴ Fᴴ (surf _ x):=by
 intro F G; have hx (i): surf _ (shear F G (atom i))=shear Gᴴ Fᴴ (surf _ (atom i)) :=by
    cases i
    next i=>
       change surf _ (shear _ _ (psi i))=shear _ _ (surf _ (psi _)); rw [surf_P,shear,shear,adapt_psi,adapt_bar,map_sum]; cases i <;> simp [map_smulₛₗ,surf_P,Fintype.sum_sum_type,Matrix.one_apply,ite_smul]
    next i=>
       change surf _ (shear _ _ (bar i))=shear _ _ (surf _ (bar _)); rw [surf_M,shear,shear,adapt_bar,map_neg,adapt_psi,map_sum]; cases i <;> simp [map_smulₛₗ,surf_M,sum_neg_distrib,Fintype.sum_sum_type,Matrix.one_apply,ite_smul]
 have hp (l:List _): surf _ (shear F G (l.map atom).prod)=shear Gᴴ Fᴴ (surf _ (l.map atom).prod):=by induction l with
 | nil=> simp [surf_one]
 | cons j l ih=> rw [List.map_cons,List.prod_cons,map_mul,surf_mul,surf_mul,map_mul,hx,ih]
 have hs (s): surf _ (shear F G (mono s))=shear Gᴴ Fᴴ (surf _ (mono s)):=by obtain ⟨w,-,-,hw⟩:= expression s; rw [hw]; simpa only [List.map_ofFn] using hp (List.ofFn w)
 rw [←write x]; simp only [map_sum,map_smul,map_smulₛₗ,hs]
end YM.QCD.Sway
