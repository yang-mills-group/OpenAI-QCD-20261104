import YM.Eden.Roam
/-! # Self normal spin chart, equality on all AP stances and with dagger. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
open Lining Ferry Cylinder Elm Elm.SparK Elm.SparK.Arbor
variable {c f:Side}{N k m:ℕ}{I J:Type}[Fintype I][Fintype J]
lemma twist_a (A:Matrix I J ℂ)(B:Matrix J J ℂ)(C:Matrix J J ℂ): (A*C)*B*(A*C).transpose=A*(C*B*C.transpose)*A.transpose:=by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
-- generic recurrences with antisym
section
variable (A B:Matrix I I ℂ)(x:Alg I)(i j:I)
lemma outing : Wand (-A.transpose)=Wand A:=by
     ext x; unfold Wand; simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; refine sum_congr rfl fun j _=>?_; change (-A i j) • vary i (vary j x)= _; rw [show vary i (vary j x)= -vary j (vary i x) from CliffordAlgebra.contractLeft_comm _ _ x, neg_smul,smul_neg,neg_neg]; rfl
lemma sunset : vary i (dagger x)= grade (dagger (vary i x)) :=by
     have h (l:List I) : vary i (dagger (l.map atom).prod)=grade (dagger (vary i (l.map atom).prod)):=by
         induction l with
         | nil=> simp only [List.map_nil,List.prod_nil,dagger_one,vary_one,map_zero]
         | cons j l ih=> simp only [List.map_cons,List.prod_cons,dagger_mul, dagger_atom, vary_mul,ih]; by_cases he:i=j
                         · simp only [he,vary_self,one_mul,mul_one,map_add,dagger_mul, grade_atom, map_neg,map_mul,dagger_atom,neg_mul, mul_neg,neg_neg]; rw [add_comm]
                         rw [vary_off _ _ he]; simp [dagger_mul,grade_atom,dagger_atom]
     have hp (i': Finset I): vary i (dagger (mono i'))=grade (dagger (vary i (mono i'))):=by obtain ⟨W,-,-,he⟩:= expression i'; rw [he]; simpa only [List.map_ofFn] using h (List.ofFn W)
     rw [← write x]; simp_rw [map_sum,map_smul,map_smulₛₗ,hp]
lemma sunset_twice : Creek.v j (Creek.v i (dagger x))= dagger (Creek.v i (Creek.v j x)):=by
    rw [show Creek.v i (dagger x)=_ from sunset x i, anti]; change -grade (vary j (dagger (vary i x)))=dagger _; rw [sunset,grade_twice]; rw [show vary j (vary i x)= -vary i (vary j x) from CliffordAlgebra.contractLeft_comm _ _ x,map_neg,neg_neg]; rfl
lemma stars_wand : Wand (star A) (dagger x)= dagger (Wand A x):=by
   unfold Wand; simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,map_sum,map_smulₛₗ,sunset_twice]; rw [sum_comm]; rfl
lemma cast_voice : Creek.birth (Wand (star A)) (dagger x)=dagger (Creek.birth (Wand A) x):=by
     let Y:=Wand A; let X:=Wand (star A); have h(n:ℕ): (X^n: EndA I) (dagger x)=dagger ((Y^n:EndA I) x):=by
          induction n with|zero=> simp|succ n ih=> rw[pow_succ',pow_succ',ContinuousLinearMap.mul_apply, ih]; exact stars_wand ..
     have ht:= (Stays.birther Y x).map dagger.toAddMonoidHom continuous_dagger; refine (Stays.birther X _).unique (ht.congr_fun (fun i=>?_)); change (i.factorial:ℂ)⁻¹ • (X^i:EndA I) (dagger x)=dagger ((i.factorial:ℂ)⁻¹ • ((Y^i:EndA I) x)); rw[h,map_smulₛₗ]; simp
end
noncomputable def corsage (F:Train k)(c:Side)(m:ℕ)(x:Cover): Matrix (Sings m) (Sings m) ℂ:= let P:= mood m x (1:Grid c); -(P* Buzz.start c F 6*P.transpose)
noncomputable def rosewood (F:Train k)(c:Side)(m:ℕ): SpinPol m→ₗ[ℂ] SpinPol m:= (Creek.birth (Wand (corsage F c m 0))).toLinearMap
variable (x:Cover)(F:Train k)(hk:2≤ k)(s:Signed)
local notation "T"=> corsage F c m
local notation "M"=> Buzz.start c F 6
local notation "Q" z:arg => mood m z (1:Grid c)
local notation "Z"=> rosewood F c m
variable (A:SpinPol m)
include hk
lemma evolS : T x=T 0:=by
    let V:= BannerV c x; let P:= slab V; have h:Q x=Q 0*P:=by have hp:=roam (k:=m) 0 x (1:Grid c); rw [pull_one] at hp; rw [zero_add] at hp; exact hp.symm -- translate 1 defeq
    change -(Q x * _ *(Q x).transpose) = _; rw [h,twist_a, show P*M*P.transpose=M from sash F hk x ] ; rfl
lemma tintS (P:EuPin)(h:P.Lifts s) : changeVars (pinTT m s P) (Z A) = Z (changeVars (pinTT m s P) A):=by
    let X:=pinTT m s P; let T₀:=PinWheel c s P; have hz: X*(Q 0)=(Q 0)*T₀:=by have hh:= motionM (k:=m) 0 (1:Grid c) s P h; rw[Signed.act_zero,show pull s 0 (1:Grid c)=1 from (by funext i; unfold pull Step.read; split<;> simp)] at hh; exact hh.symm
    change changeVars X (Creek.birth (Wand _) A)=Creek.birth (Wand _) (changeVars X A); rw [QCD.Anomaly.transfer]; congr 3 -- try
    symm; unfold corsage; dsimp only; rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ X.transpose,← Matrix.transpose_mul]; rw [hz,twist_a, psyche F hk s P h]
lemma colorS(u:su.El) : Z (changeVars (noir u m) A) = changeVars (noir u m) (Z A) :=by
    let P:= noir u m; let S:=Q 0; let X:=grame c u; have ht:P*S=S*X:=by let g(_ :Site c):=u; have hv:= gradient_m (k:=m) 0 (1:Grid c) g; rw [show Lattice.gauge g (1:Grid c)=1 from (by funext i; simp [Lattice.gauge,g])] at hv; exact hv.symm
    change Creek.birth (Wand _) (changeVars P A)=changeVars P (Creek.birth (Wand _) A); have hz:P*T 0*P.transpose=T 0:=by change P* (-(S*M*S.transpose))*_ = _; rw [Matrix.mul_neg,Matrix.neg_mul,←Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc _ _ P.transpose,← Matrix.transpose_mul, ht, twist_a,show X*M*X.transpose= M from vigil F hk u]; rfl
    rw [QCD.Anomaly.transfer,hz]
omit hk
lemma flavorS (u:FlavorTorus) : let P:= slab (byFlavor u (fun i : SpinMode m=>i.2)); Z (changeVars P A)=changeVars P (Z A):=by
    intro P; let S:=Q 0; let X:=slab (flavP c u); have ht:P*S=S*X:=(festival 0 (1:Grid c) u).symm
    change Creek.birth (Wand _) (changeVars P A)=changeVars P (Creek.birth (Wand _) A); have hz:P*T 0*P.transpose=T 0:=by change P* (-(S*M*S.transpose))*_ = _; rw [Matrix.mul_neg,Matrix.neg_mul,←Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc _ _ P.transpose,← Matrix.transpose_mul, ht, twist_a,show X*M*X.transpose= M from flavorRoll F u]; rfl
    rw [QCD.Anomaly.transfer,hz]
lemma gradeS : Z (grade A)=grade (Z A):=by let Y:=T 0; exact DFunLike.congr_fun ((stout Y).birthP.evenG.eq) A
include hk
lemma chargeS : Z (changeVars (masq m) A) = changeVars (masq m) (Z A):=by
    let P:=masq m; let X:=railN c; let S:=Q 0; have ht:P*S=S*X:=by have he:= reel_char (k:=m) 0 (1:Grid c); rw [show Massive.conjugate ∘ (1:Grid c)=1 from funext fun _=> Papyrus.recol_el] at he; exact he.symm
    change Creek.birth (Wand _) (changeVars P A)=changeVars P (Creek.birth (Wand _) A); have hz:P*T 0*P.transpose= -(T 0).transpose:=by change P* (-(S*M*S.transpose))*_ = _; rw [Matrix.mul_neg,Matrix.neg_mul,←Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc _ _ P.transpose,← Matrix.transpose_mul, ht, twist_a,show X*M*X.transpose= -(M).transpose from raised F hk ]; unfold corsage; dsimp only; rw [Matrix.mul_neg,Matrix.neg_mul,neg_neg,Matrix.transpose_neg, neg_neg, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul,← Matrix.mul_assoc]
    rw [QCD.Anomaly.transfer,hz, outing]
lemma adjS (a:Axis): UV.aSpin m a (Z A)= Z (UV.aSpin m a A):=by
    let P:=eyeW m a; let S:=Q 0; let X:=moonS c a; let H:=Signed.mirror a; have ht:P*S=Mstar S*X:=by
         have h:= festiveV (k:=m) 0 (1:Grid c) a -- from Hue uses k not m
         have he:pull (Signed.mirror a) 0 (1:Grid c)=1:=by funext i; unfold pull Step.read; split<;>simp
         rw[he,Signed.act_zero] at h; exact h.symm
    change changeVars P (dagger (Creek.birth (Wand _) A))= Creek.birth (Wand _) (changeVars P (dagger A)); have hz: P *T 0*P.transpose=star (T 0):=by
        change P* (-(S*M*S.transpose))*_ = star (-(S*M*S.transpose)); rw [Matrix.mul_neg,Matrix.neg_mul,←Matrix.mul_assoc,← Matrix.mul_assoc, Matrix.mul_assoc _ _ P.transpose,← Matrix.transpose_mul, ht, twist_a,show X*M*X.transpose= star M from slight F hk a,star_neg, Matrix.star_eq_conjTranspose,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; have h:Sᵀᴴ=Mstar S:=rfl; rw [h,← Matrix.mul_assoc]; rfl
    rw [QCD.Anomaly.transfer, hz,cast_voice]
end YM.QCD.Eden
#print axioms YM.QCD.Eden.adjS
#print axioms YM.QCD.Eden.tintS
