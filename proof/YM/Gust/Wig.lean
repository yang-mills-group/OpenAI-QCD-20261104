import YM.Gust.Sony
set_option autoImplicit false
set_option maxHeartbeats 920000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala QCD QCD.Lat
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n:ℕ}{x:Points (m+1)}(hx:x∈conf _)
local notation "F"=> Factory T n
local notation "S"=> polarM hK hf n
local notation "Hq"=> Clouds hK hf n
local notation "ξ"=> launch hK hf n
open Tarn.ChargeQ Patria Patria.Gall Onyx
variable (A:Axis×Axis→K.W) (hA:Persona T A) (V:Axis×Axis→(Factory T n).Ref 4)(hV:∀ i:Axis×Axis, Fees (launch hK hf n 4 (V i)) (plant (markR hf A hA i.1 i.2 n)))
local notation "L" i:arg j:arg=> A (i,j)
local notation "N"=>fun i j=>A (i,j)
local notation "R" i:arg j:arg=>markR hf A hA i j n
local notation "J"=>Fin (n+1)
local notation "JL"=> Fin (m+1)
set_option quotPrecheck false
local notation "Θ" => fun i j=>(S).project 4 (V (i,j))
open Finset
variable (a b l:Axis)(u:Fin (m+1)→ (Factory T n).Token)(v:Fin (m+1)→ Mater T n)(he:∀ i, Fees (stint hK hf (u i)) (plant (v i)))
abbrev Wk (v:Fin (m+1)→ Mater T n):= fun i=>(v i).v 0
noncomputable abbrev attenuation(v:Fin (m+1)→ Mater T n)(x:Points (m+1)):= led (List.ofFn (fun i=>(v i).u)) * ∏ i:Fin n,K.total _ x (fun j=>(v j).v i.succ)
include hA hx
lemma occupyX(t:E4)(hp:Points.cons t x∈conf _) : ValueP (Points.cons t x) (Fin.cons (markR hf A hA a b n) v)= attenuation v x* phot (fun a b=>A (a,b)) (Wk v) x a b t:=by
     let X: JL→ K.W:=Wk v; let Y:=fun i=>(v i).u; let Xq:=Points.cons t x; let f: Mater T n:= R a b; change ValueP Xq (Fin.cons f v)=_
     unfold ValueP phot; rw [List.ofFn_succ]; rw [show (Fin.cons (α:=fun _=> Mater T n) f v 0).u=(none:Kind n) from rfl,led,loan_nil,one_mul,Fin.prod_univ_succ]; let S0(i:Fin (n+1)):= K.total _ Xq (fun k=> (Fin.cons (α:=fun _=> Mater T n) f v k).v i)
     have h(i:Fin n): S0 i.succ=K.total _ x (fun j=>(v j).v i.succ):=by
          unfold S0; rw [show (fun k=> (Fin.cons (α:=fun _=> Mater T n) f v k).v i.succ)=Fin.cons (lampU P K) (fun j=>(v j).v i.succ) from ?_,hf.functor _ _ hp]; · rfl
          exact funext fun k=>by induction k using Fin.cases<;>rfl
     have hs:S0 0= K.total _ (Points.cons t x) (Fin.cons (L a b) X):=by unfold S0; apply congr_arg; ext1 i; induction i using Fin.cases<;>rfl
     change led (List.ofFn Y)*(S0 0*∏ i:Fin n,S0 i.succ)=attenuation v x* phot (fun a b=>A (a,b)) _ _ _ _ _; rw[hs]; simp_rw [h]; symm; apply Eq.trans (mul_assoc ..); apply congr_arg (led (List.ofFn Y) * ·); exact mul_comm ..
include hx hV he
lemma occupancy(t:E4)(hp:Points.cons t x∈conf _): Spiral.Outer.viewed (Θ) ((S).classTokens ∘ u) x a b t= attenuation v x* phot (fun a b=>A (a,b)) (Wk v) x a b t:=by
     -- Table-vs actual.LitReal.
     let X: JL→ K.W:=Wk v; let Y:=fun i=>(v i).u; let C':= attenuation v x; let Xq:=Points.cons t x; let f: Mater T n:= R a b
     let U:Fin (m+2)→(F).Token:= Fin.cons ⟨4,V (a,b)⟩ u
     have hPX (k:Fin (m+2)): Fees (stint hK hf (U k)) (plant (Fin.cons (α:=fun _=>Mater T n) f v k)):=by induction k using Fin.cases with
                                                                                                           | zero=> exact hV _
                                                                                                           | succ i=> exact he i
     exact Eq.trans (zoomT hK hf u (V (a,b)) Xq hp) (Eq.trans (fire hK hf Xq U (Fin.cons f v) hPX) (occupyX hf hx A hA a b v t hp))
-- core vanishes. width.n
def locCharge(K: Choir)(A:Axis×Axis→K.W)(x:Points (m+1))(p:Fin (m+1)→K.W)(a b l:Axis):Prop:=(∀ᶠ n in atTop,Integrable (gustL x p (fun a b=> A (a,b)) a b l n)) ∧ Outer.Budget (-1) (fun n=> ∫ y, gustL x p (fun a b=> A (a,b)) a b l n y)
-- compute any external cofactor.
omit he hV
include hK hA hf hx
lemma gustify (hl: Ward.onLine l x)(hb:a≠b)(hL: attenuation v x ≠0): locCharge K A x (Wk v) a b l :=by
       have h0(i:Axis×Axis):= united hK hf _ (enter (markR hf A hA i.1 i.2 n) (fitL hf A hA i.1 i.2)); choose V hV' using h0; let Vz:= fun a b=>(S).project _ (V (a,b));
       have hu(v:Mater T n):∃ p:(F).Token, Fees (stint hK hf p) (plant v):=by
             choose d hd using fun i:J=> hK.absorbs (v.v i); let D:=univ.sup d; have ht:Stay v D:=fun i=> hK.slope (show d i ≤ 2*D from (le_sup (f:=d) (mem_univ _)).trans (by change D≤2*D; omega)) (hd i)
             obtain ⟨z,h⟩:= united hK hf _ (enter v ht); exact ⟨⟨_,z⟩,h⟩
       choose p hh using fun i=> hu (v i); let q:JL→(S).Tag:=(S).classTokens ∘p
       obtain ⟨Y,H,Ht⟩:= estateR hK hf n
       obtain ⟨hc,hq⟩:= Spiral.Outer.drained _ hx q Vz Y (Hq) H Ht (dressC hK hf A hA V hV' Y H) (orientedSS hK hf A hA V hV') a b l hb hl
       let C':= attenuation v x; let X(r:ℕ):=gustL x (Wk v) (fun a b=>A (a,b)) a b l r; let Z(n):=Spiral.Outer.draught x q Vz a b l n
       have he:∀ᶠ n in atTop,∀ d∈ Outer.other a,∀ t:E4, Spiral.Outer.breeze Vz q x a b l d n t=C' * shineP (fun a b=>A (a,b)) (Wk v) x a b l d n t:=by
             filter_upwards [eventually_all.mpr fun i=> Outer.petal_home a b l (x i)] with n he d hd t; unfold Spiral.Outer.breeze shineP stream; by_cases h: D (basis d) (Outer.petal a b l n) t=0
             · simp [h]
             · rw [occupancy hK hf hx A hA V hV' d b p v hh t ?_] -- ℝ•ℂ
               · simp [Complex.real_smul,C']; ring
               · apply Work.A01.conf_cons hx; intro i ht; apply h; rw [ht,D,(he i).fderiv_eq]; -- fderiv projection at basis. 
                 let P':E4 →L[ℝ] ℝ:= PiLp.proj (𝕜:=ℝ) 2 (fun _:Axis=>ℝ) a; change fderiv ℝ P' _ _=_; rw [P'.fderiv]; change basis d a= _; simp[basis,Ne.symm (mem_erase.mp hd).1]
       have hF:∀ᶠ i in atTop, X i= fun y=> C'⁻¹ * Z i y:=by
              filter_upwards [he] with i h; refine funext fun y=> ?_; unfold Z X Spiral.Outer.draught gustL; refine Eq.trans ?_ (congr_arg (C'⁻¹ * ·) (?_ : ∑ d∈ Outer.other a, C' * shineP (fun a b=>A (a,b)) (Wk v) x a b l d i y= _)); · rw [← Finset.mul_sum,inv_mul_cancel_left₀ hL]
              exact sum_congr rfl fun j hj => (h j hj _).symm
       refine ⟨(hc.and hF).mono (fun i ⟨h,hx⟩=> by change Integrable (X i); rw[hx]; exact h.const_mul C'⁻¹),?_⟩ -- dependent casts !
       -- budget const multiple
       refine (hq.times C'⁻¹).same (hF.mono (fun i hi=>?_)); change _= ∫ y,X i y; rw[hi, integral_const_mul]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.gustify
