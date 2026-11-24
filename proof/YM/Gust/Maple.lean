import YM.Gust.Kin
set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}(hK:K.Domestic)
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
local notation "Sz"=>Stake T n
local notation "Yr"=>Mater T n
namespace Mater
open Finsupp
variable (x:Mater T n)
variable {s:Signed}{p:EuPin}(h:p.Lifts s) (a:Axis)
noncomputable abbrev axisK (h:p.Lifts s)(T:Pollens P K)(n:ℕ): Stake T n →ₗ[ℂ] Stake T n := Finsupp.linearCombination ℂ (fun x:Mater T n=> plant (act hK h x))
noncomputable def barK (T:Pollens P K)(n:ℕ): Stake T n →ₛₗ[starRingEnd ℂ]Stake T n:=
    (Finsupp.linearCombination ℂ (fun i: Mater T n=> plant (eye hK a i))).comp ({toFun:=fun y=>y.mapRange (star:ℂ→ℂ) (star_zero _),map_add':=fun x y=>by ext;simp,map_smul':=fun x y=>by ext; simp}: Stake T n→ₛₗ[starRingEnd ℂ] Stake T n)
@[simp] lemma pin_pl : axisK hK h T n (plant x)=plant (act hK h x):=by simp [axisK,plant]
@[simp] lemma bar_pl : barK hK a T n (plant x)= plant (eye hK a x):=by simp[barK,plant]
lemma induced {P: Stake T n→Prop}(x:Stake T n)(h:P 0)(hu:∀ (i:Mater T n)(c:ℂ),P (c • plant i))(ht:∀ x y,P x→P y →P (x+y)):P x:=by
       induction x using Finsupp.induction_linear with
       | zero=>exact h
       | add _ _ hh hk=> exact ht _ _ hh hk
       | single i c=> simpa only[plant,smul_single', smul_eq_mul,mul_one] using hu i c
variable (v w u:Stake T n)
lemma spin_meets (M: Model K n):∃ N:Model K n,∀ v:Stake T n,morph M (axisK hK h T n v)=morph N v:=by
      refine ⟨fun k=> (M k).compLinearMap (fun _=> (T.spin p).toLinearMap),fun v=>?_⟩; induction v using induced with
      | h=>simp
      | hu i c=> rw [map_smul,map_smul,map_smul,pin_pl,once,once]; rfl
      | ht x y h k=> rw[map_add,map_add,map_add,h,k]
private lemma aliased {p : K.W → K.W} [DecidableEq J](f:J→K.W)(i:J)(v:K.W): p∘ update f i v= update (p∘ f) i (p v):=by funext j; by_cases h:j=i <;> simp[h]
noncomputable def barM (T: Pollens P K) (M:Model K n):Model K n:=fun b=>{
    toFun:=fun X=>star (M b (Ch T a ∘ X))
    map_update_add':=by
         intro dR' m i x y; letI:=dR'; simp only [aliased,map_add,(M b).map_update_add]; simp
    map_update_smul':=by intro dR m i c z; letI:=dR; simp only[aliased,map_smulₛₗ,(M b).map_update_smul,star_smul]; simp
}
lemma reflective (M: Model K n)(v:Stake T n): morph M (barK hK a T n v)=star (morph (barM a T M) v):=by
       induction v using induced with
       | h=> simp
       | hu i c=> rw[map_smulₛₗ,map_smul,map_smul,star_smul,bar_pl,once,once]; change star c • _= star c • star (star _);rw[star_star];rfl -- potential no goals.
       | ht x y h k=> rw[map_add,map_add,map_add,h,k,star_add]
namespace Fees
variable {v w u}
lemma spin_meets (hp:Fees v w): Fees (axisK hK h T n v) (axisK hK h T n w):=by intro M; obtain ⟨N,hZ⟩:= Mater.spin_meets (n:=n) (T:=T) hK h M; rw[hZ,hZ,hp]
lemma bars (hp:Fees v w):Fees (barK hK a T n v) (barK hK a T n w):=by intro M; rw[reflective,reflective,hp]
lemma swap(h:Fees v w):Fees w v:=fun i=>(h i).symm
lemma hop(h:Fees v w)(hP:Fees w u):Fees v u:=fun i=> (h i).trans (hP i)
lemma older:Fees v v:=fun _=>rfl
lemma scale(h:Fees v w)(c:ℂ):Fees (c • v) (c • w):=fun i=>by rw[map_smul,map_smul,h i]
lemma together(h:Fees v w)(p q:Stake T n)(hp:Fees p q):Fees (v+p) (w+q):=fun i=>by rw[map_add,map_add,h i,hp i]
end Fees
-- bar rotation relation
lemma bar_spin : Fees (axisK hK h T n (barK hK a T n v)) (barK hK a T n (axisK hK h T n v)) :=by
        induction v using induced with
        | h=> simp only[map_zero]; exact Fees.older
        | hu x c=> simp only [map_smul,map_smulₛₗ,bar_pl,pin_pl] -- order
                   exact Fees.scale (Fees.swap (eye_act hK x h a)) _
        | ht x y hh hk=> rw[map_add,map_add,map_add,map_add]; exact Fees.together hh _ _ hk
lemma origin (v:Stake T n): Fees (axisK hK h T n v) (axisK hK h T n v):=Fees.older
lemma modern {q:EuPin}{u v:Signed}{l:EuPin}(hv:q.Lifts u)(ht:l.Lifts v)(hp:l.coord=(p*q).coord)(z:Stake T n):Fees (axisK hK h T n (axisK hK hv T n z)) (axisK hK ht T n z) :=by
        have hK':v=s*u:= signsFaith (show Signed.inclusionO v= Signed.inclusionO (s*u) from ht.symm.trans (hp.trans (EuPin.life_mul h hv)))
        subst v; induction z using induced with
        | h=> simp only[map_zero]; exact Fees.older
        | hu x c=> simp only [map_smul,pin_pl]; refine Fees.scale (Fees.hop (w:=plant (act hK (EuPin.life_mul h hv) x)) (fun M=>?_) (Mater.slickD hK x (EuPin.life_mul h hv) l ht)) _
                   rw[once,once]; change M x.u _=M x.u _; refine congr_arg (M x.u) (funext (fun i=>?_)); change T.spin p (T.spin q _)=T.spin _ _; rw [T.spine hK p q _ _ h hv]; rfl
        | ht x y hh hv=> rw[map_add,map_add,map_add]; exact Fees.together hh _ _ hv
abbrev homeLift : EuPin.Lifts 1 1 := (map_one Signed.inclusionO).symm
lemma recoil : axisK hK homeLift T n v=v:=by
         induction v using induced with
         | h=>simp
         | hu x c=>
                    rw[map_smul,pin_pl]; have hp: act hK homeLift x=x:=by unfold act; cases x; congr 1; rw [T.spurs hK]; rfl -- structures dep
                    rw[hp]
         | ht x y hh hv=> rw[map_add,hh,hv]
lemma pale :Fees (barK hK a T n v) (barK hK timeAxis T n v):=by
        induction v using induced with
        | h=> simp only[map_zero]; exact Fees.older
        | hu x c=>simp only[map_smulₛₗ,bar_pl]; exact Fees.scale (heel hK x a) _
        | ht x y hh hv=> rw[map_add,map_add]; exact Fees.together hh _ _ hv
lemma twice : Fees (barK hK a T n (barK hK a T n v)) v :=by
        induction v using induced with
        | h=> simp only[map_zero]; exact Fees.older
        | hu x c=>simp only[map_smulₛₗ,bar_pl,show starRingEnd ℂ (starRingEnd ℂ c)=c from star_star c]; exact Fees.scale (risen hK x a) _
        | ht x y hh hv=> rw[map_add,map_add]; exact Fees.together hh _ _ hv
end Mater
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Mater.twice
#print axioms YM.Massive.Gust.Mater.modern
#print axioms YM.Massive.Gust.Mater.bar_spin
