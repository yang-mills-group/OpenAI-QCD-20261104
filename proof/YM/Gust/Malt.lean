import YM.Gust.Nilo
import YM.Gust.Wig
set_option autoImplicit false
set_option maxHeartbeats 690000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala Marque
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n k:ℕ}(a b l:Axis)
open Tarn.ChargeQ
variable (A:Axis×Axis→ K.W)(hA:Persona T A)
variable {x:Points (m+1)} (v:Fin (m+1)→ K.W)(s:Fin (m+1)→ Bool)(hx:x∈conf _)(ht:Ward.onLine l x)(hp:∀ i,v i∈ Col T (s i))
variable (hb:a≠b)
local notation "L" i:arg j:arg=> A (i,j)
open Finset
include hf hK ht hp hx
lemma banners (hj:∏ i,tauMod (s i)=1) (hm:∀ i,v i≠0):∃ n:ℕ,∃ y:Fin (m+1)→ Mater T n, Wk y=v ∧ attenuation y x≠0:=by
       let c(i): Marque T:=⟨x i,v i,s i,hp i⟩; let r:= List.ofFn c; have h: lands r=grove K v x:=by unfold r grove lands; rw[List.map_ofFn]; rfl
       obtain ⟨n,t,hZ,hY⟩:= lotus hK hf l r (h ▸ (garden ..).2 hx) (fun i hi=>by obtain ⟨b,rfl⟩:= List.mem_ofFn.mp hi; exact hm b) (fun i hi=>by obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hi; exact ht b) (show grades r= _ from by unfold grades r; rw[List.map_ofFn,List.prod_ofFn]; exact hj)
       rw[h] at hZ; have hL:t.length=m+1:= by have h:= congr_arg List.length hZ; simpa only[wall,List.length_map,grove,List.length_ofFn] using h
       let V(i:Fin (m+1)):= t.get (Fin.cast hL.symm i); let Y(i:Fin (m+1)):= (V i).2; have he :t=List.ofFn V:=by
            refine List.ext_get (by simpa only[List.length_ofFn]) (fun j hj ht=> ?_); rw[List.get_ofFn]; rfl
       have hp(i): ((V i).1,(V i).2.v 0)=(x i,v i):=by
           unfold wall grove at hZ; rw [he,List.map_ofFn] at hZ; exact congr_fun (List.ofFn_inj.mp hZ) i
       refine ⟨n,Y,funext fun i=> congr_arg Prod.snd (hp i), mul_ne_zero ?_ ?_⟩
       · intro h; have H:= led_sq (List.ofFn (fun i=> (Y i).u)); rw [h] at H; simp at H
       · apply prod_ne_zero_iff.mpr; intro i _; have hh:=hY i; have he:wall t i.succ=grove K (fun j=> (Y j).v i.succ) x:=by
                rw[he]; unfold wall grove; rw[List.map_ofFn]; apply congr_arg; funext j; exact Prod.ext (show (V j).1=x j from congr_arg Prod.fst (hp j)) rfl
         rw [he,grooved] at hh; exact hh
omit hp ht hx
lemma cap_fall (h: ∀ y:E4,Points.cons y x∈ conf _→∀ d:Axis, phot (fun a b=>A (a,b)) v x d b y=0) (hx:x∈conf _): locCharge K A x v a b l:=by
        let S(n):=gustL x v (fun a b=>A (a,b)) a b l n; have hp:∀ᶠ n in atTop,S n=0:=by
             filter_upwards [eventually_all.mpr fun i=> Outer.petal_home a b l (x i)] with n he; funext y; unfold S gustL; refine sum_eq_zero ?_; intro d hd; unfold shineP stream; by_cases hh:D (basis d) (Outer.petal a b l n) y=0
             · simp[hh]
             · rw[h,smul_zero]; apply Work.A01.conf_cons hx; intro i ht; apply hh; rw[ht,D,(he i).fderiv_eq]; let P':E4→L[ℝ]ℝ:=PiLp.proj 2 (fun _=>ℝ) a; change fderiv ℝ P' _ _=_; rw[P'.fderiv]; change basis d a=_; simp[basis,Ne.symm (mem_erase.mp hd).1] -- stream rewrite def
        exact ⟨hp.mono fun i h=>by change Integrable (S i); rw[h]; exact integrable_zero .., Outer.Budget.same (Outer.no_budget (-1)) (hp.mono fun i h=>by change 0=∫ y,S i y; rw[h]; simp)⟩
include hx hp hA hb ht
lemma windWard: locCharge K A x v a b l:=by
        by_cases hu:∀ i,v i≠0
        · by_cases hj:∏ i,tauMod (s i)=1; · obtain ⟨n,y,H,h⟩:= banners hK hf l v s hx ht hp hj hu; rw[←H]; exact gustify hK hf hx A hA a b l y ht hb h
          apply cap_fall hK hf a b l A v _ hx; intro y h d; unfold phot
          have he:= hf.parity _ _ h (Fin.cons (L d b) v); let f:= Fin.cons (α:=fun _=>ℂ) 1 (fun i=> tauMod (s i)); let w:= Fin.cons (α:=fun _=> K.W) (L d b) v; have hh:T.parity ∘ w=fun i=> f i • w i:=by
               funext i; induction i using Fin.cases with
               | zero=> change T.parity (L d b)= (1:ℂ) • L d b; rw[hA.tense.parity,one_smul]
               | succ i=> exact (hue ..).1 (hp _)
          change K.total _ _ (T.parity ∘ w)=_ at he; rw[hh,MultilinearMap.map_smul_univ,Fin.prod_univ_succ,show f 0=1 from rfl,one_mul] at he; by_contra hp; exact hj (smul_left_injective ℂ hp (he.trans (one_smul ..).symm))
        push_neg at hu; obtain ⟨i,h⟩:=hu; exact cap_fall hK hf _ _ _ _ _ (fun y ht _=> (K.total _ _).map_coord_zero i.succ h) hx
omit hp
end YM.Massive.Gust
#print axioms YM.Massive.Gust.windWard
