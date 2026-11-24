import YM.Gust.Glob
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {K:Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n:ℕ}
namespace Gala
local notation "J"=>Fin (n+1)
local notation "I"=>Kind n
abbrev Fg (t:Gala T n):List (Kind n):= t.map fun i=>i.2.u
noncomputable def backward (t:Gala T n)(a:Axis):Gala T n:=t.reverse.map (fun i=>(Ortho.move (Signed.reflect a) i.1,tint hK a i.2))
lemma lengths (t:Gala T n)(a:Axis)(i) : wall (backward hK t a) i= oppositeS T a (wall t i):=by simp [wall,backward,oppositeS,tint,List.map_map,comp_def]
@[simp] lemma prim (v:Gala T n)(a:Axis): Fg (backward hK v a)= (Fg v).reverse:=by simp [Fg,backward,tint,List.map_map,comp_def]
lemma can (v:Gala T n)(i:J) : turnW i (Fg v) * turnW i (Fg v)=1:=by
       induction v with
       | nil=>simp[Fg,turnW]
       | cons t v h=> simp only [turnW,Fg,List.map_cons,List.prod_cons] at *; apply Eq.trans _ h; rw [show mark _ _ * _ * (mark _ _ * _) = (mark t.2.u i * mark t.2.u i)*(turnW i (Fg v)*turnW i (Fg v)) from by unfold turnW Fg; ring,turn_m,one_mul] -- use show
include hf
lemma mark_sum(v:Gala T n)(hv:Piers v)(i:J)(h:tone (wall v i)≠0): turnW i (Fg v)=1:=by
       let p:= xpos v; let c:Fin v.length→K.W:=fun j=> (v.get j).2.v i; have hp:tone (wall v i)= K.total _ p c:= introduces Prod.fst (fun x=>x.2.v i) v
       have hx:= hf.parity _ _ ((pier v).1 hv) c; let f (j:Fin v.length):= Kind.mark (v.get j).2.u i; rw [show T.parity ∘c=(fun j=> f j • c j) from funext (fun j=> (hue ..).1 ((v.get j).2.mem i)),MultilinearMap.map_smul_univ] at hx
       have he : ∏ j,f j=1 := smul_left_injective ℂ (show K.total _ _ c≠0 from hp ▸ h) (hx.trans (one_smul ℂ _).symm)
       have hh : (List.ofFn f).prod= ∏ i,f i:= List.prod_ofFn; rw[←he,←hh]; unfold turnW Fg; rw[List.map_map]; rw [show f=(Kind.mark · i) ∘ (fun (x:E4 × Mater T n)=>x.2.u) ∘v.get from rfl]; rw [←Function.comp_assoc,← List.map_ofFn,List.ofFn_get] -- name
open Finset
lemma washed(v:Gala T n)(a:Axis)(hv:Piers v): gate (backward hK v a) = star (gate v):=by
       have h(i:J): tone (wall (backward hK v a) i)=star (tone (wall v i)):=by rw [lengths]; exact hf.starry _ (length_ok _ hv i) a
       simp_rw [gate,h]; rw [star_mul,star_prod,show purse (backward hK v a)= cross (Fg v) (Fg v)*purse v from ?_, show star (purse v)=purse v from led_star _]
       by_cases ht : ∏ i: J,tone (wall v i)=0
       · rw [←star_prod,ht]; simp
       have hh: cross (Fg v) (Fg v)=cross (Fg v) []:= cross_sel _ _ _ (fun i=>by rw[mark_sum hf v hv i.succ (Finset.prod_ne_zero_iff.mp ht i.succ (mem_univ i.succ))]; simp [turnW]); have hz(v:List (Kind n)):cross v []=1:=by induction v with|nil=>simp|cons _ _ hh=>simp[hh]
       rw [hh,hz,one_mul,mul_comm]
       change led (Fg _)=_; rw[prim]; exact reversed_v _
lemma taggedP(v w:Gala T n)(a:Axis)(hv:Piers (backward hK v a++w)): gate (backward hK v a++w)=star (purse v)*purse w*∏ i:J,tone (oppositeS T a (wall v i)++wall w i):=by
       let V:= backward hK v a ++w; let X:= Fg v; let Y:=Fg w; have hu:Fg V=X.reverse++Y:=by unfold V; rw[show Fg _=Fg (backward hK v a)++Fg w from List.map_append,prim]
       have he i: wall V i= oppositeS T a (wall v i)++wall w i:=by unfold V; rw [show wall _ i=wall (backward hK v a) i++wall w i from List.map_append,lengths]
       let U(i:J):= tone (wall V i); let C:=∏ i,U i; have hh :∏ i:J,tone (oppositeS T a (wall v i)++wall w i)=C:= prod_congr rfl fun i _=> congr_arg tone (he i).symm
       rw [hh]; change led (Fg V)*C= star (led X)*led Y*C; by_cases h:C=0; · rw[h]; ring
       rw [led_star,hu]; have hq(i:J):turnW i Y=turnW i X:=by
            have ht:=mark_sum hf V hv i (prod_ne_zero_iff.mp h i (mem_univ i)); rw [hu] at ht; simp only [turnW,List.map_append,List.prod_append,List.map_reverse,List.prod_reverse] at ht
            calc
              _= turnW i X *(turnW i X*turnW i Y) :=by rw[←mul_assoc,show turnW i X*turnW i X=_ from can v i,one_mul]  -- Y=X
              _=_:=by rw [show turnW i X*turnW i Y=1 from ht,mul_one]
       rw [turnL,reversed_v,cross_reverse_l,cross_sel X Y X (fun i=> hq _)]; linear_combination (purse v*purse w*C)*(cross_sq X X) -- unfold purse
end Gala
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Gala.washed
#print axioms YM.Massive.Gust.Gala.taggedP
