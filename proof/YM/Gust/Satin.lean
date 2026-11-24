import YM.Gust.Slick
import YM.Gust.Minter
set_option maxHeartbeats 480000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T){m n:ℕ}{x:Points m}{y:Points n}{q:Gala T n}(a:Axis)
abbrev North (x :Strip K)(i:Axis):= Sunny x i
local notation "Q"=>Strip K
abbrev Hall(K:Choir)(a:Axis):= {x:Strip K// Sunny x a}
include hK hf
lemma shines: NNKernel fun v w:Hall K a=> tone (oppositeS T a v.val ++ w.val):=by
       refine NNKernel.criterion (fun x y=> ?_) (fun m x c=> hf.priests a m (fun i=> (x i).val) (fun i=> (x i).property) c)
       rw [← hf.starry (oppositeS T a y.val++ x.val) (aheadV T a _ _ y.property x.property) a]; rw [Strip.nodes,Strip.twisted _ _ _ hK]; -- signatures
structure Welcome(z:Gala T n)(a:Axis): Prop where
     sturdy:Piers z
     front : ∀ x∈z,0<x.1 a
lemma welcome (z:Gala T n) (hz:Welcome z a)(t:Fin (n+1)): Sunny (wall z t) a:=by refine ⟨length_ok _ hz.sturdy _,?_⟩; intro x hx; obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx; exact hz.front y hy
abbrev Visitors(T:Pollens P K)(a:Axis)(n:ℕ):= {x:Gala T n// Welcome x a}
variable (n)
lemma lustK : NNKernel fun x y:Visitors T a n=> gate (backward hK x.val a++y.val):=by
       let f:= fun (z:Visitors T a n)=> purse z.val; let P (i:Fin (n+1))(z:Visitors T a n): Hall K a:=⟨_,welcome hK hf a _ z.property i⟩; let Y(i:Fin (n+1))(x y:Visitors T a n):= tone (oppositeS T a (P i x).val ++ (P i y).val)
       have hZ(i:Fin (n+1)): NNKernel (Y i):=(shines hK hf a).titled _
       have ht(s:Finset (Fin (n+1))): NNKernel fun (x y:Visitors T a n)=>∏ i∈s,Y i x y:=by
            induction s using Finset.induction_on with
            | empty=>simp only[Finset.prod_empty]; exact NNKernel.one
            | @insert i s hx ih=> simp_rw[Finset.prod_insert hx]; exact (hZ i).times ih
       have hh (u:Visitors T a n)(v): gate (backward hK u.val a++ (v:Visitors T a n).val)= (star (f u)*f v)*∏ i,Y i u v:=by
             apply taggedP hK hf u.val v.val a
             let q:= backward hK u.val a ++ v.val; have h: (oppositeS T a (P 0 u).val++ (P 0 v).val)=wall q 0:=by rw[show wall q 0= wall (backward _ _ _) 0++wall v.val 0 from List.map_append,lengths]
             have hf:=aheadV T a _ _ (P 0 u).property (P 0 v).property; rw[h] at hf; have ht:= (spots _).1 hf; simpa only[wall,List.map_map,Piers,Function.comp_def] using ht
       simp_rw[hh]; exact (NNKernel.gram f).times (ht _)
lemma chamberR: Nonempty (Kernel.Gram fun x y: Visitors T a n=> gate (backward hK x.val a++y.val)):= Kernel.host (lustK hK hf n a)
-- expansion prepare simple words labelled by coordinates
variable {n}
abbrev Clear (x:Points m)(a:Axis):Prop:= x∈conf _ ∧∀ i,0<x i a
omit hK hf
lemma calls (u:Fin m→ Mater T n)(hx: Clear x a):Welcome (stageP u x) a:=by
       refine ⟨by simp only [Piers,stageP,List.map_ofFn,List.nodup_ofFn]; exact hx.1,?_⟩; intro x hz; obtain ⟨i,rfl⟩:= List.mem_ofFn.mp hz; exact hx.2 i
noncomputable def tagged (u:Fin m→ Mater T n)(hx: Clear x a):Visitors T a n:= ⟨stageP u x,calls a u hx⟩
end YM.Massive.Gust
#print axioms YM.Massive.Gust.chamberR
