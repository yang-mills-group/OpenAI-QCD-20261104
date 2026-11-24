import YM.Gust.Kin
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust.Kind
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
noncomputable def bit : Ix→Ix→ℂ
| some i, some j => if i>j then -1 else 1
| _,_=>1
/-- Kuhn sign: blocks of distinct nonempty extra jar anticommute. -/
noncomputable def lead (i:Ix)(L:List Ix):ℂ:= (L.map (bit i)).prod
noncomputable def led : List Ix→ℂ
| []=> 1
| i::l=> lead i l*led l
noncomputable def cross (u v:List Ix):ℂ:= (u.map (fun x=>lead x v)).prod
lemma bit_square(x y:Ix): bit x y * bit x y=1:=by unfold bit; split<;> first| (split <;> simp)| simp
@[simp] lemma bit_self(x:Ix):bit x x=1:=by cases x <;>simp[bit]
@[simp] lemma bit_star(x y:Ix):star (bit x y)=bit x y:=by unfold bit; split <;> first| (split <;> simp)| simp
lemma lead_sq(x:Ix)(v:List Ix):lead x v * lead x v=1:=by
     unfold lead; induction v with
     | nil=>simp
     | cons i l h=>simp only[List.map_cons,List.prod_cons]; rw[show bit x i*_*(bit x i*_)=bit x i*bit x i*((l.map ..).prod*(l.map (bit x)).prod) from by ring,h,bit_square,one_mul] -- implicit
lemma led_sq(x:List Ix): led x * led x=1:=by
      induction x with
      | nil=>simp[led]
      | cons i L hh=>rw [led,show lead i L*led L*(lead i L*led L)= lead i L*lead i L*(led L*led L) from by ring,hh,lead_sq,one_mul]
@[simp] lemma lead_nil(i:Ix):lead i []=1:=by simp [lead]
@[simp] lemma lead_cons(i x:Ix)(v:List Ix):lead i (x::v)=bit i x*lead i v:=rfl
lemma lead_ac (i:Ix)(u v:List Ix): lead i (u++v)=lead i u*lead i v:=by simp [lead]
@[simp] lemma lead_star(i:Ix)(u:List Ix):star (lead i u)=lead i u:=by induction u with | nil=>simp|cons i l ih=> simp [ih]
@[simp] lemma led_star(u:List Ix):star (led u)=led u:=by induction u with|nil=>simp[led]|cons i l ih=>simp[led,ih]
lemma cross_ac(u v w:List Ix):cross (u++v) w=cross u w*cross v w:=by simp[cross]
lemma cross_ad(u v w:List Ix):cross u (v++w)=cross u v * cross u w:=by
      induction u with|nil=>simp[cross]|cons i L hh=>simp only[cross,List.map_cons,List.prod_cons,lead_ac] at *; rw [hh]; ring
@[simp] lemma cross_cons (i:Ix)(u v:List Ix):cross (i::u) v=lead i v*cross u v:=rfl
@[simp] lemma cross_nil(v:List Ix):cross [] v=1:=rfl
lemma turnL(l w:List Ix): led (l++w)=cross l w*(led l*led w):=by induction l with|nil=>simp[led]|cons i l h=> simp only [List.cons_append,cross_cons,led,h,lead_ac]; ring
lemma cross_sq(l v:List Ix):cross l v*cross l v=1:=by induction l with|nil=>simp|cons i l ih=> rw[cross_cons,show lead i v * cross l v * (lead i v*cross l v)=lead i v*lead i v*(cross l v*cross l v) from by ring,ih,lead_sq,one_mul]
lemma lead_perm(i:Ix){u v:List Ix}(h:u.Perm v):lead i u=lead i v:=(h.map _).prod_eq
lemma cross_reverse_l(u v:List Ix):cross u.reverse v=cross u v:=(List.reverse_perm u|>.map _).prod_eq
lemma cross_reverse_r(u v:List Ix):cross u v.reverse=cross u v:=by induction u with|nil=>simp|cons i u h=> rw[cross_cons,cross_cons,h,lead_perm _ (List.reverse_perm _)]
lemma reversed_v(u:List Ix):led u.reverse= cross u u*led u:=by
     induction u with
     | nil=>simp[led,cross]
     | cons i u h=>
           have he:=lead_sq i u; rw[List.reverse_cons,turnL,cross_reverse_l,h,led]; nth_rw 1 [show i::u=[i]++u from rfl]; -- choose rewriting?
           simp only [cross_ac,cross_cons,lead_cons,bit_self,mul_one,one_mul,lead_nil,cross_nil]
           -- remaining cross u with right
           rw[show cross u (i::u)=cross u [i]*cross u u from cross_ad u [i] u,led]
           simp only [led,lead_nil,mul_one,cross_nil]; -- ring
           linear_combination - cross u [i]*cross u u*led u*he
abbrev turnW(i: J)(u:List Ix):ℂ:= (u.map (fun x=> mark x i)).prod
lemma lead_sel (i:Fin n)(u:List Ix): lead (some i) u = ∏ j ∈ (Finset.univ.filter (fun x=> x < i)),turnW j.succ u:=by
      induction u with
      | nil=> simp[turnW]
      | cons x u h=>
           simp_rw [turnW,List.map_cons,List.prod_cons]; rw[prod_mul_distrib, lead_cons,h]; unfold turnW; congr 1; rcases x with _|x; · simp [mark,Kind.q,bit,tauMod]
           by_cases h:x < i
           · rw[prod_eq_single_of_mem x (by simp [h])]
             · simp [bit,h,q,mark,tauMod]
             intro y _ h; simp [mark,q,h,tauMod]
           · simp only[bit,gt_iff_lt,if_neg h]; rw [prod_eq_one]; intro y hv; simp [mark,q,tauMod]; intro he; subst y; exact (h (mem_filter.mp hv).2).elim
lemma loan_nil (L:List Ix): lead none L=1:=by induction L with | nil=>simp | cons x l ih=>simp [ih,bit]
lemma cross_sel(x u v:List Ix)(h:∀ i:Fin n, turnW i.succ u=turnW i.succ v):cross x u=cross x v:=by
      induction x with
      | nil=>simp
      | cons y l h'=> simp only[cross_cons,h']; congr 1; cases y with
                                              | none=> simp[loan_nil]
                                              | some i=>simp only[lead_sel,h]
end YM.Massive.Gust.Kind
#print axioms YM.Massive.Gust.Kind.reversed_v
#print axioms YM.Massive.Gust.Kind.cross_sel
