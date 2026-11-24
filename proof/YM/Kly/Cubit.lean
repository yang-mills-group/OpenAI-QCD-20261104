import YM.Kly.Jazz
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Filter Set Analysis
open Fields (pointMoment distinct)
open OS (Cross)
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ComplexOrder
variable {F:Fields}{S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
abbrev Vose (F:Fields):= E4 × F.W × Bool
abbrev plain (v:List (Vose F)):Cluster F:= v.map fun s=>(s.1,s.2.1)
abbrev Light (v: List (Vose F)):Prop:=∀ x∈v,Fields.homogeneous F x.2.2 x.2.1
noncomputable abbrev starb (v:List (Vose F)):Bool := v.foldr (fun x a=> xor x.2.2 a) false
noncomputable def bin (p q:Bool):ℂ:= if p&&q then -1 else 1
lemma sparkC(p q r:Bool) : bin p q * bin p r=bin p (xor q r)∧ bin p r*bin q r=bin (xor p q) r:=by cases p<;>cases q<;>cases r<;> norm_num [bin]
variable (H:Fields.Euclidean S)
include H
-- moving first element right
lemma blink(l r: Cluster F)(x:Plant F) (p:Bool)(hp: F.homogeneous p x.2)(y:List (Vose F))(hy:Light y)(h:distinct (F:=F) (l++ (x::plain y ++ r))): pointMoment S (l++(x::plain y ++ r))= bin p (starb y)* pointMoment S (l++ (plain y++ x::r)):=by
     induction y generalizing l with
     | nil=> rw [show bin p (starb (F:=F) [])=1 from by cases p <;> rfl,one_mul]; rfl
     | cons s y ih=>
          let u:Plant F:=(s.1,s.2.1); let z:= s.2.2; have he:plain (s::y)=u::plain y:=rfl; have hu:F.homogeneous z u.2:= hy s List.mem_cons_self
          have hx: distinct (F:=F) (l++ x::u::(plain y++r)):=h; have ht: distinct (F:=F) (l++ u::x:: (plain y++r)):=locations.mpr (List.Perm.nodup ((List.Perm.append_left l (List.Perm.swap ..)).map Prod.fst) (locations.mp hx)); let W:=l++[u]
          have hh:= ih W (fun i hi=>hy i (List.mem_cons_of_mem _ hi)) (show distinct (W++(x::plain y++r)) from by simpa only [W,List.append_assoc,List.cons_append,List.nil_append] using ht)
          calc _ = bin p z* pointMoment S (W++ (x::plain y++r)):= by unfold W bin; simp only [he,List.cons_append,List.append_assoc,List.nil_append]; exact H.swap _ _ _ _ hx _ _ hp hu -- H.swap oriented reversed?
               _ = _:= by rw [hh,← mul_assoc,(sparkC p z (starb y)).1]; unfold W; simp only [he,List.cons_append,List.append_assoc,List.nil_append]; rfl
lemma relays(l r:Cluster F)(x y:List (Vose F))(hx:Light x)(hy:Light y)(hp:distinct (F:=F) (l++ (plain x ++ (plain y++r)))): pointMoment S (l++(plain x++(plain y++r)))=bin (starb x) (starb y) * pointMoment S (l++ (plain y++(plain x++r))):=by
     induction x generalizing l with
     | nil=>rw [show bin (starb (F:=F) []) (starb y)=1 from by unfold starb; simp [bin],one_mul]; rfl
     | cons s x ih=>
          let i:Plant F:=(s.1,s.2.1); have ht:plain (s::x)= i:: plain x:=rfl; let A:=l++[i]
          have hP:distinct (A++ (plain x++(plain y++r))):=by unfold A; simpa only [ht,List.append_assoc,List.cons_append,List.nil_append] using hp
          have he:distinct (A++(plain y++(plain x++r))):=by
               apply locations.mpr; refine List.Perm.nodup (List.Perm.map _ (List.Perm.append_left A ?_)) (locations.mp hP); rw [←List.append_assoc,← List.append_assoc]; exact (List.perm_append_comm).append_right _ -- args
          calc _=pointMoment S (A++(plain x++(plain y++r))):=by simp only [ht,A,List.append_assoc,List.cons_append,List.nil_append]
               _=bin (starb x) (starb y)*pointMoment S (l++(i::(plain y++(plain x++r)))):=by rw[ih A (fun i hi=>hx i (List.mem_cons_of_mem _ hi)) hP]; simp only[A,List.append_assoc,List.cons_append,List.nil_append]
               _=_:=by
                    have hv:distinct (F:=F) (l++(i::plain y++(plain x++r))):=by simpa only [A,List.append_assoc,List.cons_append,List.nil_append] using he
                    change bin _ _*pointMoment S (l++(i::plain y++(plain x++r)))=_; rw [blink H _ _ i s.2.2 (hx _ List.mem_cons_self) y hy hv,←mul_assoc,mul_comm (bin (starb x) (starb y)),(sparkC _ _ _).2,ht]; rfl
omit H
variable (p:E4)
abbrev tranV (x:List (Vose F))(p:E4): List (Vose F):=x.map fun ⟨k,v⟩=> (k+p,v)
lemma remit (x:List (Vose F)) : plain (tranV x p)= carry (plain x) p:=by simp [plain,tranV,carry,List.map_map,Function.comp_def]
lemma stV(x:List (Vose F)): starb (tranV x p)=starb x:=by induction x with| nil=> rfl| cons i x ih=> rw[tranV,List.map_cons]; change xor i.2.2 (starb (tranV x p))=_; rw[ih]; rfl
lemma transV(x:List (Vose F))(h:Light x) : Light (tranV x p):=by intro y hy; obtain ⟨z,hz,rfl⟩:= List.mem_map.mp hy; exact h z hz
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.relays
#print axioms YM.Massive.Bridge.Kly.transV
