import YM.Lyre.Grid
import YM.Pods.Wander
/-! # Borel-coherent chess replicas across every designated physical tiling -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Set QCD QCD.Lat QCD.Tide QCD.Revolve QCD.RP QCD.Grass Lattice Wilson Matrix
open Chess Cells Romance Plum
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {F:ℕ}{n:Side}
variable (l:List (Band n))(x:Stud n F)
noncomputable def road : List (Band n)→Stud n F→Stud n F
 | [],x=> x
 | C::l,x=> tallH C (road l x)
lemma paintsM (C: Band n)(U:Grid n): tallH C x U= adapter (copies F (- Tide.lens C)) (Twist (copies F (- Tide.lens C))) (turn (x (C.pullC su U))):=by rw [huesT, RP.copies_neg,tilts,Twist, ← Matrix.star_eq_conjTranspose,star_neg,← copies_star,Tide.lens_star]
lemma drive (V:Grid n): road l x V= adapter (copies F (spinM l)) (Twist (copies F (spinM l))) (((⇑(turn (A:=Modes n F)))^[l.length]) (x (pull (linear l) (stride l) V))):=by
    induction l generalizing V with
    | nil=> rw [spinM_nil,copies_one]; simp [Twist,linear,stride,road]
    | cons a l ih=> rw [road, paintsM (road l x) a,ih, Grass.turns,twist_turn,adapt_together,← copies_mul,← spinM_cons,← twist_mul, ← copies_mul,← spinM_cons]; unfold Cut.pullC; rw [pull_pull,List.length_cons,iterate_succ_apply']; rfl -- convert iterate step.Application

lemma drive_closed (hu: Lyre.Potion x)(he:∀ C∈l,C.kind=.link)(h:linear l=1)(ht:stride l=0) : Chess.SignedEq (road l x) x:=by
    have hk:Even l.length:=(alcohol l h).1
    have hv:= closed_spin l he h ht; obtain ⟨b,hb⟩:= hu; rcases hv with hv| hv
    · apply Or.inl; funext i; rw [drive l x,h,ht,pull_id,twistW _ _ hk,hv, copies_one]; simp [Twist]
    have h(V:Grid n): road l x V=grade (x V):=by rw [drive l x,h,ht,pull_id,twistW _ _ hk,hv, RP.copies_neg, copies_one]; simp [Twist, adapter_neg]
    cases b; · exact Or.inl (funext fun i=> (h i).trans (hb i))
    exact Or.inr (funext fun i=> (h i).trans (hb i))
lemma road_add (x y:Stud n F): road l (x+y)=road l x + road l y:=by
   induction l with| nil=> rfl| cons C l ih=> rw [road,ih]; funext U; simp only [huesT,Pi.add_apply,road,map_add]
lemma road_real (u:ℝ): road l ((u:ℂ) • x)=(u:ℂ) • road l x:=by induction l with| nil=>rfl| cons C l ih=> simp_rw [road,ih,smog]; simp
lemma road_one : road l (1:Stud n F)=1:=by induction l with| nil=> rfl| cons C l ih=> rw [road,ih,smogOne]
lemma road_neg (x:Stud n F): road l (-x) = -road l x:=by simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] using road_real l x (-1)
lemma road_parity(p:Bool)(h:∀ V,Grass.Hom p (x V)):∀ V,Grass.Hom p (road l x V):=by
   induction l with
   | nil=> exact h
   | cons a l ih=>intro V; unfold road; rw [huesT]; have he:=ih (a.pullC su V); cases p <;> simp only [Grass.Hom,Plus,Minus,Bool.false_eq_true,↓reduceIte] at he ⊢ <;> rw [tilt_grade,he]; exact map_neg ..
lemma road_app (l p : List (Band n)): road (l++p) x=road l (road p x):=by induction l with|nil=>simp [road]|cons a l ih=>simp [road,ih]
lemma tallHy (C:Band n)(x:Stud n F): tallH C (tallH C x)=x:=by
    funext U; let K:Lat.Cut n F:= ⟨0,0,0⟩
    have hv : C.pullC su (C.pullC su U)=U:=by simp -- probe
    let X:Insertion n F:= ContinuousMap.const _ (x U) -- NO F shadow
    rw [huesT,huesT,hv]; have h' := ContinuousMap.congr_fun (pictured (R:=C) (C:=K) X) U; rw [paints K (picture C K X) C rfl, paints K X C rfl] at h'; exact h'
lemma road_symm (l:List (Band n)): road l.reverse (road l x)=x:=by induction l with| nil=>rfl| cons a l ih=> rw [List.reverse_cons,road_app]; simp [road,tallHy,ih]
lemma road_inj (l:List (Band n)): Injective (road (F:=F) l):= LeftInverse.injective (fun x=>road_symm x l)
variable {T:Cells.Tiling n}(u:TapeWalk n T)
lemma touringM (hu:T.kind=.link)(h:Lyre.Potion x)(p:T.Cell)(v:TapeWalk n T)(he:finish T p u=finish T p v): SignedEq (road (pathT T u) x) (road (pathT T v) x):=by
    let l:= v.reverse++u; have ht:finish T p l=p:=by rw [show l=_ from rfl,app,he,Romance.back]
    have hL : ∀ C∈pathT T l,C.kind= .link:=by intro C h; obtain ⟨⟨i,j⟩,-,rfl⟩:= List.mem_map.mp h; exact hu
    have hA := drive_closed (pathT T l) x h hL (destination l p ht).1 (destination l p ht).2
    let w:= (pathT T v).reverse; have hz: pathT T l=w++pathT T u:= by simp [pathT,l,w]
    have hp : road w (road (pathT T v) x)=x:= road_symm ..
    rw [hz,road_app] at hA; rcases hA with hA|hA; · exact Or.inl (road_inj w (hA.trans hp.symm))
    apply Or.inr; apply road_inj w; rw [road_neg,hp,hA]
lemma roadF (p:T.Cell)(g:T.Cell→ Set (Site n))(h:Steady (T:=T) g)(hx:Fence (g p) x):Fence (g (finish T p u)) (road (pathT T u) x):=by induction u with| nil=> exact hx| cons a u ih=> exact ih.tall (h a.1 _ a.2)
variable (T)
noncomputable def palmH (x:Stud n F)(i j:T.Cell):Stud n F:= road (pathT T (Romance.tag T i j)) x
lemma palm_at (p:T.Cell): palmH T x p p=x:=by simp [palmH,Romance.tag,road,pathT]
lemma bookR (p v:T.Cell) (u : TapeWalk n T) (h:Lyre.Potion x)(hT:T.kind= .link)(he:finish T p u=v):SignedEq (road (pathT T u) x) (palmH T x p v):=touringM x u hT h p _ (he.trans (tag_spec T p v).symm)
-- usable tiling theorem
lemma booked (K:Regulator n F)(h:T.kind=.link){I:Type*}(p:I→ T.Cell)(x:I→Stud n F)(hp:∀ i,Fence (T.chamber (p i)) (x i))(hh:∀ i,Lyre.Potion (x i)): Texture K T (fun i=> palmH T (x i) (p i)):=by
     constructor
     · intro i v; have he:= roadF (x i) (Romance.tag T (p i) v) (p i) T.chamber (chamber T) (hp i); rw [tag_spec] at he; exact he
     · intro i v; obtain ⟨b,hb⟩:=hh i; exact ⟨b,road_parity (pathT T (Romance.tag T _ v)) (x i) _ hb⟩
     intro z a i v; exact bookR (x i) T _ _ ((z,a)::(Romance.tag T (p i) v)) (hh i) h (by rw [finish,tag_spec])
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.booked
