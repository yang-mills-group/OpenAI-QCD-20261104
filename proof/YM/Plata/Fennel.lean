import YM.Plata.Paths
import YM.Rill.Leap
/-! Combine at full insertion before taking its sign. Anti-periodic phases of DIFFERENT odd marks could disagree individually. -/
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Filter Lattice Wilson Massive Massive.Lyre Massive.Romance
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Grass Chess Cells
open Cylinder Patria Patria.Depth Patria.Hub Patria.Exposure
open UV
open scoped Topology BigOperators Classical ComplexOrder
variable {F:ℕ}{n:Side}
noncomputable abbrev bank (b:Cover)(a:Axis)(x: Stud n 6):Stud n 6:= march b (Action.adj a x)
lemma banked (R : Regulator n 6)(hr:R.t=0)(T:Cells.Cut n)(hk:T.kind=.link)(b: Cover)(h:wrap n b=T.slide)(x:Insertion n 6)(hp: Potion (⇑x)): SignedEq (tallH T (⇑x)) (bank b T.pos (⇑x)):=by
      obtain ⟨k,hp⟩:= hp; have hs:= pic_match R T b h hk x hr k hp; rw [← tallC (C:=R.zeroCut) (⇑x) hr]; exact hs -- args
lemma invested (b:Cover)(a:Axis)(x y:Stud n 6): bank b a (x*y)= bank b a y * bank b a x:=by
      unfold bank; rw [show Action.adj a (x*y)= Action.adj a y* Action.adj a x from ?_,movesM]; funext U; rw [eye_value,Pi.mul_apply,tilt_mul]; simp [eye_value] -- Density coerces
lemma bank_one (b:Cover)(a:Axis): bank b a (1:Stud n 6)=1:=by
      funext V; unfold bank; rw [marches,eye_value]; change QCD.Kit.disguise _ (tilt _ 1)=1; rw [tilt_one,map_one]
lemma banking (b:Cover)(a:Axis)(x y:Stud n 6): bank b a (x+y)=bank b a x+bank b a y:=by funext U; simp [bank,marches,eye_value] -- march may simplify 
lemma marches_h(b:Cover)(a:Axis)(x:Stud n 6)(z:ℂ): bank b a (z • x)= star z • bank b a x:=by funext U; simp [bank,marches,eye_value]
lemma bank_zero(b:Cover)(a:Axis): bank b a (0: Stud n 6)=0:=by funext U; simp[bank,marches,eye_value]
variable {C:Sequence}{β ε:ℝ}{P:Calibration C}
-- Single reference entries at a cutoff
structure Stem where
      d:ℕ
      x:Label d
      y:Cover
abbrev Stem.k (P: Calibration C)(i:ℕ)(x:Stem):Insertion (C.S.side (C.R i) (C.N i)) 6:=P.physical none i x.x x.y
noncomputable abbrev task (P: Calibration C)(i:ℕ)(l:List Stem): Insertion (C.S.side (C.R i) (C.N i)) 6:= (l.map (Stem.k P i)).prod
def Stave (P:Calibration C)(v: Stem)(b:Cover)(a:Axis): Stem:= ⟨_,P.sym.adj _ a v.x,(Signed.mirror a).act v.y+b⟩
noncomputable abbrev sector (P:Calibration C)(v:List Stem)(b:Cover)(a:Axis): List Stem:= v.reverse.map (fun i=>Stave P i b a)
variable (hP:P.System)
variable {k:ℕ}
include hP
open SourceRead
variable (v:Stem)(b:Cover)(a:Axis)
lemma reflects (h:P.Mixing v.d k):bank b a ⇑(Stem.k P k v)= ⇑(Stem.k P k (Stave P v b a)):=by
    let c:=C.S.side (C.R k) (C.N k); let z:=P.sym.adj v.d a v.x; let B:= (Signed.mirror a).act v.y
    unfold Stem.k bank; rw [show Action.adj a ⇑(P.physical none k v.x v.y)= P.physical none k z B from (by unfold Calibration.physical; rw [hP.sections.star,h.star])]
    change march b (P.physical none k z B)= P.physical none k z (B+b); unfold Calibration.physical; let V(p:Cover)(x:Label v.d):= funext (hP.sections.localizes v.d c p x); rw[V,V]; exact Canvas.stylus ..
variable {a b}
lemma spokes (l:List Stem)(h:∀ i∈l,P.Mixing i.d k): bank b a ⇑(task P k l)= ⇑(task P k (sector P l b a)):=by
    induction l with
    | nil=> exact bank_one ..
    | cons v l ih=> simp only [task, List.map_cons,List.prod_cons, ContinuousMap.coe_mul, invested,reflects hP v b a (h _ (by simp))]; rw [ih (fun i hi=> h i (List.mem_cons_of_mem _ hi))]; simp only [sector,List.reverse_cons,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,task,List.map_map]; rfl
variable {I:Type*} [Fintype I]
noncomputable abbrev cash (P:Calibration C)(i:ℕ)(x:I→List Stem)(z:I→ℂ): Insertion (C.S.side (C.R i) (C.N i)) 6:= ∑ j:I,z j • task P i (x j)
lemma spindles (x:I→List Stem)(z:I→ℂ)(h:∀ i,∀ j∈x i,P.Mixing j.d k): bank b a ⇑(cash P k x z)=⇑(cash P k (fun i=> sector P (x i) b a) (star z)):=by
    suffices ∀ p:Finset I,bank b a ⇑(∑ j∈p,z j • task P k (x j))= ⇑(∑ j∈p,(star z) j • task P k (sector P (x j) b a)) from this _
    intro p; induction p using Finset.induction_on with
    | empty=> simp [bank_zero] -- 
    | @insert i p hp ih =>simp only [Finset.sum_insert hp,ContinuousMap.coe_add, ContinuousMap.coe_smul,Pi.star_apply, banking,marches_h]; rw [spokes hP _ (h _),ih]; rfl -- rewrite order
variable (T:Tiling (C.S.side (C.R k) (C.N k)))(p:T.Cell)(r:ℕ)
noncomputable abbrev passes (P:Calibration C)(adj:Bool)(a:Axis)(y w:Cover)(x:List Stem):= if adj then sector P x w a else sector P (sector P x y a) w a
abbrev turns (adj:Bool)(z:ℂ):= if adj then star z else z
lemma debts (x:I→List Stem)(z:I→ℂ)(h:∀ i,∀ j∈x i,P.Mixing j.d k)(a:Axis)(s:Bool)(hT:T.kind=.link)(hv: ((C.A k).regulator).t=0)(hx:Potion (⇑(cash P k x z))): SignedEq (road (pathT T (trace T p a r s)) (cash P k x z)) (⇑(cash P k (fun i=> passes P s a (y T p a) (hail T p a r) (x i)) (fun i=>turns s (z i)))):=by
    let u:=T.bandCut p a; let t:= T.bandCut (peak T p a r) a; let R:=(C.A k).regulator; let K:= cash P k x z
    have he(b:Cover)(v:T.Cell)(h':wrap (C.S.side (C.R k) (C.N k)) b=(T.bandCut v a).slide) (x':I→List Stem) (z':I→ ℂ)(hZ:∀ i,∀ j∈x' i,P.Mixing j.d k)(hx:Potion (⇑(cash P k x' z'))): SignedEq (tallH (T.bandCut v a) (cash P k x' z')) (⇑(cash P k (fun i=> sector P (x' i) b a) (star z'))):=by
          rw [← spindles hP x' z' hZ]; exact banked R hv (T.bandCut v a) hT b h' _ hx
    cases s
    · let f(i):=sector P (x i) (y T p a) a; let V:=cash P k f (star z); have hL:SignedEq (tallH u K) (⇑V):=he _ _ (fenceP T a p hT) _ _ h hx; have hV:Potion (⇑V):=by
              have hp:Potion (tallH u K):= Goblet.potW [u] _ hx
              rcases hL with hL|hL
              · rw [← hL]; exact hp
              rw [hL] at hp; have hh:= Goblet.potscaling hp (-1:ℂ); simpa only[neg_one_smul,neg_neg] using hh
      have hZ: ∀ i,∀ j∈f i,P.Mixing j.d k:=by rintro i j hj; obtain ⟨j',hm,rfl⟩:=List.mem_map.mp hj; exact h i j' (List.mem_reverse.mp hm)
      have hf':SignedEq (tallH t V) (⇑(cash P k (fun i=> passes P false a (y T p a) (hail T p a r) (x i)) (fun i=>turns false (z i)))):=by
          have hh:= he _ _ (fence T a p r hT) f (star z) hZ hV; rw[star_star] at hh; exact hh
      exact (Goblet.applauds T [(peak T p a r,a)] _ _ hL).trans hf'
    exact he _ _ (fence T a p r hT) x z h hx
end YM.Plata
#print axioms YM.Plata.banked
#print axioms YM.Plata.invested
#print axioms YM.Plata.debts
