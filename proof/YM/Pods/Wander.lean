import YM.Pods.Spy
import YM.Cells.Margins
/-! # Chess-board replica actual orientation path
Left-even or left-odd copies on a homogeneous-parity insertion may always
use matching projections. A single different value of the regulator β isn't allowed
in applying the eventual pressure estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Romance
open Function Filter Set QCD QCD.Lat QCD.Tide QCD.Revolve QCD.RP QCD.Grass Lattice Wilson Matrix
open Chess Cells
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {F:ℕ}{n:Side}(T:Cells.Tiling n) (R:Lat.Cut n F) (A:Insertion n F)
abbrev TapeWalk (n:Side) (T:Tiling n):= List (T.Cell×Axis)
abbrev pathT (t:TapeWalk n T): List (Band n):=t.map (fun (x,i)=> T.bandCut x i)
-- run right-to-left
noncomputable def finish (x:T.Cell) : TapeWalk n T → T.Cell
  | []=>x
  | (u,i)::t=> T.mate u i (finish x t)
lemma app (u v : TapeWalk n T)(x:T.Cell): finish T x (u++v)= finish T (finish T x v) u:=by induction u with | nil=> simp [finish] | cons i w ih=> rcases i with ⟨i,j⟩; simp [finish,ih]
lemma back (x:T.Cell)(u:TapeWalk n T): finish T (finish T x u) u.reverse=x:=by
    induction u with
    | nil=> rfl
    | cons i u ih=> rcases i with ⟨i,j⟩; rw [List.reverse_cons,app]; simp [finish,ih]
variable {T}
variable (u:TapeWalk n T)
lemma after_turn (x:T.Cell): T.omega (finish T x u)= linear (pathT T u)* T.omega x:=by
    induction u with
    | nil=> rw [show linear (pathT T [])=1 from rfl,one_mul];rfl
    | cons i u ih=> rcases i with ⟨i,j⟩; unfold pathT; simp only [finish,List.map_cons,T.turn,ih,linear,mul_assoc]
lemma after_move (x:T.Cell)(p:Site n): T.copyMap (finish T x u) p = maps (pathT T u) (T.copyMap x p):=by
    induction u with
    | nil => symm; change affine 1 (0:Site n) (T.copyMap x p)=T.copyMap x p; simp [affine]
    | cons a l ih=> rcases a with ⟨u,i⟩; rw [pathT, List.map_cons,maps_cons,Equiv.trans_apply,finish,T.after,ih]; rfl
lemma destination (x:T.Cell) (h:finish T x u=x): linear (pathT T u)=1∧ stride (pathT T u)=0:=by
    have hg: linear (pathT T u)*T.omega x=1*T.omega x:=by rw [← after_turn u,h,one_mul];
    have he:=mul_right_cancel hg; refine ⟨he,?_⟩; have ht:= after_move u x 0; rw [h] at ht; unfold maps at ht; rw [he] at ht; change T.copyMap x 0=affine 1 _ (T.copyMap x 0) at ht; simpa [affine] using ht.symm

lemma up (x:T.Cell)(i:Axis) : T.mate (x+step i) i x=x+step i:=by
    ext k; by_cases hk:k=i; · subst k; simp; ring
    rw [T.mate_off (x+step i) i x hk]; simp [hk]
lemma down (x:T.Cell)(i:Axis) : T.mate x i x=x-step i:=by rw [← T.mate_invol x i (x-step i),show T.mate x i (x-step i)=x from ?_]; have ht:= up (T:=T) (x-step i) i; rw [show (x-step i)+step i=x from sub_add_cancel ..] at ht; exact ht
lemma connect (x y:T.Cell): ∃ u : TapeWalk n T,finish T x u=y:=by
    obtain ⟨l,hL⟩:= tracks x y; subst y; induction l generalizing x with
    | nil=> exact ⟨[],rfl⟩
    | cons i l ih=> rcases i with ⟨i,h|h⟩; · obtain ⟨p,hp⟩:=ih (x+ step i); refine ⟨p++[(x+step i,i)],?_⟩; rw [app]; simp [finish,up]; exact hp
                    obtain ⟨p,hp⟩:=ih (x-step i); refine ⟨p++[(x,i)],?_⟩; rw [app]; simp [finish,down,Step.vec,stop]; simpa only [sub_eq_add_neg] using hp
variable (hu:T.kind= .link)
lemma path_price (l p : List (Band n))(x:Insertion n F): reels R (l++p) x=reels R l (reels R p x):=by induction l with | nil=>simp [reels] | cons a l ih=>simp [reels,ih]
lemma path_symm (l:List (Band n))(x:Insertion n F) : reels R l.reverse (reels R l x)=x:=by induction l with | nil=>rfl | cons a l ih=> rw [List.reverse_cons,path_price]; simp [reels,pictured,ih]
lemma path_inj (l:List (Band n)): Injective (reels R l):= LeftInverse.injective (path_symm R l)
lemma path_neg (l:List (Band n))(x:Insertion n F): reels R l (-x)= -reels R l x:=by
     induction l with
     | nil=>rfl
     | cons a l ih=> simp only [reels,ih]; rw [← neg_one_smul ℂ, pic_smul]; simp
lemma price₀ (l:List (Band n))(x:Insertion n F): ‖reels R l x‖=‖x‖:=by induction l with | nil=>rfl | cons a l ih=> simp [reels,pic_price,ih]
include hu
lemma touring (h:A∈ setOf Chess.Parity)(hR:R.t=0)(x:T.Cell)(v:TapeWalk n T)(he:finish T x u=finish T x v): SignedEq (reels R (pathT T u) A) (reels R (pathT T v) A):=by
    let l:= v.reverse++u; have ht:finish T x l=x:=by rw [show l=_ from rfl,app,he,back]
    have hL : ∀ C∈pathT T l,C.kind= .link:=by intro C h; obtain ⟨⟨i,j⟩,-,rfl⟩:= List.mem_map.mp h; exact hu
    have hA := picture_closed (pathT T l) R A hR h hL (destination l x ht).1 (destination l x ht).2
    let w:= (pathT T v).reverse; have hz: pathT T l=w++pathT T u:= by simp [pathT,l,w]
    have hp : reels R w (reels R (pathT T v) A)=A:= path_symm ..
    rw [hz,path_price] at hA; rcases hA with hA|hA; · exact Or.inl (path_inj R w (hA.trans hp.symm))
    apply Or.inr; apply path_inj R w; rw [path_neg,hp,hA]
omit hu
variable {g:T.Cell → Set (Site n)}
def Steady (g:T.Cell → Set (Site n)):Prop:=∀ (x y:T.Cell)(a:Axis),MapsTo (T.bandCut x a).reflect (g y) (g (T.mate x a y))
lemma margins (T:Tiling n)(k:ℕ): Steady (T:=T) (fun x=> T.margin x k):=by intro x y a i h; obtain ⟨P,rfl⟩:= T.pointed y i; change _∈T.margin _ k; rw [← T.after]; exact (T.reflected_margin ..).mp ((T.reflected_margin ..).mpr h)
lemma chamber (T:Tiling n): Steady (T:=T) T.chamber:=by intro x y a i h; obtain ⟨P,rfl⟩:= T.pointed y i; rw [← T.after]; exact (T.reflected_chamber ..).mp ((T.reflected_chamber ..).mpr h)
lemma reach_in (x:T.Cell)(h:Steady (T:=T) g)(he: Floors (g x) A): Floors (g (finish T x u)) (reels R (pathT T u) A):=by induction u with
     | nil=> exact he
     | cons i u ih=> rcases i with ⟨i,j⟩; exact pictures ih (h i _ j)
lemma gauge_reel (u:List (Band n))(h:Invariant A) : Invariant (reels R u A):=by induction u with | nil=> exact h | cons a u ih=> exact picture_inv ih
lemma reel_parity (u:List (Band n))(p:Bool)(h:∀ V,Grass.Hom p (A V))(hr:R.t=0):∀ V,Grass.Hom p (reels R u A V):=by
     intro V; induction u generalizing V with
     | nil=> exact h _
     | cons a u ih=> unfold reels; rw [paints R _ a hr]; obtain he:= ih (a.pullC su V); cases p <;> simp only [Grass.Hom,Plus,Minus, Bool.false_eq_true,↓reduceIte] at he ⊢ <;> rw [tilt_grade,he]; exact map_neg .. 

variable (T)
-- cells choose path, preserving zero (for exact local operands)
def tag (p v:T.Cell) : TapeWalk n T:=if v=p then [] else (connect p v).choose
lemma tag_spec (p v:T.Cell): finish T p (tag T p v)=v:=by by_cases h:v=p; subst v; simp [tag,finish]; rw [tag,if_neg h]; exact (connect p v).choose_spec
noncomputable def moved (p v:T.Cell):= reels R (pathT T (tag T p v)) A
lemma moved_at (p:T.Cell): moved T R A p p=A:=by simp [moved,tag,pathT,reels]
lemma along (p v:T.Cell) (hA:Parity A)(hR:R.t=0)(hΩ:T.kind= .link)(he : finish T p u=v): SignedEq (reels R (pathT T u) A) (moved T R A p v):=touring R A u hΩ hA hR p _ (he.trans (tag_spec T p v).symm)
-- accessor direct connection: floors, parity
structure SameTile (C:Tiling n)(x:C.Cell)(a:Insertion n F): Prop where
   floors : Floors (C.chamber x) a
   inv : Lat.Invariant a
   parity : Chess.Parity a
variable (C:Regulator n F)(hv:C.t=0)
include hu hv
-- assemble all link orientations in one family; order structures included
lemma stabilizes {I:Type*} (P:I→T.Cell)(x:I→ Insertion n F) (he:∀ i,SameTile T (P i) (x i)) : Chess.Pattern C T (fun i v => moved T C.zeroCut (x i) (P i) v):=by
    let A i:=moved T C.zeroCut (x i) (P i)
    constructor
    · intro i v; let g:= tag T (P i) v; have hh := reach_in C.zeroCut (x i) g (P i) (chamber T) (he i).floors; rw [show finish T (P i) g = v from tag_spec ..] at hh; exact hh -- args
    · intro i v; exact gauge_reel C.zeroCut (x i) _ (he i).inv
    · intro i v; obtain ⟨p,h⟩:= (he i).parity; exact ⟨p,reel_parity C.zeroCut (x i) _ _ h hv⟩
    intro p a i v; exact along T C.zeroCut (x i) ((p,a)::(tag T (P i) v)) (P i) (T.mate p a v) (he i).parity hv hu (by rw [finish,tag_spec])
-- order representation of lhs can simplify actual desired input at arbitrary occupied cells.
theorem assembled (x:T.Cell→Insertion n F)(h:∀ i,SameTile T i (x i))(hb:0≤ C.β)(hl:4≤ n.val):
    let Y:= fun i v=> moved T C.zeroCut (x i) i v; ‖C.raw ((Finset.univ.toList.map x).prod)‖≤∏ i:T.Cell, Chess.Array.root C (T:=T) Y i:=by
   intro Y; have hP:= Chess.Array.tiles id (stabilizes (I:=T.Cell) T hu C hv id x h) hu hb hl -- signature order?
   let W:=Chess.Array.use T Finset.univ.toList Y id; have he:W=(Finset.univ.toList.map x).prod:=by unfold W Chess.Array.use; congr 2; funext i; exact moved_at ..
   rw [← he]; exact hP
end YM.Massive.Romance
#print axioms YM.Massive.Romance.assembled
