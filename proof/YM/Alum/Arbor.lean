import YM.Alum.Wreath
import YM.Pods.Shifts
/- Rename a root tile; even link costs don't distinguish arbitrary orientations except
 actual sewn paths. Includes reconciliation with continuous parents for boot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open QCD.Cove Finset NormedSpace QCD.RP
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical ComplexOrder
namespace Goblet
variable {n c l d:Side}{F:ℕ}
open Chess Cells Romance Massive.Lyre.Array Plum
variable (g:Ratio c n)(he:Even c.val)(z: Site n)(p v: Site c)
-- Pure rooted transform via full inertia orientations.T.Ar same hierarchy.B.Statement.
variable (h:Odd g.count.val)
local notation "B'"=>mural g he z
local notation "T!"=> mural g he (z+g.embed p)
open YM.Intag
include he
lemma cuts_a (a:Axis): (B').bandCut (p+v) a=(T!).bandCut v a:=by
     refine Ladder.cut_eq _ _ rfl rfl (?_); change (B').starts (p+v) a=(T!).starts v a
     unfold Tiling.starts; change (fun i=> z i- _) a+g.root (p+v) a = (fun i=>(z+g.embed p) i-_) a+g.root v a; rw [map_add]; simp only [Pi.add_apply]; change z a-_+(g.root p a+g.root v a)= z a+g.root p a-_+_; abel
lemma mateV (a:Axis)(u:Site c): (B').mate (p+v) a (p+u) = p+ (show Site c from (T!).mate v a u):=by
    funext x; by_cases h:x=a; · subst x; simp; change (2*(p a+v a)-1-(p a+u a):Per c)=p a+(2*v a-1-u a); ring
    apply Eq.trans ((B').mate_off _ _ _ h); exact congr_arg (p x+·) ((T!).mate_off _ _ _ h|>.symm)
-- same proof.Work.Z at root interpolation.Even large ratio.Schedule.
include h in
lemma margV (x:Site n) (k:ℕ) : x ∈ (B').margin (p+v:Site c) k ↔ x ∈ (T!).margin v k:=by rw [key_margin _ _ _ _ _ h,key_margin _ _ _ _ _ h,show g.embed (p+v)=g.embed p+g.embed v from g.root.map_add _ _,add_assoc]
lemma repointed (P:Regulator n F)(x:Stud n F)(u: Site c)(hx:Potion x): topH (B') P x (p+u)=topH (T!) P x u:=by
    let f(v:Site c):=p+v; let K (u:Site c × Axis):=(f u.1,u.2); let L:= mural g he z; let W:= T!
    have hM(q:Site c): SignedEq (palmH L x (p+u) (f q)) (palmH W x u q):=by
           let U:= tag W u q
           have hv (l:TapeWalk n W): finish L (p+u) (l.map K)=f (finish W u l):=by induction l with| nil=>rfl| cons a t ih=> change L.mate _ _ _=f _; rw [ih]; exact mateV g he z p a.1 a.2 _
           have he : finish L (p+u) (U.map K)=f q:= (hv U).trans (by rw [show finish W u U=q from tag_spec ..]); apply ((bookR x L (p+u) (f q) _ hx rfl he).symm).trans
           have hh(t:TapeWalk n W):pathT L (t.map K)=pathT W t:=by induction t with| nil=>rfl| cons a l ih=> exact congr_arg₂ List.cons (cuts_a g ‹_› z p a.1 a.2) ih
           exact Or.inl (congr_arg (road · x) (hh U))
    let N:= Fintype.card (Site c); let V:Finset (Site c):=Finset.univ; let A:= V.toList
    have hp:List.Perm A (A.map f):=(List.perm_ext_iff_of_nodup V.nodup_toList (V.nodup_toList.map (fun _ _ h=> add_left_cancel h))).2 fun i=> iff_of_true (mem_toList.mpr (mem_univ _)) (List.mem_map.mpr ⟨i-p,mem_toList.mpr (mem_univ _),show p+(i-p)=i from (by abel)⟩)
    apply (pow_left_inj₀ (top_nn ..) (top_nn ..) (n:=N) W.cells_positive.ne').mp; change topH L _ _ _^Fintype.card L.Cell= topH W _ _ _^Fintype.card W.Cell; rw [top_power,top_power]; apply signsV
    apply (signed_rearr A (A.map f) hp (palmH L x (p+u)) (fun j=> potW _ x hx)).trans
    rw [List.map_map]; exact signsList A _ _ hM
-- arch reconciliation. Continuous operators always.P.Glacier.B price. applies to any Run authentic when P.t=0.
variable (P:Regulator n F) (T:Tiling n)(x:T.Cell)(X:Insertion n F)(hK:P.t=0)(hV:T.kind=.link)
local notation "Fv"=> floorL T P.average P
omit he
lemma knownV(V:Insertion n F):P.average V=valueH P V:=rfl
include hK
lemma sprouts : floorL T P.average P X x=topH T P X x:=by
       apply (pow_left_inj₀ (floor_nn ..) (top_nn ..) T.cells_positive.ne').1; rw[roof_power,top_power, knownV]; apply congr_arg (fun X : Stud n F=> ‖valueH P X‖)
       suffices h:∀ l:List T.Cell,(⇑((l.map (replicateR T P X x)).prod):Stud n F)=(l.map (palmH T X x)).prod from h _
       have hh(l:List (Band n)): ⇑(reels P.zeroCut l X)= road l X:=by
            induction l with|nil=> rfl|cons a l ih=>
                 change ⇑(QCD.RP.picture a P.zeroCut (reels P.zeroCut l X))= _; funext i
                 rw [paints _ _ _ (show P.zeroCut.t=0 from hK) i]; simp only[ih]; rw [road,huesT] -- possible inconsistent uses normF? tTape.Se
       intro l; induction l with| nil=>rfl| cons a l ih=> simp only [List.map_cons,List.prod_cons]; change ((⇑(replicateR T P X x a)): Stud n F)*_= _; exact congr_arg₂ (·*·) (hh _) ih
end Goblet
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.Goblet.sprouts
#print axioms YM.Massive.Lyre.Goblet.repointed
