import YM.Pods.Walls
import YM.Pods.Shingle
import YM.Next.RANK.Coordinates
/-! # Tiling pure geometry
 Keep every period/chamber authentic incl arbitrary offsets and intermediate ancestors.
 All ratios in layouts are odd-sided, from actual vertex purchases later.
-/
-- edit trailing
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter MeasureTheory
open Lattice Wilson Cells
open Massive Massive.Romance
open scoped BigOperators Classical
variable {c f l:Side}(g:Ratio c f)(x y:Site f)(p:Site c)(he:Even c.val)(hp:Odd g.count.val)
local notation "T" => mural g he x
local notation "b"=> ((g.count.val/2):ℕ)
include he hp
lemma no_step (v:Site f) : (mural g he x).copyMap 0 v=v:=by
   have h:(T).omega 0=1:=by
      apply Signed.ext; · rfl
      ext i; simp only [Tiling.omega]; simp
   have hh : (T).translateBy 0=0:=by
       have hh:(mural g he x).copyMap 0 x=x+g.embed 0:= tuned g he hp x (0:Site c) -- syntax
       rw [Tiling.copyMap,affine,h,show g.embed 0=0 from g.root.map_zero] at hh; simpa using hh
   rw [Tiling.copyMap,affine,h,hh]; simp
lemma behind (i:Axis): (mural g he x).starts p i +((b:ℕ):Per f)= (x+g.embed p) i:=by
   unfold Tiling.starts; change x i-_+_+_= _; abel; rfl
lemma shorter (i:Axis)(h:y∈ (mural g he x).chamber p):(Lattice.lift (y-(x+g.embed p)) i)=(↑((mural g he x).coordinated p y i):ℤ)-b:=by
    let z(j:Axis):=(↑((mural g he x).coordinated p y j):ℤ)-b
    suffices h:Lattice.lift (y-(x+g.embed p))=z from congr_fun h i
    apply lift_eq_iff.mpr; refine ⟨?_,?_⟩
    · funext i; change y i - (x+g.embed p) i = (z i:Per f); rw[← behind g x p he hp i]; unfold z; simp only [Int.cast_sub,Int.cast_natCast]; rw [← sub_sub]; simp [Tiling.coordinated, Per]
    intro i; have hh:=(mural g he x).small h i; have hu:=(mural g he x).narrow; change (mural g he x).coordinated p y i<g.count.val at hh; change g.count.val< _ at hu; unfold z; obtain ⟨w,hw⟩:=hp; omega
lemma key_margin (k:ℕ): y ∈ (mural g he x).margin p k ↔ separation y (x+g.embed p)+k ≤ b:=by
    constructor
    · rintro ⟨hy,h⟩
      have hk (i:Axis): (Lattice.lift (y-(x+g.embed p)) i).natAbs+k≤b:=by rw [shorter _ _ _ _ _ hp i hy]; have hc:= h i; change k ≤ _ ∧ (mural g he x).coordinated p y i+k+1 ≤g.count.val at hc; obtain ⟨w,hw⟩:=hp; omega
      have h': separation y (x+g.embed p) ≤ b-k:=by unfold separation pdist; apply Finset.sup_le; intro i _; have hx := hk i; omega
      have hx:= hk 0; omega
    intro h
    have hx(i:Axis): k ≤ (mural g he x).coordinated p y i ∧ (mural g he x).coordinated p y i+k+1 ≤ g.count.val:=by
        let d:=Lattice.lift (y-(x+g.embed p)) i
        let u:ℤ:= d + (b:ℤ)
        have hv:d.natAbs ≤separation y (x+g.embed p):= component_le _ _
        obtain ⟨w,hw⟩:=hp
        have ht:0 ≤u:=by dsimp only [u]; omega
        have hge:u.toNat+k+1 ≤ g.count.val:=by dsimp only [u]; omega
        have hl:k ≤ u.toNat:=by dsimp only [u]; omega
        have hk:(mural g he x).coordinated p y i=u.toNat:=by
            unfold Tiling.coordinated; rw [show y i- _ = ((u.toNat:ℕ):Per f) from ?_,ZMod.val_natCast_of_lt (lt_trans (show u.toNat<g.count.val by omega) (mural g ‹Even c.val› x|>.narrow))]
            rw [← Int.cast_natCast,Int.toNat_of_nonneg ht]; unfold u; simp only [Int.cast_add,Int.cast_natCast]
            rw [show (d:Per f)=y i- (x+g.embed p) i from congr_fun (wrap_lift _) i,← behind g x p ‹Even c.val› ⟨w,hw⟩ i]; abel
        rw [hk]; exact ⟨hl,hge⟩
    refine ⟨fun i=>?_,fun i=>hx i⟩; change (mural g he x).coordinated _ _ i < g.count.val; have hp:=hx i; omega
lemma crimp {k s:ℕ}{p':Site c}{y y':Site f}(h:y∈ (mural g he x).margin p k)(hq:y' ∈ (mural g he x).margin p' s)(hx:p≠p'): k+s< separation y y':=by
    let v:=x+g.embed p; let w:= x+g.embed p'; have hC:g.count.val≤separation v w:=by
         unfold v w; rw [add_comm x,add_comm x,separation_translate,YM.Next.Rank.Station.both]; exact Nat.le_mul_of_pos_right _ (YM.Next.Rank.Station.separation_pos _ _ hx)
    have ht:separation y v+k≤ b:=(key_margin _ _ _ _ _ hp _|>.mp h) -- hp explicit
    have hs:separation y' w+s ≤ b:=(key_margin _ _ _ _ _ hp _|>.mp hq)
    have hv:=separation_triangle v y w; have hw:= separation_triangle y y' w; rw [separation_comm v y] at hv; obtain ⟨z,hz⟩:=hp; omega
lemma padding {k h₁:ℕ}(h:y∈ (mural g he x).margin p k)(hk:h₁ ≤k):y∈ (mural g he x).margin p h₁:=by
  rw [key_margin _ _ _ _ _ hp] at h ⊢; omega

end YM.Intag
#print axioms YM.Intag.crimp
#print axioms YM.Intag.no_step
