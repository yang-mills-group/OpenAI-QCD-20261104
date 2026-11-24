import YM.Bwana.Mono
import YM.Alum.Arbor
import YM.Intag.Column
/- true duplicate coordinates.Multi-body orientation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Shelv
open Function Filter Set QCD QCD.Lat QCD.Tide QCD.Revolve QCD.RP QCD.Grass Lattice Wilson Matrix
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Depth.Off Massive.Romance Massive.Chess
open YM.Next.Rank.Station Cells
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {S:Scheme}(R:Side){i j k n q N:ℕ} (hp:Even (S.side R j).val) (v: Site (S.side R k))(x: Cover) (hj:j≤ k) (hk:k≤ i)
local notation "Sn"=> S.side R
set_option quotPrecheck false
local notation "TL" h:arg=> Column.sky S R j _ h hp v
local notation "T₁"=> mural (viewW S R hj) hp v
local notation "TZ"=> Column.sky S R j i (hj.trans hk) hp v
local notation "I₀"=> Site (S.side R j)
local notation "V1"=> viewW S R hk
include hj hk
lemma frames : Column.sky S R j i (hj.trans hk) hp v =mural (viewW S R (hj.trans hk)) hp ((viewW S R hk).embed v):=by unfold Column.sky Column.pillar; rw [dif_pos hk]
-- Avoid subst tiling. Use explicit `T:T₀=v shelf`. TL and T₁ have same Cell defin but rewriting problematic. use refl proof when unfolding.
lemma tours (x : Site (S.side R k))(p:I₀): (TZ).copyMap p ((viewW S R hk).embed x)=(viewW S R hk).embed ((T₁).copyMap p x):=by
     unfold Column.sky Column.pillar; rw [dif_pos hk]; exact maps_step _ _ _ _ _ hp (viewOdd ..) (viewOdd ..) x
include hp -- hp implicit from statement
lemma ballad (p:I₀)(a:Axis)(x:Site (S.side R k)): ((TZ).bandCut p a).reflect ((V1).embed x)=(V1).embed (((T₁).bandCut p a).reflect x):=by
     let L:=T₁; let Y : Site (Sn i):= (V1).embed x
     obtain ⟨w,hw⟩:= L.pointed (0:(T₁).Cell) x; rw [← hw,← tours R hp v hj hk,← Tiling.after,← Tiling.after,tours R hp v hj hk]; rfl -- omega?
-- expand slide proof.AP signs require lattice minimal.Set.
lemma slide (p:I₀)(a:Axis): ((TZ).bandCut p a).slide=wrap _ (ratioTo S i k • Lattice.lift (((T₁).bandCut p a).slide)) :=by
     let Y:=T₁; let V:= TZ; let g:= viewW S R hk; have hZ : g.embed 0=0:=g.root.map_zero
     have hg:= ballad R hp v hj hk p a 0; rw [hZ] at hg; simp only [Cells.Cut.reflect, affine, Signed.act_zero,zero_add] at hg; exact hg
omit hk
local notation "Wz"=> TapeWalk (Sn k) T₁
-- cover at k, slide accumulated signed path at THIS k. Acts with all translations exact vector.
def layX : TapeWalk (Sn k) T₁→ Cover
 | []=>0
 | (p,a)::l=> (Signed.mirror a).act (layX l)+Lattice.lift (((T₁).bandCut p a).slide)
variable (w:TapeWalk (S.side R k) (mural (viewW S R hj) hp v))(t:Site (S.side R j))
-- translated mirror on infinite cover with common translation ratio_t.Facts keeps match.
noncomputable def arks (b:ℕ→ Cover): ℕ→ Cover:= lineC S (sawC b (axes (pathT T₁ w))) k (layX R hp v hj w)
local notation "W" x:arg=> arks R hp v hj w x
include hk hp
lemma finishK : finish TZ t w = finish T₁ t w:=by
     induction w with
     | nil=>rfl
     | cons a l ih=> rcases a with ⟨p,u⟩; change (TZ).mate p u (finish TZ _ l)= (T₁).mate p u (finish T₁ _ l); rw [ih]; rfl -- parser precedence
lemma canvasK (b:ℕ→ Cover)(k':ℕ)(h: wrap (Sn i) (b i)∈ (TZ).margin t k') : wrap (Sn i) ((W b) i)∈ (TZ).margin (finish T₁ t w) k':=by
     induction w with
     | nil=>
        rw [finish]; rw [show arks R hp v hj [] b i=b i from ?_]; exact h; unfold arks lineC axes pathT layX; simp [sawC]
     | cons a l ih=>
        rcases a with ⟨p,a⟩
        have ht : wrap (Sn i) (arks R hp v hj ((p,a)::l) b i)=((TZ).bandCut p a).reflect (wrap (Sn i) (arks R hp v hj l b i)):=by
           rw [show arks R hp v hj ((p,a)::l) b i=(Signed.mirror a).act (arks R hp v hj l b i)+ratioTo S i k • Lattice.lift (((T₁).bandCut p a).slide) from ?_,map_add, ←wrap_signed,Cut.reflect,affine,slide R hp v hj hk]; swap
           unfold arks lineC; change (Signed.mirror a).act _ +ratioTo S i k • ((Signed.mirror a).act _+_) = _; rw [Signed.act_add,act_times, smul_add,← add_assoc]; -- or rfl
           rfl
        rw [ht]; exact margins TZ k' p _ a ih -- `t:=finish`
omit hp hk hj
-- math fold if no inclusion. fix below
end YM.Intag.Shelv
#print axioms YM.Intag.Shelv.finishK
#print axioms YM.Intag.Shelv.canvasK
#print axioms YM.Intag.Shelv.slide
