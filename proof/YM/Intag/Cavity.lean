import YM.Intag.Summer
import YM.Intag.Films
/-!
# costs of all adaptive alignment options geometry
 local ε. floor widths from old/within tile.Sparks true-face. prior step seams unaffected. Kern q'=°.Rune.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory Finset RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open MassiveQCD.Cupola MassiveQCD.Sample
open scoped BigOperators Classical
namespace CardsT
open Column Massive.Patria.Rolls
variable (S:Scheme)(R:Side)(i k:ℕ){I:Type} [Fintype I]
variable (X:I→ Cover)
local notation "H" k:arg=> Hole I S i k
local notation "P" k:arg => wrap (S.side R k) ∘ (showX S i k X)
local notation "V"=> viewW S R
local notation "W"=> wrap (S.side R i) ∘ X
local notation "Mk" k:arg=> flex S i k
local notation "C!" k:arg=> ratioTo S k i
set_option quotPrecheck false
lemma door (t:H k)(h:i ≤ k): separation ((V h).embed ((W) t.1)) ((P k) t) ≤ flex S i k:=by
      dsimp only [Function.comp_apply]; rw [Ratio.embed_wrap,showX, map_add]; rw [add_comm (wrap _ _) (wrap _ t.2.val)]; exact Work.E08.separation_box_add _ t.2.property
-- NOTE scope.*choose Jcost before Tweet.
lemma peg (h:i≤k):flex S i k ≤ 100*ratioTo S k i:=Nat.mul_le_mul_left _ (Nat.sub_le _ _)
variable (M:ℕ)
lemma zone (h:i≤ k)(he:∀ x y,x≠y→ 202+M ≤ separation ((wrap (S.side R i)∘ X) x) ((wrap (S.side R i)∘ X) y))(t u: H k)(hp:t.1≠u.1): ratioTo S k i*(M+2) ≤ separation ((wrap (S.side R k) ∘ showX S i k X) t) ((wrap (S.side R k)∘ showX S i k X) u):=by
      let g:=viewW S R h; let L:= ratioTo S k i; let N(x:H k):= g.embed ((W) x.1)
      have hh : L*(202+M) ≤ separation (N t) (N u):=(Nat.mul_le_mul_left L (he _ _ hp)).trans_eq (both g ((W) t.1) ((W) u.1)).symm; rw [mul_add] at hh
      have hi: separation (N t) ((P k) t)≤100*L:= (door S R i k X t h|>.trans (peg S i k h))
      have hv: separation (N u) ((P k) u)≤100*L:= (door S R i k X u h|>.trans (peg S i k h))
      have hW:=separation_triangle (N t) ((P k) t) (N u); have hz:=separation_triangle ((P k) t) ((P k) u) (N u); rw [separation_comm ((P k) u) (N u)] at hz -- rew issue first
      change L * _ ≤ _; rw [mul_add]; omega
variable (hM:∀ x y: I,x≠ y→ 202+M ≤ separation ((wrap (S.side R i)∘ X) x) ((wrap (S.side R i)∘ X) y))(hx:201≤ (S.side R i).val)
include hM hx
lemma firesW (hi:i ≤ k): Injective (P k) :=by
      intro x y he; have hp:x.1=y.1:=by
           by_contra hv; have ht:=zone S R i k X M hi hM x y hv; rw [he, separation_self] at ht; have hh:0<ratioTo S k i * (M+2):=Nat.mul_pos (odd_to hi).pos (by omega); omega
      apply Prod.ext hp; apply Subtype.ext
      dsimp only [Function.comp_apply,showX] at he; rw [map_add,map_add,hp] at he
      refine wrap_injOn (S.side R k) ?_ ?_ (add_left_cancel he)
      all_goals intro a; have hfx := (box_test.mp x.2.property).1 a; have hfy:=(box_test.mp x.2.property).2 a; have hvx:=(box_test.mp y.2.property).1 a; have hvy:=(box_test.mp y.2.property).2 a; let g:= V hi; have ht:= Nat.mul_le_mul_right g.count.val hx; rw [← g.exact_size] at ht; change 201* ratioTo S k i ≤ _ at ht; have hz:= peg S i k hi; have hφ :0<ratioTo S k i:= (odd_to hi).pos; omega -- maybe projections shadow? 
lemma lightX (hi:i≤ k)(m:ℕ)(hp:1 ≤ m): Fires (wrap (S.side R k)∘ showX S i k X) m:=by
    let O:=(P k); have h:=firesW S R i k X M hM hx hi; intro j; exact ((card_le_one.mpr (fun x hx y hy=>h (((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm))): ((univ.filter fun p:H k=> O p=j)).card≤1).trans hp
omit hM hx in
private lemma ceilingPop {c f:Side}(R: Ratio c f){I:Type}[Fintype I](X:I→Site f)(hx:Injective X)(m:ℕ)(hp:R.count.val^4 ≤ m):Fires (R.parent∘X) m:=by
      intro i
      apply le_trans _ hp
      rw [← site_card R.count]; apply le_trans ?_ (card_univ ..).le; refine Finset.card_le_card_of_injOn (R.residue ∘ X) (fun i _=>mem_univ _) ?_; intro x h y hy he; apply hx; have hh:R.parent (X x)= R.parent (X y):=((mem_filter.mp h).2).trans ((mem_filter.mp hy).2).symm; rw [← R.unpack_at (X x), hh, show R.residue (X x)=R.residue (X y) from he, R.unpack_at]
lemma ancestors (hi:i ≤ k)(m:ℕ)(hp:(S.step k).L.val^4 ≤ m): Fires ((Flume.sliceL (S.step k) (S.sides_next R k)).parent ∘ (wrap (S.side R (k+1))∘ showX S i (k+1) X)) m:=ceilingPop _ _ (firesW S R i (k+1) X M hM hx (Nat.le_succ_of_le hi)) _ hp
omit hx
variable (b:ℕ)
lemma reserveX (hi:i ≤ k)(hp:b*b ≤ ratioTo S k i*M)(u v:H(k+1))(he:u.1≠v.1): b*b ≤ separation ((Flume.sliceL (S.step k) (S.sides_next R k)).parent ((P (k+1)) u)) ((Flume.sliceL (S.step k) (S.sides_next R k)).parent ((P (k+1)) v)) :=by
       let g:= Flume.sliceL (S.step k) (S.sides_next R k); apply Intag.Film.apert_ineq g ((S.step k).odd); apply le_trans _ (zone S R i (k+1) X M (Nat.le_succ_of_le hi) hM u v he)
       rw [chip S hi,mul_assoc]; refine Nat.mul_le_mul_left g.count.val ?_; rw [mul_add]; have hx:0 <ratioTo S k i:= (odd_to hi).pos; omega
lemma spaces (hi:i ≤ k)(hp:b*b ≤ ratioTo S k i*M) : (∀ T:Finset (H k), T∈stencil S i k→MassiveQCD.Cupola.Spaced (wrap (S.side R k)∘ showX S i k X) T b)∧∀ T:Finset (H(k+1)),T∈stencil S i (k+1)→ MassiveQCD.Cupola.Spaced ((Flume.sliceL (S.step k) (S.sides_next R k)).parent ∘ (wrap (S.side R (k+1))∘ showX S i (k+1) X)) T b:=by
    refine ⟨fun T h x hx y hy he=>?_,fun T h x hx y hy he=>?_⟩
    rotate_left -- uncertain `_`
    · exact reserveX S R i k X M hM b hi hp _ _ (fun h' => he ((h:Set.InjOn _ _) hx hy h'))
    exact hp.trans ((Nat.mul_le_mul_left (ratioTo S k i) (Nat.le_add_right M 2)).trans (zone _ _ _ _ X _ hi hM _ _ fun h' => he ((h:Set.InjOn _ _) hx hy h')))
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.spaces
#print axioms YM.Intag.CardsT.lightX
#print axioms YM.Intag.CardsT.ancestors
