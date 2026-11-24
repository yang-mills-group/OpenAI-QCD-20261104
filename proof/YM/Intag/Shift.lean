import YM.Intag.Vane
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Romance QCD QCD.Tide
open scoped BigOperators Classical
variable {c C f F:Side}(g:Ratio c f)(x y:Site f)(p:Site c)(he:Even c.val)(hp:Odd g.count.val)
include he hp
namespace Vent
lemma resp (z:Site f){n:ℕ}{y:Site f}{P:Site c}(h : z∈ (mural g he x).margin P n)(hx : y=z+g.embed p): y∈ (mural g he x).margin (P+p :Site c) n:=by
    subst y
    rw [key_margin _ _ _ _ _ hp] at h ⊢; rwa [show g.embed (P+p)=g.embed P+g.embed p from g.root.map_add _ _,← add_assoc,separation_translate]
-- any B TILING with given shifts. full replicas T stride s U. choose z letting margin simultaneously.Un.Move coherent palettes.All typeA stencil points.Even.h.Path. high-level reconstruct Lifts.S.
omit hp
variable {I : Type*}[Fintype I]
lemma balm (Y:I→Site f)(k:ℕ)(hk:0<k)(h:Fintype.card I*(2*k)<g.count.val): ∃ z:Site f, ∀ i,∃ j:Site c,Y i ∈(mural g he z).margin j k:=by
    let v:=Fintype.equivFin I; let T:= mural g he (0:Site f)
    obtain ⟨z,hz⟩:= T.fits_together (Y ∘ v.symm) k hk h
    let x:Site f:= fun i=> z i+((g.count.val/2:ℕ):Per f); let B:=mural g he x
    have hB:T.newly z = B :=by unfold Tiling.newly T B mural; congr 1; funext i; dsimp only [x]; rw [add_sub_cancel_right]
    refine ⟨x,fun i=>?_⟩
    let p:= (T.newly z).which (Y i); have hc : Y i∈ (T.newly z).margin p k:=by have hh:=hz (v i); rw [comp_apply,v.symm_apply_apply] at hh; exact hh
    suffices h: ∀ U:Tiling f,U=T.newly z→ ∃ j:U.Cell, Y i∈ U.margin j k by exact h B hB.symm
    rintro U rfl; exact ⟨p,hc⟩ -- likely subst wrong
-- A>B ; choose B-test center to fit all A copies.Within each such B cell optionally.
variable (gA:Ratio C f)(rA:Ratio C c)(hw:Even C.val)(hr:Odd gA.count.val)
local notation "H"=>mural gA hw x
-- cost constant use Fintype Signed need instance. for ANY replicated note letters across orientation.Power Budget.
include he hw hr hp rA
lemma briny (Y:I→Site f)(k:ℕ)(hk:0<k)(ht:Fintype.card (Signed × I)*(2*k)<g.count.val):∃ z:Site f,∀ i,∀ j:Site C,∃ p:Site c, (mural gA hw x).copyMap j (Y i)∈ (mural g he z).margin p k:=by
   let R (i:Signed × I):= i.1.act (Y i.2-x)+ x; obtain ⟨z,h⟩:=balm g he R k hk ht; refine ⟨z,fun i j=>?_⟩
   obtain ⟨p,hpV⟩ := h ((H).omega j,i); exact ⟨p+rA.embed j,resp g z (rA.embed j) he hp _ hpV (by rw [swath _ _ _ hw hr,embed_comp rA g, ← add_assoc])⟩
-- UNIQUE index.V assign; costs when positions farther than one cell.More mechanism conditional.
omit rA
lemma ticket (Y:I→Site f)(hY:∀ i j:I,i≠ j→ g.count.val< separation (Y i) (Y j))(k:ℕ)(hx:∀ i,Y i∈ (mural gA hw x).margin (0:Site C) k)(hv:g.count.val ≤2*k) (z:Site f)(p:Site C × I→Site c)(hB:∀ i:Site C × I,(mural gA hw x).copyMap i.1 (Y i.2) ∈ (mural g he z).chamber (p i)): Injective p:=by
   intro i j hei
   have he':separation ((H).copyMap i.1 (Y i.2)) ((H).copyMap j.1 (Y j.2))≤g.count.val:= (mural g he z).extent (hei ▸ hB i) (hB j)
   by_contra hn
   by_cases hv':i.1=j.1; · have hp:= hY _ _ (show i.2≠j.2 from fun h=> hn (Prod.ext hv' h)); rw [hv',Tiling.copyMap,Tiling.copyMap,affine,affine,separation_translate,separation_signed] at he'; exact not_le_of_gt hp he'
   have hp'(j:Site C × I): (H).copyMap j.1 (Y j.2) ∈ (mural gA hw x).margin j.1 k:= ((H).reflected_margin _ _ _).1 (hx _); exact not_le.mpr ((show g.count.val <_ from hv.trans_lt (by simpa only [two_mul] using (crimp gA x i.1 hw hr (hp' i) (hp' j) hv')))) he'
end Vent
end YM.Intag
#print axioms YM.Intag.Vent.briny
#print axioms YM.Intag.Vent.ticket
