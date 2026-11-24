import YM.Intag.Column
import YM.Oars.Deduct
import YM.TIPS.Fall
/-!
# exact simultaneous option array at all finer steps
 include true-pay startup for posterior columns.B footprints of shifts under any Averaging family. Allow options with zero weight / no parent. Slot positions are true covariant translated lifts. charging.
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
open Column
variable (S:Scheme)(R:Side)(i k:ℕ){I:Type} [Fintype I]
-- posterior capacity deterministic paid.Slot offsets allowed. near.S.
noncomputable def flex (S:Scheme)(i k:ℕ):ℕ:=100*(ratioTo S k i-1)
noncomputable abbrev Hole (I:Type)(S:Scheme)(i k:ℕ):= I ×↥(box (flex S i k))
variable (X:I→ Cover)
local notation "U" m:arg=> Hole I S i m
local notation "Zp" m:arg=> ratioTo S m i
local notation "N" m:arg=> flex S i m
set_option quotPrecheck false
local notation "L"=> (S.step k).L
noncomputable abbrev showX (X:I→ Cover)(u:Hole I S i k) : Cover := ratioTo S k i • X u.1 +u.2.val
lemma gap (hk:i≤k): (S.step k).L.val * flex S i k+28*(2*(S.step k).L.val) ≤ flex S i (k+1):=by
      have hp: (S.step k).L.val ≥3:= (S.step k).coarse; have ht:0 < Zp k := (odd_to hk).pos
      let s:= (S.step k).L.val; let r:= Zp k; unfold flex; rw [chip S hk]; change s*(100*(r-1))+_ ≤ 100*(s *r-1)
      have hv:s*(100*(r-1)) +100*s=100*(s*r):=by
           have he:s*(r-1)+s=s*r:= by rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1≤ r from ht)]
           nlinarith only [he] -- edit
      omega
-- proof gap robust.timeout. Book.A.Rule matching.Man. Show Laurent sizes attach.C.
local notation "Φ" k:arg=>showX S i k X
noncomputable def link (t:U (k+1))(u:U k):Prop:= t.1=u.1 ∧ Laurent.size (showX S i (k+1) X t-(S.step k).L.val • showX S i k X u) ≤ 28*(2*(S.step k).L.val)
open Laurent Finset YM.Massive.Patria.Rolls Planned.PrimaryIntegral295
lemma fitsB (x:Cover)(r:ℕ)(h:Laurent.size x≤r): x∈ box r:=by
   rw [box_test]; have ht(i:Axis):(x i).natAbs ≤ Laurent.size x:=by unfold Laurent.size; exact single_le_sum (f:=fun i':Axis=>(x i').natAbs) (s:=univ) (fun _ _=>Nat.zero_le _) (mem_univ i)
   constructor <;> (intro i; specialize ht i; omega)
lemma addsBox (x y: Cover)(z t:ℕ)(hp:x∈box z)(hv:y∈box t): ((S.step k).L.val • x + y)∈ box ((S.step k).L.val*z+t):=by
   rw [box_test]; obtain ⟨h0,h1⟩:= box_test.mp hp; obtain ⟨h2,h3⟩:= box_test.mp hv; constructor <;> intro i <;> simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply,nsmul_eq_mul, Nat.cast_add,Nat.cast_mul]
   · nlinarith only [h2 i,mul_le_mul_of_nonneg_left (h0 i) (Int.natCast_nonneg (S.step k).L.val)]
   linarith only [h3 i,mul_le_mul_of_nonneg_left (h1 i) (Int.natCast_nonneg (S.step k).L.val)]
lemma touch (u:U k)(x:Cover)(hp:i≤k)(hx: Laurent.size x≤28*(2*(S.step k).L.val)): ∃ t:U (k+1),link S i k X t u ∧ showX S i (k+1) X t = (S.step k).L.val • (showX S i k X u)+x:=by
    let z:= u.2.val; let w:= (S.step k).L.val • z+x; have hw:w∈ box (flex S i (k+1)):=box_larger (addsBox S k z x (flex S i k) _ u.2.property (fitsB x _ hx)) (gap S i k hp); let t:U (k+1):=⟨u.1, w,hw⟩; have ht:showX S i (k+1) X t=(S.step k).L.val • showX S i k X u+x:=by unfold showX; rw [chip S hp,mul_smul,smul_add, add_assoc]
    exact ⟨t,⟨rfl,by rw [ht,add_sub_cancel_left]; exact hx⟩,ht⟩
-- Steps stable budget 60.O.Message.Purchase script uses actual Karrier by same Side.
lemma ages (u:U k)(t:U (k+1))(h:link S i k X t u): separation ((Flume.sliceL (S.step k) (S.sides_next R k)).parent (wrap _ (showX S i (k+1) X t))) (wrap (S.side R k) (showX S i k X u)) ≤ 60 ∧ size (Carrier.cellar L (showX S i (k+1) X t) - showX S i k X u) ≤ 60:=by
      let a:=showX S i k X u; let b:=showX S i (k+1) X t; let x:=b-(S.step k).L.val • a; have hx: Laurent.size x≤28*(2*(S.step k).L.val):=h.2; have hK:b=(S.step k).L.val • a+x:=by unfold x; abel -- use abel
      have hw:= tread L x a hx; rw [← hK] at hw; refine ⟨?_,hw⟩
      let s:=Flume.sliceL (S.step k) (S.sides_next R k); rw [Planned.PrimaryIntegral295.Streets.owner]; exact (Massive.Poised.Chute.cost_p ..).trans hw

noncomputable def stencil : Set (Finset (Hole I S i k)) := {s | Set.InjOn (Prod.fst) (s:Set (Hole I S i k))}
variable (q:I→Bool)
local notation "κ" k:arg=> stencil (I:=I) S i k
-- Holds even when duplicated center alternatives. independence polygon.C addresses authentically each.option. D includes singletons & empty.
lemma pledges : MassiveQCD.Sample.Pledge ((q∘Prod.fst): Hole I S i (k+1)→Bool) ((q∘Prod.fst): Hole I S i k→ Bool) (link S i k X) (stencil S i k) (stencil S i (k+1)):=by
      let T:=link S i k X; have hh:Hyp T (κ k):=by
             refine ⟨by simp [stencil],?_,fun s i j l ht hk hx h e=> (ht: Set.InjOn _ _) hk hx (h.1.symm.trans e.1)⟩
             exact fun i j hV ht=> (show Set.InjOn _ _ from hV).mono (Finset.coe_subset.mpr ht)
      refine ⟨hh,fun i j h=> congr_arg q h.1,?_⟩
      intro s u h; intro x hx y hy he
      let S':=findV T u
      obtain ⟨z,hz⟩:= Option.ne_none_iff_exists'.1 (h.2.1.2 _ hx); obtain ⟨t,ht⟩:= Option.ne_none_iff_exists'.1 (h.2.1.2 _ hy)
      have hp:= (findG T hh _ _ h.1).1 hz; have hv:= (findG T hh _ _ h.1).1 ht; refine h.2.1.1 hx hy ?_
      change S' x=S' y; change S' x=_ at hz; change S' y=_ at ht; rw [hz,ht, (h.1:Set.InjOn _ _) hp.1 hv.1 (hp.2.1.symm.trans (he.trans hv.2.1))]
@[simp] lemma oneSt (u:U k):{u}∈stencil S i k:=by simp [stencil]
lemma univSt : (Finset.univ:Finset (Hole I S i i))∈ stencil S i i:=by
       rintro x hx y hy he; refine Prod.ext he (Subtype.ext ?_); have hp (t:U i) : t.2.val=0:=by
            have ht:t.2.val∈Lattice.box (flex S i i):= t.2.property; obtain ⟨h,h'⟩:= box_test.mp ht; ext a; change t.2.val a=0; have hx:=h a; have hv:=h' a; have hC : flex S i i=0:=by simp [flex]
            omega
       rw [hp x,hp y]
lemma through (u:U i) : showX S i i X u=X u.1:=by
     let v:U i:=⟨u.1,0,Lattice.center_box _⟩ -- center_box namespace?
     have he: u=v:= (univSt S i (I:=I):Set.InjOn _ _) (mem_univ _) (mem_univ _) rfl; rw [showX, he, Column.home_c]; simp [v]
lemma population : Fintype.card (Hole I S i i)=Fintype.card I:=by
     let v: U i→I:= Prod.fst; have hv: Function.Bijective v:=⟨fun x y h=> (univSt S i (I:=I):Set.InjOn _ _) (mem_univ _) (mem_univ _) h,fun x=> ⟨(x,⟨0,Lattice.center_box _⟩),rfl⟩⟩; exact Fintype.card_congr (Equiv.ofBijective v hv)
-- count per option. names via offsets; no ambiguity at seam.
noncomputable def cardOpt (P:Side):= (box (28*(2*P.val))).card
lemma opts_foot (t:U (k+1)): (opts (link S i k X) t).card ≤ cardOpt (S.step k).L:=by
     let f(u:U k):= showX S i (k+1) X t - (S.step k).L.val • showX S i k X u
     apply Finset.card_le_card_of_injOn f (fun j hi=> fitsB _ _ ((mem_filter.mp hi).2 : link S i k X t j).2)
     intro u hu v hv h; have hU:link S i k X t u:= (mem_filter.mp hu).2; have hV:link S i k X t v:=(mem_filter.mp hv).2
     have hh:u.1=v.1:= hU.1.symm.trans hV.1; unfold f at h; have hA:= nsmul_right_injective (S.step k).L.pos.ne' (sub_right_injective h); unfold showX at hA; rw [hh] at hA; exact Prod.ext hh (Subtype.ext (add_left_cancel hA)) -- sub_left?
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.opts_foot
#print axioms YM.Intag.CardsT.ages
#print axioms YM.Intag.CardsT.pledges
#print axioms YM.Intag.CardsT.population
#print axioms YM.Intag.CardsT.through
#print axioms YM.Intag.CardsT.touch
