import YM.Clays.Gale
import YM.Clays.Norian
import YM.TIPS.Splice
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ η ξ m:ℝ}
variable (p:I → Cover) (F: Reel c 6 I D) {U:BudgetPoint}{L E':Type}
local notation "o"=> wrap c ∘ p
local notation "q"=> traceI I
variable (f:D→Site c)(g:D→ℝ)
local notation "Ψ"=> Ribbon.burst (traceI I)
open ConnectedActivityE6 Blaze King Reserves
open Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.Poised.Counting Massive.Poised.Counting.Click
open scoped YM.Massive.Poised.Plans.Stamp
open LoomT Stags Massive.Poised.Pipes
variable (X:Massive.SourceRead.TaperHol){U' : YM.Source.Hol su}(B:Massive.Lining.Temper.Collage.Exhibit U')
variable (Dx nL r d:ℕ)
open Card Iris Puff
variable (H:I→ Massive.UV.Label d) {D' I' : I → Type} (k:∀ i:I,CentreFrame (c:=c) U t (H i) (traceI I i) B (p i) (r+1) (D' i) Empty) (G : Reel c 6 I E')
lemma weight_given (hv: (1:ℝ) ≤ v)(j:I)(W:CentreFrame (c:=c) U t (H j) (traceI I j) B (p j) (r+1) L Empty) (he: Published W X Dx nL a v x 0)(hθ:θ≤ a) : Published W X Dx nL θ v x 0:=by
    obtain ⟨A,A',hx,ht,hd⟩:=he; obtain ⟨f,hf,hF⟩:=A'; refine ⟨A,⟨f,hf,QCD.Shells.Warmlet.fresh _ _ hF hθ (fun i=>(hf i).sight.travels)⟩,hx,?_,hd⟩; obtain ⟨u,hu,hU⟩:=ht.price; exact ⟨u,hu,fun _=> budget_finite (fun i=> i.elim) (by simp)⟩
lemma unionR (v:Grid c)(hm: Summable fun i=>F.mist U.threshold i v)(he: Summable fun i=> G.mist U.threshold i v): Summable (fun i=> Reel.mist (addReel 6 F G) U.threshold i v) ∧ Reel.rope (addReel 6 F G) U.threshold v=F.rope U.threshold v+G.rope U.threshold v:=by
    have h :HasSum (fun i=> Reel.mist (addReel 6 F G) U.threshold i v) (F.rope U.threshold v+G.rope U.threshold v):= hm.hasSum.sum he.hasSum; exact ⟨h.summable,h.tsum_eq⟩
lemma truncated (he: F.Occupant (wrap c ∘ p) q t U 2 a x (fun _=>1)): (survived F).Occupant (wrap c ∘ p) q t U 2 a x (fun _=>1):=by
    obtain ⟨f,hf,hV⟩:=he.reserve; exact ⟨true_multi _ _ _ he.booked,f ∘ Subtype.val,fun i=> budget_pull (fun x: LargeE F=>x.val) Subtype.val_injective (hf i),fun i=> hV i.val⟩ -- arity inspect
-- shrink spend by exp Δ for nonempty.Stone.
lemma orb (he: F.Occupant (wrap c ∘ p) q t U 2 a x (fun _=>1))(hb:w≤a): F.Occupant (wrap c ∘ p) q t U 2 w (Real.exp (w-a)*x) (fun _=>1):=by
    obtain ⟨f,hf,hV⟩:=he.reserve; refine ⟨he.booked,f,fun i=>?_,hV⟩; refine budget_mono (budget_scale (Real.exp_nonneg _) (hf i)) (fun j=>?_) (fun j=>?_)
    · split; next h=> exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=>abs_nonneg _) (hV j _ (he.booked.stays j).choose_spec).travels) (Real.exp_nonneg _)
      exact le_rfl
    split; next ht=>
          let A:ℝ:= coverNumber U.B (F.addr j).support; have hF':1≤ A:= by
              obtain ⟨G,hG,hq⟩:= Lattice.coverNumber_realized U.B (F.addr j).support; have hv:G.Nonempty :=by obtain ⟨x,hx,hz⟩:=halo_spec.mp (hG.1 ht); exact ⟨x,hx⟩
              unfold A; exact_mod_cast (hq ▸ (by have he:=Finset.card_pos.mpr hv; omega : 1 ≤ G.card) : 1 ≤ coverNumber U.B (F.addr j).support) -- temp
          simp only [abs_one,prod_const_one,one_mul]; rw [mul_left_comm, ←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hV j _ (he.booked.stays j).choose_spec).travels; exact Real.exp_monotone (by change w*A ≤ w-a+a*A; nlinarith only [hF',hb])
    next ht=> rw [mul_zero]
variable (V:I→ℝ) (hx:∀ i, Published (k i) X Dx nL a v (V i) 0) (hq:Pilot X B d U.order U.power Dx nL r C θ) (hp:30*(r+1)≤ c.val) (ha:0≤a)(ht:1 ≤ t)
local notation "A!"=> Gel.May.Roles q B p U d H r k F
variable (b': I→Massive.UV.Label d)(u':I→ℝ)(S:∀ i:I,CentreFrame (c:=c) U t (b' i) (traceI I i) B (p i) (r+1) (I' i) Empty)(hr:∀ i,Published (S i) X Dx nL a v (u' i) 0)
include hq hp ha ht hx hr
lemma ties (u:Grid c)(hm: Summable fun i=>F.mist U.threshold i u)(he: Summable fun i=>G.mist U.threshold i u):
   Reel.rope (Gel.May.Roles q B p U d (H+b') r (fun i=> simple (k i) (S i)) (addReel 6 F G)) U.threshold u=(A!).rope U.threshold u+ (Gel.May.Roles q B p U d b' r S G).rope U.threshold u:=by
    let X₁:=addReel 6 F G
    have hT(i:I): Published (simple (k i) (S i)) X Dx nL a v ((V+u') i) 0:= warn _ _ (hx i) (hr i); rw [Gel.May.ledgers q X B p U _ _ _ Dx nL hq _ _ hT ht hp _ u (unionR F G u hm he).1 ha,(unionR F G u hm he).2,Gel.May.ledgers q X B p U _ _ _ Dx nL hq _ _ hx ht hp _ u hm ha,Gel.May.ledgers q X B p U _ _ _ Dx nL hq _ _ hr ht hp _ u he ha,add_add_add_comm,←sum_add_distrib]; refine congr_arg _ (sum_congr rfl fun i hi=>?_); -- local arrays ritual
    rw [ProfileL.burstStirs 6 q u _ _ (Taxing.tapFrame X B _ _ _ _ _ _ (hT i) u hq hp ht ha),ProfileL.burstStirs 6 q u _ _ (Taxing.tapFrame X B _ _ _ _ _ _ (hx i) u hq hp ht ha),ProfileL.burstStirs 6 q u _ _ (Taxing.tapFrame X B _ _ _ _ _ _ (hr i) u hq hp ht ha), Stamp.ride _ _ (hX:=hx i) (hY:=hr i) u hq rfl rfl hp ht ha,map_add]
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.ties
#print axioms YM.MassiveQCD.Sample.Basal.orb
