import YM.MassiveQCD.Relight.Whirl
import YM.MassiveQCD.Relight.Coherent
/-! # Winding projector compensation at each slope and all higher degrees of illumination
    No reordering or interlacing at radius except conditional inner gauge TOT budgets to be
    purchased for the census. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival Shells Shells.Warmlet Finch Stem Grove Calm
variable (E:Gem c N I)(v:I→ℕ)
-- ensure all real-axis integral terms included; no from Gauge transform assumptions on values. caller must purchase Radius & Phase.
structure Ghoul (b:Bool):Prop where
   alive: RotationE E v
   first i: b=true → v i=1
   high i: b=false →2≤v i
noncomputable def vern (E:Gem c N I)(r:ℕ→ℂ)(v:I→ℕ):ℂ:=∑' i,r (v i) * (gemTone E i)
set_option quotPrecheck false
variable (b:Bool)
local notation "H"=> refund E b p.threshold
local notation "V"=> shadowE E b
lemma virtue (h:Ghoul E v b)(hP:E.Gather): RotationE V v ∧ Yank H v:=by
   obtain ⟨hx,hT⟩:=h.alive; have hf := refundWire E b p.threshold hx; refine ⟨⟨shutter E b hx,fun s k g hk=>?_⟩,⟨⟨hf.1, hf.2.2,hf.2.1⟩, fun s k g hk=>?_⟩⟩
   · obtain ⟨e,hE⟩:= hT s k g hk; exact ⟨e,fun i=> ⟨(hE i).1,(hE i).2.1,fun u=> rank_ray E b s g k e i (hE i).2.1 ((hE i).2.2) hx hk (hP.role ..) u⟩⟩
   obtain ⟨e,hE⟩:= hT s k g hk; exact ⟨e,(fun i=>congr_arg RegularAddress.support (hE i).2.1), (fun i=>(hE i).1), fun i u=> voyager E b i s k g e (hE i).2.1 ((hE i).2.2) hx hk (hP.role ..) u⟩ -- param order
noncomputable def labelled (z:ℕ→ℂ)(x:Grid c):EvenA c N:= if b then z 1 • Patron.total (canon c (Phased.amount E)) p.threshold x else 0
variable (hM :∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ u*Sen i w X)
variable (hk:1≤u)
include hk hM
-- can later incorporate soft rank.R.O with charge ``overA'' norm.N.O. budget center all.
lemma jobs (h:Ghoul E v b)(hP: Licence p a T t E)(ht:1 ≤ t)(hw:η+1+1≤a)(ha:0≤η): let R:= tideCost N u*T; let P:= payment 1 (4*p.B+2) 0 1 1 R η 0
   Peers (V) v p a t R ∧ Wax (H) p.threshold p.B η P t ∧ Yank (H) v ∧ SumBudget (fun i=>‖gemTone E i‖) ((Fintype.card (Site c):ℝ)*T) ∧ ∀ z:ℕ→ℂ, UnitCoeff z →∀ x:Grid c,
   Stem.income (weight E v z) p.threshold x= Stem.income (weight V v z) p.threshold x + sparkF c N (vern E z v) + labelled E b z x (p:=p)+ swarm (bleach H v z) x :=by
     have hh:0≤a:= by linarith
     have ht':0<t:=zero_lt_one.trans_le ht
     obtain ⟨f,hf,hV⟩:= hP.zone; have he :=h.alive.notes; intro R P; obtain ⟨hV1,hV2⟩:= virtue E v b h (Entr.Licence_g hP); obtain ⟨hv₁,hv₂,hv₃,hv₄⟩:= payed E b hM f hk ht' hV a η hf hw ha; have hL : Licence p a R t V:=⟨_,hv₁,hv₃⟩; have hK: Wax (H) p.threshold p.B η P t:= ⟨refundG E b p.threshold, _,hv₂,hv₄⟩; have hR:= (budget_mono (Stem.mast E f hf (fun i=> (hV i).travel) hh) (fun i=> norm_nonneg (gemTone E i)) (fun i=> (tempo E b i (zero_le_one.trans hk) hM ht' (hV i)).1));
     refine ⟨⟨hV1,(fun i=> by cases b; exact (by norm_num : 1 ≤ (2:ℕ)).trans (h.high i rfl); exact (h.first i rfl).ge), fun i=> resSeek E b i (he.real ..),?_, hL⟩,hK,hV2,hR,fun z hz U=>?_⟩
     · intro i r hh hv; cases b; · exfalso; have hz:=h.high i rfl; omega
       exact shapeRank E i hv r
     have hx := permits _ (payments V v z (fun i=>hz _) zero_le_one hL) ht' hh U; have hw: HasSum (fun i=> z (v i) • letters (spoke E b) p.threshold U i) (labelled E b z U (p:=p)):= by
          unfold labelled; split
          next hb=> subst b; have hw:=(spokeLamp E true U (Entr.Licence_g hP) (woke E v h.alive) (t:=p.threshold) (fun b i=> costsE E b (Loom.sumRide _ _ _ hf (fun i=>(hV i).travel) hh) ht' (fun i=>(hV i).sizeU _ (flat_ok ..)) i)).const_smul (z 1); simp_rw [fun i=> h.first i rfl]; simpa using hw
          next hb =>
            have hh': b=false := by simpa only [Bool.not_eq_true] using hb
            subst b; apply hasSum_zero.congr_fun; intro i; rw [show letters (spoke E false) _ _ i=0 from ?_,smul_zero]; unfold letters; by_cases hm: Healthy p.threshold ((spoke E false).addr i).support U
            · rw [masked_eq _ _ _ _ hm]; exact map_zero (beamCL (E.addr i).site N)
            exact masked_ne _ _ _ _ hm
     have he' : HasSum (fun i=> z (v i) • baker c N (gemTone E i)) (sparkF c N (vern E z v)):=by
         let g i:= z (v i)*(gemTone E i); have hh : Summable g:=Summable.of_norm_bounded hR.2.1 (fun i=> by unfold g; rw [norm_mul,Complex.norm_real]; exact mul_le_of_le_one_left (norm_nonneg _) (hz _)); refine (hh.hasSum.smul_const (1:EvenA c N)).congr_fun fun i=>?_ ; exact (mul_smul ..).symm
     let hS:= ((bleachPay H v z (fun i=>hz _) zero_le_one hK).heated ht ha U).1.hasSum; refine ((((hx.hasSum.add he').add hw).add hS).congr_fun (fun i=>?_)).tsum_eq
     rw [earns,earns]; -- dsimp only folded function
     change _=_+ z (v i) • ((H).mean i U); rw [← smul_add, ← smul_add,← smul_add, say]; abel -- ordering change
end YM.QCD.Relight
#print axioms YM.QCD.Relight.jobs
