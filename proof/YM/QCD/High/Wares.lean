import YM.QCD.High.Tarp
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Scale/add proof. Weaken conditional for E heads. exact HASpanic.
variable {ι' μ:Type}
open Finch Calm Stem Push.BetaTransport Ring0 Jets.Touch Collection WilsonStartup
variable (b:Flavor N){G:Gem c N ι} {Y:Ruby.Hue c N β}{K:PathData su}{O:Clip}{W: St c}
-- param occupant Q sum tape.
section pre
noncomputable abbrev topsK (V:PathData su)(O:Clip)(P:BudgetPoint)(c:Side)(N:ℕ):Grid c→EvenA c N:= baker c N ∘ Push.BetaTransport.kinetic V O P
variable (hp:K.Bounds O σ A P) (he:Decent O p)(hw:Geo.Width p O σ) (hz:20 < c.val) (ha:0<a)
include hp he hw hz ha
lemma mastH (ht:0 ≤ t)(hh:t ≤ p.supportExponent) (hW: 2 ≤ p.B) :
     let q:=Φ p.B t c*price p t; let x:= air (treeH N c) p.B; let R:= bedT K p c; let V:= vowT K p O c; let G:=weave (linen x (-1)) (ostinato R V N); let Y:=Ruby.HJoin (tint (reef x p.threshold true) (-1)) (riff R V N)
     Cameo G Y p b a t (q+regularNeed su p O σ A 0 (p.threshold^2)) ((Fintype.card (Site c):ℝ)*q+softNeed su p O σ A 0 (p.threshold^2)) (topsK K O p c N):=by
     intro q x R V G Y; let r(U: Grid c):= ocean c N (∑ i:Site c,heads p i U); have hΞ:= spinX _ b (sincere (N:=N) (c:=c) p ha.le hW ht) (gigantic p) ht ha (by omega) r (fun U=> paidH U)
     obtain ⟨hF,hQ,hC,hH,hY⟩:= vowsP K O p N hp he hw hz ha; let Z:=ostinato R V N; let q' (U :Grid c):= baker c N (∑' i,V.logarithm i U)+Patron.total Z p.threshold U
     have hG : Cameo Z (riff R V N) p b a t _ _ q':=⟨hF,fun i hi=>⟨hQ.face i,hQ.van i hi⟩, shipX b _ _,wells _ hC hh (le_rfl),scant _ hH (by linarith) le_rfl,fun U=>by rw [show q' U= _ from rfl,add_sub_cancel_right]; exact (hY U).1⟩ -- issue rw show
     have hI:= cones (linen x (-1)) (tint (reef x p.threshold true) (-1)) b Z _ (chase x _ b (-1) hΞ ht ha) hG ht ha
     simp only [abs_neg,abs_one,one_mul,neg_one_smul] at hI
     rw [show topsK K O p c N= -r+q' from funext (fun i=>?_)] -- edit rw
     · exact hI
     have he' := (hY i).2
     let e:=((R.pours V).additive p i); let f:= (∑' j,V.logarithm j i); let d:=(∑ j,heads p j i); have hh: Patron.total Z p.threshold i=ocean c N e:=he'.tsum_eq
     have hs:Push.BetaTransport.kinetic K O p i+e=d+f:= wedgeK K O p hp he hw hz _; change baker c N _= -(r i) + (baker c N _+Patron.total Z p.threshold i); change baker c N _= -(ocean _ _ d)+(_+_); rw [hh, show Push.BetaTransport.kinetic K O p i=d+f-e from (by linarith only [hs]), map_sub,map_add]; unfold Reggae.ocean; rw [ContinuousLinearMap.neg_apply,ContinuousLinearMap.neg_apply,neg_neg]; abel
end pre
lemma fiddle (hp:AnchorT G p a t u)(h:0 ≤ r)(hz:r≤ a): Saline G p r t u false:=by
   obtain ⟨f,hf,hQ⟩:=hp.peg; refine ⟨f,hf,fun i=> ?_⟩; obtain ⟨⟨h1,h2,h3,h4,h5,h6⟩,hv⟩:= hQ i; refine ⟨⟨h1,h2,h3,?_,h5,h6⟩,fun U _=>(future (lens (G.addr i).site) h hz _).trans (hv _)⟩
   exact fun U hi l hl hd=>(future (lens _) h hz _).trans (h4 U hi l hl hd)
lemma liamG [Fintype ι] (hp:AnchorT G p a t u)(ht:Crossing G)(hv:0<t)(hz:2 ≤ c.val) (hr:0< r)(hh:r≤a)(hk:∀ U:Grid c,(∑ i,G.view i U)=paleF N (W U)):
   let k:= air G p.B; let q:=Φ p.B t c*u; Cameo k (reef k p.threshold false) p b r t q ((Fintype.card (Site c):ℝ)*q) (paleF N ∘ W):=by intro k q; exact spinX G b (fiddle hp hr.le hh) ht hv.le hr hz (paleF N∘W) (fun U=>by exact Eq.trans (Finset.sum_congr rfl (fun i _=>clothH G i U)) (hk U))
end YM.QCD.High
