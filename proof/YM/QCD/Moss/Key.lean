import YM.QCD.Moss.Mercy
/-! # Transparent local filament. Prototype word for an exact period comparison. Forest, corrected slide choices and seam socks. No-limit letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory ProbabilityTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Coat Animals
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Loom Loom.Fleet
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Deck
open Further.PhysicalPeriodLimitF933 Macrame Stellar Mint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {P : Teller su}{O:Patch}{D :ℕ}{M:KernelChoices}
variable {h:f.val=c.val*O.L.val}{H:F.val=C.val*O.L.val}{hC:C.val=c.val*D}{he:2≤c.val}
local notation "Lx"=> Lace.project (h:=h) (H:=H) hC he
variable {W κ κ' μ β τ:ℝ} {R:Rep su f}{R':Rep su F}{X:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}
local notation "S"=>stepped M h
local notation "Y"=>stepped M H
variable {T:Tube su (stepped M h)} {T':Tube su (stepped M H)} {N:ℕ}{I J:Type}
variable {K:Cash W τ μ L X o κ T R}{K':Cash W τ μ L X o κ' T' R'}
variable (u:Fleet K I N) (v:Fleet K' J N)(z:EvenA C N →ₐ[ℝ] EvenA c N)
local notation "B"=>radiusB τ
variable {w:Pipe.Clump (stepped M H) J}{r:Pipe.Clump (stepped M h) I}{x:Site C}{n:ℕ}
variable (V:Page hC he u v z w r x n) {E:Tree.Forest (stepped M h).ratio}{G:Tree.Forest (stepped M H).ratio}
variable (hu:u.Famous)(hv:v.Famous) (hN: 2*(2*n+3)<c.val)
variable {A:Coat T E}{A':Coat T' G}
variable (O':T'=re T)(χ:Chi)(U:Grid c)(hU:RG.flags (Pressure.temp τ) U=∅)
include hU V
lemma flagsH:RG.flags (Pressure.temp τ) ((Lx).low.links U)=∅:=by
   ext i; rw [show i∈RG.flags (Pressure.temp τ) ((Lx).low.links U) ↔ _ from flagged hC U i (show _ from (by have h:=K.laws.data.room.buys; omega)) (Pressure.temp τ),hU]; simp
omit hU V
lemma reversed {I J:Type}[Fintype I][Fintype J][Nonempty I] (g:I→EvenA C N)(p:J→EvenA c N)(w:I→ J)(X: Matchup w) (ht:∀ i,z (g i)=p (w i)): z (choiceS g)=choiceS p:=by
    have h:=funext ht; obtain ⟨m,hm,hM⟩:= X.folded; unfold choiceS; rw [pay_for z,map_sum]; simp_rw [ht]; rw [Shingle.multiplied _ hM,Shingle.received _ hM, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; push_cast; congr 1; field_simp -- sig
include hu hv V hN hU O'
set_option quotPrecheck false
local notation "V'"=> (Lx).low.links U
lemma parityH (U' : (Lx).Fitted E G) :
   z (draws (planted (prism T' τ χ o.K (V') G) w.toLeft) ((v.suitcase G).capacityP w (own w.toLeft)))=
     draws (planted (prism T τ χ o.K U E) r.toLeft) ((u.suitcase E).capacityP r (own r.toLeft)):=by
      let X' := planted (prism T τ χ o.K U E) r.toLeft; let Y' := planted (prism T' τ χ o.K (V') G) w.toLeft
      have h1:X'.manifest:=planted_valid ..; have h2:Y'.manifest:=planted_valid ..
      have hp : bleached X':= by change { (roster r.toLeft) with flags:=RG.flags (Pressure.temp τ) U}=_; rw [V.cash,Mint.unrostered,hU]
      have hp': bleached Y':=by change {(roster w.toLeft) with flags:=RG.flags (Pressure.temp τ) (V')}= _; rw [V.news,Mint.unrostered,flagsH u v z V U hU] -- edit
      let p' := weftK (h:=h) (Q:=M) (H:=H) hC x
      let Xg:= (u.suitcase E).capacityP r (own r.toLeft); let Yg:= (v.suitcase G).capacityP w (own w.toLeft)
      have hh k: z (call (Y'.taggedL ((Lx).pullTag M k)) Yg)=call (X'.taggedL k) Xg:=by
         have hx: Stellar hC he P τ (X'.taggedL k) (Y'.taggedL ((Lx).pullTag M k)):=⟨hp,hp',rfl,rfl,rfl,rfl,rfl,U',rfl,K.laws.data.room,K'.laws.data.room,O',by have h:= K.laws.data.room.buys; omega⟩
         exact gravity u v z V hu hv hN _ _ hx rfl h1 h2
      unfold Beam.draws; apply reversed z _ _ p' (Mint.makeup x); intro i; rw [← show z _=call _ _ from hh (p' i)] -- reducible?
      apply congr_arg; have he i (hi:i∈v.fullA w):Deck.reverts hC x ((Lx).low.cut i)=i:=Deck.same_site hC x _ (by omega) V.reaches i hi
      refine call_critical K' _ Yg ((v.suitcase G).ripeP _ _ (v.forwarded G hv)) ((v.suitcase G).lullP _ _ (v.forwarded G hv)) (Y'.taggedL i) (Y'.taggedL ((Lx).pullTag M (p' i))) rfl rfl h2 h2 ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun k hk=> (congr_arg i.1 (he _ hk)).symm,fun k hk=>(congr_arg i.2 (show (Deck.reverts hC x ((Lx).low.cut k.1),k.2)=k from Prod.ext (he k.1 hk) rfl)).symm, fun _ _ _=>rfl⟩
lemma mermaid (Hr:u.Given r)(Hw:v.Given w): z (v.vF w χ (V'))= u.vF r χ U:=by
     letI:Nonempty (Tree.Forest (Y).ratio):= Tree.select (decreed H) O.odd_side; letI:Nonempty (Tree.Forest (S).ratio):= Tree.select (decreed h) O.odd_side
     have hh E (G:Tree.Forest (Y).ratio)(hr:(Lx).Fitted E G): z ((v.suitcase G).shootsP (prism T' τ χ o.K (V') G) w)=(u.suitcase E).shootsP (prism T τ χ o.K U E) r:=by
         have hf: RG.flags (Pressure.temp τ) (V')∩v.fullA w=(roster w.toLeft).flags:=by rw [flagsH u v z V U hU,empty_inter, V.news,Mint.unrostered]
         have hg: RG.flags (Pressure.temp τ) U∩u.fullA r=(roster r.toLeft).flags:=by rw [hU,empty_inter,V.cash,Mint.unrostered]
         unfold shootsP; rw [if_pos ⟨Hw.2.1,Hw.2.2,hf⟩,if_pos ⟨Hr.2.1,Hr.2.2,hg⟩]; exact parityH u v z V hu hv hN O' χ U hU hr
     let T (i:Reserve (Y)) j:= Deck.dismount (h:=h) hC he x (i (Deck.reverts hC x j)) -- shadows T
     unfold vF; apply reversed z _ _ T ((Deck.countingF (Q:=M) (h:=h) (H:=H) hC he x).expands _ (Deck.irrevocable ..)); intro k
     let F' := allot («S»:=(S)) (T k); let E':=(Lx).repeater F'; simp only
     have hy:= hh F' E' ⟨fun _=>rfl⟩
     refine Eq.trans ?_ hy; apply congr_arg; refine v.spacial w hv _ _ rfl rfl rfl rfl rfl (fun _ _ _=>rfl) rfl ?_; intro i hi
     let W:=Deck.reverts hC x; let a:= (Y).ratio.parent i; have hx: W ((Lx).low.cut a)=a:=Deck.same_site hC x _ (by omega) V.reaches _ hi
     change (k a).up i=F'.up ((Lx).high.cut i); unfold F' allot T; dsimp only; unfold dismount; dsimp only
     rw [show (S).ratio.parent _= _ from Lace.position (Lx) i,show reverts hC x ((Lx).low.cut ((Lx).R.parent i))=a from hx,Deck.hereagain (h:=h) (H:=H) hC he x (show a∈Set.range W from ⟨_,hx⟩) i rfl]
end YM.QCD.Moss
#print axioms YM.QCD.Moss.mermaid
