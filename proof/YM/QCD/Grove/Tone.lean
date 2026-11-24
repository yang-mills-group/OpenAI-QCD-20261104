import YM.QCD.Grove.Woven
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open AnalyticBridge VerifiedReset -- conflicts.
section beacon
-- Caller T' per Aux existence independent. combine h explicitly in Atrium
variable {m s q:ℕ}{L:Side}{Y: Stars→Side} (R:∀ i:Stars,(Y i).val=2*(m*Slide.roller i.val)) (F:Stars→Type) (S:∀ i:Stars,Finset (F i))(Z:∀ i, Gem (Y i) N (F i))(S': Finset J)(G: Gem C N J)(T:Finset I)(P:Gem c N I)
variable (A: C.val=c.val*D)(v:Stars→ℕ) (hM:∀ i,C.val=(Y i).val*(v i))(g:Site C→ℂ)(g':Stars→Site C→ℂ) {ε b:Stars→ℝ} (hm: LiftQ (normal (Deck.divides A) A) P G T S' g B w)(he:∀ i,LiftQ (normal (Deck.divides (hM i)) (hM i)) (Z i) G (S i) S' (g' i) B w)(h:SoilB T P B w t)(hZ:SoilB S' G B w t)(hv:∀ i,SoilB (S i) (Z i) B w t)(hq:81*m ≤ s)
-- plays payoff for auxiliary morph any landscape
noncomputable def elder (x: Site c) := Trio.mist R (Trio.rip (fun i=> crests (duskQ (S i) (Z i)))) x
noncomputable def relic (x: Site c)(B: BudgetPoint)(s:ℕ):Grid c→ℝ := crests (cloudQ (B:=B) T P) x- (fun _=>crests (duskQ T P) x 1) - Trio.unearthed B R s (Trio.rip (fun i=> crests (duskQ (S i) (Z i)))) x
local notation "Ξ"=> crests (duskQ T P)
local notation "ω₁"=> elder R F S Z
local notation "ω₂"=> fun i=> crests (duskQ (S i) (Z i))
include A hM he hm hZ h
lemma birds (hc:0≤t)(hC:2*(w+1)< C.val): Trio.CompatibleP B w (Ξ) (ω₂) :=⟨fun i x s b V=> lunarS (duskQ _ _) (s,b) x V,fun i j=> tendingU (hM i) (hM j) _ G _ _ S' _ _ _ (he i) (he j) hZ hc hC,fun i=> tendingU (hM i) A _ G P _ S' _ _ _ (he i) hm hZ hc hC, fun x=>(poetry h hc x).sites⟩ -- sig
omit A hM he hm hZ h
lemma note_eq (U:Grid c) : ∑ i:Site c,crests (cloudQ T P (B:=B)) i U= ((Fintype.card (Site c):ℝ)* (Ξ) 0 1 + (∑ i : Site c, masked B.threshold (neighbors s i) (ω₁ i) U)) +∑ i:Site c,relic R F S Z T P i B s U:=by
    have hv i: (Ξ) i 1=(Ξ) 0 1:=by
       have he:= lunarS (duskQ T P) (1,i) 0 1; rw [show Strut.sky (1,i) 1=1 from vane (1,i),show Strut.act (1,i) 0=i from ?_] at he; · exact he.symm
       change affine 1 i 0=i; simp [affine]
    have he (i:Site c): relic R F S Z T P i B s U = crests (cloudQ T P (B:=B)) i U- (Ξ) 0 1-Trio.unearthed B R s (Trio.rip (ω₂)) i U:= by unfold relic; simp only [Pi.sub_apply, hv]
    unfold elder; rw [Trio.sheens]; simp_rw [he]; rw [sum_sub_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]; ring
include A hM he hm hZ h hq
lemma scourge (hC:2*(w+1)< C.val)(hW:4*w+16≤ c.val)(hc:2*w≤ m)(hk:0<w)(hs:2*s ≤ q)(hp:0 ≤ t)(U:Grid c)(x:Site c)(hx: Healthy B.threshold (neighbors q x) U) : relic R F S Z T P x B s U=0:=by
    let Θ:= ω₂; have ht:= birds F S Z S' G T P A v hM g g' hm he h hZ hp hC; have hy:=Trio.sailing B R s _ U x hq hc hs hW hx _ (Trio.tinted _ _ ht) hk
    have hr:crests (cloudQ (B:=B) T P) x U=(Ξ) x U:=by
       unfold crests; congr 1; refine sum_congr rfl fun i _=>?_ ; let p:=(Strut.act i).symm x; unfold viewS; apply utter T P h
       have he:= healthy_pull i.1 i.2 B.threshold (neighbors w p) U
       apply he.1; change Healthy B.threshold (AnalyticBridge.VerifiedReset.Seat.spread i (neighbors w ((Strut.act i).symm x))) U; exact (merries w x i).symm ▸ (hx.mono_left (show neighbors w x ⊆ neighbors q x from fun j hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))) -- Eq elaboration
    change crests (cloudQ (B:=B) T P) x U-(Ξ) x 1 - _=0; rw [hr,show Trio.unearthed B R s (Trio.rip Θ) x U= Boulevard.stillA (Ξ x) U from hy, sub_self]
omit A hM he hm hZ h
include hv
lemma stalks (hc:0 ≤ t)(x:Site c): B.Regular (neighbors s x) (ω₁ x):=by
    unfold elder; rw [Trio.spruce]; refine regularA _ fun i hi=>?_; apply AnalyticBridge.CouplingShape.reg_scale; apply Slide.regular; · apply AnalyticBridge.CouplingShape.reg_sub _ (CouplingShape.reg_const _); let V:= ω₂; rw [show Trio.froth (V i)=(∑ j,V i j) from funext fun j=> (Finset.sum_apply ..).symm]; exact regularA _ (fun j _=>AnalyticBridge.VerifiedReset.reg_larger (poetry (hv i) hc j) (subset_univ _))
    intro p; exact (neighbors_mem ..).2 ((village (R i).ge _ _).trans ((roll_cap m i).trans hq))
lemma haggle (x:Site c)(ht:0 ≤ t)(he:∀ i,0 ≤ ε i)
    (hQ:∀ i:Stars,∀ W:Positions (Push.Uniform.Primary (Y i) su), ‖W‖+2*p<p'→flags B.threshold (Boulevard.actual W)=∅→∀ l:List (Directions su (Y i)),l.length≤ B.order→(∀ i∈ l,‖i‖≤ B.threshold)→ ‖leftDerivs ((songT t ∘ primed (S i) (Z i))- (fun _=>Reggae.baker (Y i) N (b i))) l (Boulevard.actual W)‖≤ ε i)(hy:∀ V:Grid c,Healthy B.threshold (neighbors s x) V→∀ i, Trio.Sharp.landscape B (Y i) p p' (Slide.shape (Trio.trackR R i) x V)) : B.supBounds x (neighbors s x) (ω₁ x) (Trio.oroH m B s (fun i=>charge_v B (ε i))):=by
      refine Trio.tallR B R s (ω₂) (fun i j=> AnalyticBridge.VerifiedReset.reg_larger (poetry (hv i) ht j) (subset_univ _)) (fun i=>?_) hq p p' x hy ?_
      · unfold charge_v; positivity [he i]
      intro i P hk hx l hL he; exact herring _ _ (hv i) (hQ i) P hx hk l hL he
end beacon
end YM.QCD.Grove
