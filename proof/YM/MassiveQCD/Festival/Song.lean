import YM.MassiveQCD.Festival.Hill
/-! # Ports for tilted log commuting before assembling a Cents layout
 Keep arbitrary P.t.order, lemma costs have `window`. Zero π still gives all masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Festival
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Stew.Phased Villa Ruby.LanternK
open MassiveQCD.Analysis.Many MassiveQCD.Analysis
variable (G:Gem c N I)(Y:Gem c N K)(dep:I→ℕ)
noncomputable def tuneLayout (z:ℂ): Gem c N (I × Rays):= ⟨fun i=>G.addr i.1,fun i=>plyM (G.view i.1) (z^dep i.1) i.2⟩
noncomputable def tierM (p:I→ℕ) (i:I×Rays):=p i.1*Many.tier i.2
variable (U:ℂ)
local notation "Z'"=> flagE G dep
local notation "X"=> tuneLayout G dep
variable {V:ℂ}
lemma oriented (hp:RotationE G dep)(x:ℝ): RotationE ((X) (x:ℂ)) (tierM dep):=by
    let A:= (X) (x:ℂ)
    let f:=G.view
    have h (s: EvenA c N →+* EvenA c N ) (hs: Continuous s)(hS: Bijective s) (i j:I)(u:Rays)(V W:Grid c) (hh:s (f i V)= f j W)(he:dep j=dep i): s (A.view (i,u) V)=A.view (j,u) W:=by
       let a:=(x:ℂ)
       change s (plyM (f i) (a^dep i) u V)=plyM (f j) (a^dep j) u W; rw [he]; apply plies _ s hs hS _ u; unfold a; rw [← Complex.ofReal_pow,Complex.coe_smul,Complex.coe_smul,eSM _ hs,hh]
    obtain h' := hp.notes; constructor
    · refine ⟨?_,?_,?_⟩
      · rintro ⟨i,u⟩; exact coloredLog _ (h'.gauge _) _
      · rintro ⟨i,u⟩ V g hG; exact h _ (phare _) (surfeit (unit_f hG.1)) i i _ V V (h'.num i V g hG) rfl
      · rintro ⟨i,u⟩ V; exact h _ (phare _) (imp _ (gammaL ..)) i i _ V V (h'.real i V) rfl
    intro p k g hk; obtain ⟨e,he⟩:= hp.turnsK p k g hk; refine ⟨Equiv.prodCongr e (Equiv.refl _),?_⟩; rintro ⟨i,u⟩
    exact ⟨ congr_arg (·*Many.tier u) (he i).1,(he i).2.1, fun V=> h _ (phare _) (surfeit (copies_unitary _ _ (Strut.trail hk))) i (e i) u (sky p V) V ((he i).2.2 V) (he i).1⟩
lemma woke (h:RotationE G dep): Keyed G:=by refine ⟨h.notes,fun s k d hk=>?_⟩; obtain ⟨d,hd⟩:=h.turnsK _ _ _ hk; exact ⟨d,fun i=>(hd i).2⟩
lemma quilt (hp:RotationE G dep)(p:K→ℕ)(he:RotationE Y p): RotationE (Reggae.weave G Y) (Sum.elim dep p):=by
    constructor
    · refine ⟨?_,?_,?_⟩ <;> rintro (i|i) <;> first | exact hp.notes.gauge i| exact hp.notes.num i| exact hp.notes.real i| exact he.notes.gauge i| exact he.notes.num i| exact he.notes.real i
    intro s k d h; obtain ⟨e,x⟩:= hp.turnsK _ _ _ h; obtain ⟨f,y⟩:= he.turnsK _ _ _ h; exact ⟨Equiv.sumCongr e f,(fun i=> by cases i <;> first|exact x _|exact y _)⟩
lemma weak_quilt (h:Keyed G) (hs:Keyed Y): Keyed (Reggae.weave G Y):=by
    have he {I:Type}(G:Gem c N I)(h:Keyed G): RotationE G (fun _=>0):=by constructor; exact h.notes; intro s k d hx; obtain ⟨e,x⟩:= h.turns _ _ _ hx; exact ⟨e,fun i=>⟨rfl,x i⟩⟩
    exact woke _ _ (quilt G Y _ (he G h) _ (he Y hs))
lemma woke0 (h:Crossing G):Keyed G:= ⟨⟨h.blank.gauge, fun i V=>AccentFit.of_fit (h.blank.num i V), h.blank.real⟩,h.rays⟩
lemma renounces (j:I)(l:Rays)(h:1 ≤ dep j):(X (0:ℂ)).view (j,l)=0:=by
    funext U; unfold tuneLayout plyM; have he:(0:ℂ)^dep j=0:=zero_pow (by omega); simp only [he,comp_apply]; rw [braid_homo (f:=G.view j) 0,zero_pow (by have hh:=Many.tack l; omega),zero_smul,Pi.zero_apply,log_zero]
noncomputable def priceM (k:ℕ)(p:I→ℝ)(i:I×Rays):= Many.vigor i.2*(logFee k* p i.1)
section budget
variable (f:I→ℝ) (h:Anchored (fun i=>(G.addr i).site) f (fun i=>coverNumber p.B (G.addr i).support) u a) (he:∀ i,Woven (G.addr i).site (G.addr i).support p t (G.view i) (f i))
include he
include h in
lemma levelK (h₀:‖U‖≤1): Licence p u a t (Z' U):=by
    refine ⟨f,h,fun i=>?_⟩; -- h not included fix
    exact (complexTone (he i) (U^dep i)).stretches (Subset.refl _) (mul_le_of_le_one_left (he i).travel (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h₀))
-- ensures simultaneous log ray costs (before χ)
lemma candles (ht:∀ i,2^p.order*f i ≤1/4)(hz:1 ≤ t)(h₀:‖U‖≤1):∀ i,Woven ((X U).addr i).site ((X U).addr i).support p t ((X U).view i) (priceM p.order f i):=by
   intro i; have he':‖U^dep i.1‖≤1:=by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h₀
   exact (braidLaw _ hz (he i.1) (ht i.1) he' i.2).1.stretches (Subset.refl _) (le_of_eq (mul_left_comm ..))
include h
omit he in
lemma seatsT : Anchored (fun i=> ((X U).addr i).site) (priceM p.order f) (fun i=> coverNumber p.B ((X U).addr i).support) u (logFee p.order*a*2):=by
   intro x; have hp:= budget_prod (budget_scale (show 0 ≤ logFee p.order from (by norm_num : (0:ℝ)≤2).trans (logFee_post ..)) (h x)) Many.purse
   convert hp using 1; funext i
   change (if _ then Many.vigor i.2*(logFee p.order*f i.1)* _ else 0)=(logFee p.order* (if _ then f i.1*_ else 0))* _
   by_cases h:(G.addr i.1).site=x
   · rw [if_pos h,if_pos (show ((X U).addr i).site=x from h)]; change _*_*Real.exp (u*coverNumber p.B _)=_; change _*Real.exp (u*coverNumber p.B (G.addr i.1).support)=_*_; ring
   rw [if_neg h,if_neg (show ¬ ((X U).addr i).site=x from h),mul_zero,zero_mul]
lemma tuneTotal (V:Grid c)(ht:∀ i,2^p.order*f i ≤1/4)(hz:1 ≤ t)(h₀:‖U‖≤1)(hv:0≤u):HasSum (letters (Z' U) p.threshold V) (Patron.total (X U) p.threshold V):=by
    have hp:= permits (X U) (show Licence p u _ t (X U) from ⟨priceM p.order f,seatsT G dep U f h, candles G dep U f he ht hz h₀⟩) (zero_lt_one.trans_le hz) hv V -- edit
    apply hp.hasSum.prod_fiberwise
    intro i; have hf:= lantern (U^dep i) hz (he i) (ht i) (show _ from by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h₀) V
    have hh : letters (Z' U) p.threshold V i = U^dep i • masked p.threshold (G.addr i).support (G.view i) V:=by
       by_cases h: Healthy p.threshold (G.addr i).support V; · unfold letters; rw [masked_eq _ _ _ _ (show Healthy _ ((Z' U).addr i).support V from h), masked_eq _ _ _ _ h]; rfl
       unfold letters; rw [masked_ne _ _ _ _ h,smul_zero]; exact masked_ne _ _ _ _ h
    rw [hh]; exact hf
end budget
end YM.QCD.Festival
