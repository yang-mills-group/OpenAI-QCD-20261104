import YM.QCD.Stem.Creds
/-! # StampBer. collect certified Book at each Width. Era physical lift pose obligations only from outside. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A Δ θ ρ P':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration
variable (S:Gem c N I)(X:Finset I)(G:Gem c N J)(V':Ruby.Hue c N V)
lemma masking (L:Gem c N I)(U:Grid c)(t:ℝ)(x:I→Prop)(i:I): letters (Moss.muteK L x) t U i=if x i then letters L t U i else 0:=by
   unfold letters; rw [eitherX]; split; next he=> rfl
   next h=> simp [masked]
lemma dyedM (L:Gem c N I)(h:Dyed L)(x:I→Prop): Dyed (Moss.muteK L x):=by
    refine ⟨fun i=>?_,fun i=> ?_,fun i=>?_⟩
    · rw [eitherX]; split; exact h.gauge i; exact fun U k=>congr_arg Subtype.val (map_zero (sways (Lat.rotates N k)))
    · rw [eitherX]; split; exact h.num i; exact fun _ _ _=> map_zero _
    rw [eitherX]; split; exact h.real i; exact fun U=> map_zero _
noncomputable def spareH (c:Side)(N:ℕ): Ruby.Hue c N Empty:=⟨Empty.elim,Empty.elim⟩
lemma spareTu: TokenB (spareH c N) t n p 0 r:=⟨⟨fun i=> i.elim,fun i=> i.elim,fun i=> i.elim,fun i=> i.elim⟩,fun i=> i.elim,fun i=> i.elim,fun i=> i.elim,fun i=> i.elim,fun _=> ⟨fun i=> i.elim,Summable.of_finite,(by rw [tsum_empty])⟩,fun i=> i.elim⟩
-- actual at V with j—the upfront value and additional leaks. Budget accounts independent.
structure Bound (T:Gem c N I)(L:Finset I)(G:Gem c N J)(X:Ruby.Hue c N V)(P:BudgetPoint)(w:ℕ)(δ l h r α b:ℝ) (U:Grid c→EvenA c N):Prop where
  tilled :SoilB L T P w r
  rip   : Pockets L T P r l
  loom  :Licence P α δ r G
  deed  :Dyed G
  cash : TokenB X P.threshold P.B b h r
  earns (V:Grid c): U V= (∑ i∈ L,letters T P.threshold V i) +Patron.total G P.threshold V+∑' i,X.mean i V
lemma scaledLift (h:TokenB V' t n p p' r)(U:Grid c)(hw:0≤p)(hx:1≤r): Summable (fun i=> V'.mean i U):= by
    obtain ⟨v,hv,hF⟩:=h.pay; exact (Ruby.hearts V' h.mask hv (fun i=> (norm_nonneg _).trans (hF i 1)) hx hw hF U).1
lemma vRide (S:Support c)(w:ℕ)(x:Site c)(hz:j ≤ n* w)(hv:S=neighbors j x)(he:0<w): coverNumber w S ≤ ballCost n:= (Corona.cover_mono (hv ▸ (show neighbors j x ⊆ neighbors (n*w) x from (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans hz)))) w).trans (Corona.tile _ _ _ he)
abbrev penS (w n:ℕ)(d p:ℝ):ℝ:= ballCost w*(d*Real.exp (p*ballCost n))
lemma outport (X:Ruby.Hue c N (Site c))(w:ℕ)(hx:∀ i,X.bud i=neighbors w i) (h:Colors B X r d) (hp:0≤b)(hz:w ≤ n *B.B): TokenB X B.threshold B.B b (penS w n d b) r:=by
   have hd:0≤d:= (norm_nonneg _).trans (h.earn 0 1)
   refine ⟨h.tide,h.shape,h.flag,h.class',fun _=> d,fun x=> ?_,h.earn⟩ -- variable explicit p = b
   refine ⟨?_,Summable.of_finite,?_⟩
   · intro i; dsimp only; split_ifs <;> positivity
   rw [tsum_fintype]; have hK : (univ.filter fun i=>x∈ X.bud i)=neighbors w x:=by ext i; simp only [mem_filter,mem_univ,true_and,hx,neighbors_mem,separation_comm]
   dsimp only; rw [← sum_filter,hK]; refine (sum_le_sum (g:=fun _=> d*Real.exp (b*ballCost n)) ?_).trans ?_
   · intro i _; have he := vRide _ _ i hz (hx i) B.B_pos; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr he) hp)) hd
   rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (neighbors_card ..)) (by positivity)
lemma strew (Y:Ruby.Hue c N I)(G: Ruby.Hue c N J)(h:TokenB Y t w b d p)(hp:TokenB G t w b r p): TokenB (Ruby.HJoin Y G) t w b (d+r) p:=by
   obtain ⟨f,hf,H⟩:=h.pay; obtain ⟨g,hg,K⟩:=hp.pay; refine ⟨Ruby.branche Y G h.mask hp.mask,fun i=> ?_,fun i=> ?_,fun i=> ?_,Sum.elim f g,fun i=> Extra.Iteration.Cost.sum (hf i) (hg i), fun i U=>?_⟩ <;> cases i
   exacts [h.gauge _,hp.gauge _,h.fit _,hp.fit _,h.real _,hp.real _,H _ _, K _ _]
section combine
variable {I₁ I₂ I₃:Type}(Y:Gem c N I₁)(Z:Finset I₁)(E:Gem c N I₂)(F:Ruby.Hue c N I₃) {U W: Grid c→EvenA c N}
lemma hush (hp: Bound S X G V' B n d p p' r b t U)(hz: Bound Y Z E F B n A θ ρ r b t W)(hr:1≤r)(ht:0≤t)(hb:0≤b): Bound (Reggae.weave S Y) (Finset.disjSum X Z) (Reggae.weave G E) (Ruby.HJoin V' F) B n (d+A) (p+θ) (p'+ρ) r b t (U+W):=by
   have he : Dyed (Reggae.weave G E):=by
    let h:=hp.deed; let g:=hz.deed; exact ⟨fun i=>by cases i; exact h.gauge _; exact g.gauge _,fun i=>by cases i; exact h.num _; exact g.num _,fun i=> by cases i; exact h.real _; exact g.real _⟩
   refine ⟨vault S Y X Z hp.tilled hz.tilled, windfall S Y X Z hp.rip hz.rip, Reggae.guardL G E hp.loom hz.loom,he,strew V' F hp.cash hz.cash,?_⟩
   intro V; have hx:= scaledLift V' hp.cash V ht hr; have hr':= scaledLift F hz.cash V ht hr; have hh:=Summable.tsum_sum (f:=fun i=>(Ruby.HJoin V' F).mean i V) hx hr'
   rw [Pi.add_apply,hp.earns,hz.earns,woven_sum G E V (permits _ hp.loom (zero_lt_one.trans_le hr) hb V) (permits _ hz.loom (zero_lt_one.trans_le hr) hb V),sum_disjSum,hh]; change  _= (((∑ i∈X,letters S B.threshold V i)+∑ j∈Z,letters Y B.threshold V j)+(Patron.total G _ _ +Patron.total E _ _))+ ((∑' i,V'.mean i V)+∑' i,F.mean i V); abel
end combine
end YM.QCD.Stem
