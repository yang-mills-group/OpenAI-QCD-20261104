import YM.QCD.Finch.Nose
/-! # transport by spice. give height via fareG -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
open Stem Kites
variable (G: Gem c N I)(Y:Ruby.Hue c N J){Z K r d b:ℝ}
lemma avPos (c:Side): 0<averageC c:=by unfold averageC; positivity
lemma copiesG (h:0≤r) : SumBudget (fun _ : Strut c=> averageC c*r) r:=by
   refine budget_finite (fun i=>mul_nonneg (avPos c).le h) ?_; unfold averageC; rw [sum_const,card_univ,nsmul_eq_mul,mul_inv_cancel_left₀ (by positivity)]
set_option quotPrecheck false
local notation "W"=>glean G
local notation "M"=>Ruby.HGrace Y
lemma folded (he: Licence B Z K t G)(h:fareG 1 r N≤t)(hz:0<r): Licence B Z (turnCost B.order B.power*K) r W:=by
   obtain ⟨f,hf,hQ⟩:=he.zone; let H i:=averageC c*(turnCost B.order B.power*f i); let t:=turnCost B.order B.power; have ht:0≤t:= by unfold t turnCost; positivity
   refine ⟨H ∘ Prod.snd,fun x=>?_,fun i=>owls i.1 G i.2 _ (hQ _) h hz⟩
   let z(v:Strut c):= (act v).symm x; have hn:0≤K:=budget_nonneg (hf 0); refine budget_rows _ _ (fun v=>?_ ) (copiesG (c:=c) (mul_nonneg ht hn)); rw [←mul_assoc]; convert! budget_scale (mul_nonneg (avPos c).le ht) (hf (z v)) using 1; funext i
   have hv: x=((W).addr (v,i)).site ↔ z v=(G.addr i).site:= ⟨fun he=> congr_arg _ he|>.trans ((act v).symm_apply_apply _),fun h=>(show _ from by change x=act v _; rw [← h]; exact ((act v).apply_symm_apply _).symm)⟩ -- syntax
   have hp:coverNumber B.B ((W).addr (v,i)).support=coverNumber B.B (G.addr i).support:= cover_map (act v) (turn_sep _ _) ..
   change (if _ then H i*_ else _)=(averageC c*t)*(if _ then _ else _); dsimp only; rw [hp]
   by_cases heq:((W).addr (v,i)).site=x; · rw [if_pos heq,if_pos (hv.1 heq.symm).symm,show H i= (averageC c*t)*f i from (mul_assoc ..).symm,mul_assoc]
   rw [if_neg heq,if_neg (fun h=>heq (hv.mpr h.symm).symm),mul_zero]
lemma mixed (he:Dyed G): Crossing W:=by
   refine ⟨dyed _ he,fun v k g hh=>?_⟩
   refine ⟨Equiv.prodCongr (skyEquiv v) (Equiv.refl _),?_⟩; rintro ⟨p,i⟩; refine ⟨?_,fun U=>?_⟩
   · change rotateL (G.addr i) (pod v p)=rotateL (rotateL (G.addr i) p) v; unfold rotateL; congr 1
     · exact Equiv.congr_fun (podA ..) _
     change (G.addr i).support.image _=((G.addr i).support.image _).image _; rw [podA,image_image]; rfl
   change Diode N v k g (averageC c • spice p (G.view i (Strut.sky p (Strut.sky v U))))= averageC c • spice (pod v p) (G.view i (Strut.sky (pod v p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact coinT (G.view i _) (he.num i _) (Strut.comb hh (assured p)) (assured _)
lemma mixes (he:TokenB Y B.threshold B.B Z K t)(h:fareG 1 r N≤t)(hz:0<r): Purchases (M) B.threshold B.B Z K r:=by
   obtain ⟨f,hp,hQ⟩:=he.pay; let N₀ i:= averageC c*f i
   refine ⟨Ruby.votes _ he.gauge he.fit he.real,Ruby.rak _ he.mask,N₀∘Prod.snd,?_ ,fun x=>?_⟩
   · rintro ⟨v,i⟩ U; let A:= spice v (Y.mean i (Strut.sky v U)); change ‖token _ _ _ (averageC c • A)‖≤_
     have ht : token c N r (averageC c • A)=averageC c • token c N r A:=map_smul ((token c N r).restrictScalars ℝ) ..  -- wrong token vs songT defeq?
     rw [ht,norm_smul,Real.norm_of_nonneg (avPos _|>.le)]; exact mul_le_mul_of_nonneg_left (((soared v 0 t h hz _).2).trans (hQ _ _)) (avPos ..|>.le)
   let z(v:Strut c):=(act v).symm x; refine budget_rows _ _ (fun v=> ?_) (copiesG (c:=c) (budget_nonneg (hp 0))); convert! budget_scale (avPos c|>.le) (hp (z v)) using 1; ext i
   have he: x∈(M).bud (v,i) ↔ z v∈Y.bud i:=by nth_rw 1 [← (act v).apply_symm_apply x]; change act v (z v)∈Finset.image (act v) (Y.bud i) ↔ _; simp
   rw [show coverNumber B.B ((M).bud (v,i))=coverNumber B.B (Y.bud i) from cover_map (act v) (turn_sep _ _) ..]; by_cases h:x∈ (M).bud (v,i)
   · rw [if_pos h, if_pos (he.mp h)]; exact mul_assoc ..
   rw [if_neg h,if_neg (mt he.mpr h),mul_zero]
lemma fragrants (h:∀ i,Summable (letters G t i))(U:Grid c): potion (Stem.income G t) U=Stem.income W t U:=by
    let P v:=spice v (Stem.income G t (Strut.sky v U)); unfold potion; rw [smul_sum]; apply Eq.symm; apply HasSum.tsum_eq; refine Beam.lapis (letters W t U) _ (fun i=> ?_)
    apply (show HasSum (fun j=> averageC c • spice i (letters G t (Strut.sky i U) j)) (averageC c • P i) from (((h (Strut.sky i U)).hasSum.map (spice i) (phare _)).const_smul _)).congr_fun
    intro k; exact shapeS ..
lemma fragrance (h:∀ i,Summable (fun j=>Y.mean j i))(U: Grid c): potion (Calm.netT Y) U=Calm.netT (M) U:=by
    let P v:=spice v (Calm.netT Y (Strut.sky v U)); unfold potion; rw [smul_sum]; apply Eq.symm; apply HasSum.tsum_eq; refine Beam.lapis (fun i=> (M).mean i U) _ fun i=> ?_
    exact (((h (Strut.sky i U)).hasSum.map (spice i) (phare _)).const_smul _)
structure Compass (G: Gem c N I)(Y:Ruby.Hue c N J) (B:BudgetPoint)(d a t s ξ δ:ℝ)(f:Grid c→EvenA c N):Prop where
  costE : Licence B a d t G
  costY : Purchases Y B.threshold B.B s ξ t
  wardG : Crossing G
  projects : ∀ i,potion f i= Reggae.ocean c N δ+ Stem.income G B.threshold i+Calm.netT Y i
lemma lovely (F:Grid c→ EvenA c N)(hA:Calm.PayC G Y B t Z K d s b F)(ha:0≤Z)(hξ:0≤K)(ht:fareG 1 r N ≤ t)(hu:0<r)(he:1 ≤ t): Compass (W) (M) B (turnCost B.order B.power*d) Z r K s b F:=⟨folded G hA.pay ht hu, mixes Y hA.hat ht hu,mixed G hA.hue, fun i=> (hA.ears i).trans (by rw [crestedX,fragrants G (fun i=>permits G hA.pay (zero_lt_one.trans_le he) ha i),fragrance Y (fun i=>scaledLift Y hA.hat i hξ he),add_assoc])⟩
end YM.QCD.Finch
