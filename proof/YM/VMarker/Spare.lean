import YM.VMarker.Reach
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Twist
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Ribbon Cupola Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Relight Plate Stew Stew.Phased Reggae
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K R U:Type}[Fintype I] {c:Side}{N:ℕ}
open Stitch
variable (P:Rise c N E K) (F:Reel c N I R)(G:Film c N I U)(O:Register P F G)
local notation "Z"=> Keys c N
local notation "Xq"=> Ribbon.Spine I
local notation "U★"=>rootR Xq (Keys c N)
local notation "P★"=>vacR Xq (Keys c N)
local notation "P₁"=> fun i=>rootR Xq Z ∘ P.main i
local notation "P₂"=> fun i=>rootR Xq Z ∘ P.plug i

local notation "Y★"=> result P F G O
variable {q:I→Bool}{p:I→Site c}{t s h a v u ε q0 w ξ η x:ℝ}{m:ℕ}{f:E→ℝ}{g:K→ℝ}
-- shared capacities; use given basis and startup extra ledgers. Use ALL support Boost estates.E.Shape
open Jets Jets.Touch Push.AbsoluteSums Ruby LanternK Tablet Footprint
open Dust Patron
lemma ticket (z:ℝ)(p' :Rise c N E K)(h:Cents p' f g w t)(hF:Fill p' f g u u z x s m)(he:v≤u) : Anchored (fun i=>(p'.row i).site) f (fun i=>coverNumber m (p'.row i).support) v (Real.exp (-(u-v))*s):=by
   intro i; refine budget_mono (budget_scale (Real.exp_nonneg _) (hF.χ i)) ?_ ?_
   · exact fun j=> ite_nonneg (mul_nonneg (h.pos j) (Real.exp_nonneg _)) le_rfl
   intro j; split; next ht=> dsimp only; rw [mul_left_comm (Real.exp _),← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (h.pos j); have H:1 ≤ (coverNumber m (p'.row j).support:ℝ):= Nat.one_le_cast.mpr ((Animals.price_pos ..).2 ⟨_,(p'.row j).anchor⟩); apply Real.exp_monotone; nlinarith
   next _=> rw [mul_zero]
-- root-credit value costs.Cent.PLAIN.
lemma pullE (i:R)(V:Grid c)(t:ℝ): (Y★).read t V (O.ear i)= Reel.mist F t i V:=by unfold Tablet.read; rw [figures P F G O i |>.1,O.homeP]; rfl
lemma rootE (i:E)(h:i∉Set.range O.ear)(V:Grid c)(t:ℝ): (Y★).read t V i= U★ (P.reading t V i):=by
    unfold Tablet.read Rise.reading; rw [(orient P F G O i h).1]; by_cases hp:Healthy t (P.row i).support V; rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; rfl; rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,map_zero]
lemma stamp_cost (x:EvenA c N)(h:0<t): credits t (U★ x)=load (fun _=>t) x.val:=by
    change load (Tablet.chip _ _ _) (embed Embedding.inl (x.val))=_; rw [transplant]; rfl; rintro (i|i); exact h; exact zero_lt_one -- ambiguous chip
lemma at_work (k:R→ℝ)(h:F.Book p q)(X:BudgetPoint)(ht:0<t)(he:∀ i,∀ j∈ F.z i,Sight (F.addr i).support (p j) m X t (Reel.speaker q F i) (k i))(i:R)(V:Grid c) : credits t (F.mist X.threshold i V) ≤ k i:=by
    obtain ⟨j,hj⟩:=h.stays i; have hG:= he i j hj
    by_cases hv:Healthy X.threshold (F.addr i).support V; swap; · rw [Reel.mist,masked_ne _ _ _ _ hv]; unfold credits; rw [map_zero,QCD.Cove.load_zero]; exact hG.travels
    rw [Reel.mist,masked_eq _ _ _ _ hv, polite_bill _ _ (h.stage i V).1 ht]; exact (viewer (p j) _ m ht).trans (hG.pole V hv [] (by simp) (by simp))
-- heat prices.F wan. 
local notation "B!"=> ((1/32):ℝ)
local notation "b!"=> ((1/16):ℝ)
noncomputable abbrev spareCut (x:ℝ):ℝ:= (1-Real.exp (-(1/32)))*x
lemma shared (X:BudgetPoint)(h:Cents P f g t X.threshold)(hFill: Fill P f g (1/16) (1/16) s w u X.B) (X':BudgetPoint)(hB1:X.B=X'.B)(hB2:X.threshold=X'.threshold) (he:F.Occupant p q t X' m B! a (fun _=>1)) (hA: a ≤ spareCut u)(hv:G.Stock N X.B s B! t η (fun _=>1))(hη:η ≤ spareCut w)(ht:0<t) : Payment P Y★ t X.threshold B! s X.B w u:=by
    let ζ:=Real.exp (-(B!)); have hB:= he.booked; have hu:0≤ s:=hFill.cap
    obtain ⟨k,hk,hE⟩:= he.reserve; obtain ⟨l,hl,hK⟩:=hv.price; have hkk i:0 ≤ k i:= (Creek.load_nn ..).trans (at_work F k hB X' ht hE i 1); have hll i:0≤ l i:= (Creek.load_nn ..).trans (hl i 1)
    let K₁:= clean O.ear k 0; let K₂:=clean O.tag l 0; let f' i:= f i+ K₁ i; let g' i:= g i+K₂ i; have hf i: f i ≤ f' i:=le_add_of_nonneg_right (cleanNN _ _ hkk i); have hg i: g i ≤ g' i:=le_add_of_nonneg_right (cleanNN _ _ hll i); have H:Cents P f' g' t X.threshold:=⟨fun i=>(h.pos i).trans (hf i),fun i=>(h.non i).trans (hg i), fun i V=>(h.cost i V).trans (hf i),fun i V=>(h.funds i V).trans (hg i)⟩
    refine ⟨f',g',H,⟨ by norm_num, hu, fun i=>?_,fun i=>?_⟩,⟨H.pos,H.non,?_,?_⟩⟩
    · have hp:= ticket s P h hFill (by norm_num : B! ≤ b!); have hN:= anchorReach F P.row O.ear k O.homeP hkk (show Ac.Hit (fun i=>(F.addr i).support) X.B k B! a from (by rw [hB1]; simpa using hk)); refine budget_loosen (C:= Real.exp (-(b!- B!))*u+a) ?_ (by unfold spareCut at hA; norm_num; linarith only [hA]); convert budget_plus (hp i) (hN i) using 1; funext j; unfold f'; split; exact add_mul ..; exact (add_zero _).symm
    · let g₀ (k:K→ℝ)i:= k i*s^(P.front i).inv.card; let f i:=(P.front i).place; have hp:Ac.Hit f X.B (g₀ g) B! (Real.exp (-B!)*w):= hitLower f _ (fun i=>mul_nonneg (h.non i) (pow_nonneg hu _)) (fun i=>(P.front i).alive.mono (P.front i).part) (by norm_num : b!- B!=B!) (by norm_num) hFill.ε
      have h': Ac.Hit f X.B (g₀ K₂) B! η:= faresTax G _ _ _ O.mark hll hu hK; refine budget_loosen (C:=Real.exp (-B!)*w+η) ?_ (by unfold spareCut at hη; linarith only [hη]); convert budget_plus (hp i) (h' i) using 1; funext j; unfold g' g₀; split; dsimp only; rw [add_mul]; exact add_mul ..; exact (add_zero _).symm
    · apply toggle O.ear; · intro i V; rw [pullE,hB2]; apply le_trans (at_work F k hB X' ht hE i V); unfold f' K₁; rw [became]; exact le_add_of_nonneg_left (h.pos _)
      intro i hi V; rw [rootE P F G O i hi,stamp_cost _ ht]; exact (h.cost i V).trans (hf i)
    apply toggle O.tag; · intro i V; rw [figuresK P F G O i|>.1]; apply le_trans (hl i V); unfold g' K₂; rw [became]; exact le_add_of_nonneg_left (h.non _)
    intro i hi V; rw [orientK P F G O i hi|>.1,comp_apply,stamp_cost _ ht]; exact (h.funds i V).trans (hg i)
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.shared
