import YM.Mural.Plank
/-! # prepare branded log roots. At single marker, pay log budgets as true Hits with no further losses from site volumes. -/
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
local notation "Y★"=> result P F G O
variable {q:I→Bool}{p:I→Site c}{t s h a v u ε q0 w ξ η x:ℝ}{m:ℕ}{f:E→ℝ}{g:K→ℝ}
open Jets Jets.Touch Push.AbsoluteSums Ruby LanternK Tablet Footprint Mural
open Dust Patron
local notation "B!"=> ((1/32):ℝ)
local notation "b!"=> ((1/16):ℝ)
lemma clean_h (k:R→ℝ)(h:E→RegularAddress c)(e:R↪E)(he:∀ i,h (e i)=F.addr i)(hk:0 ≤k)
   (hf:Ac.Hit (fun i=>(F.addr i).support) m k u a): Ac.Hit (fun i=>(h i).support) m (clean e k 0) u a:=by
     intro j; let p:E→ℝ:= fun i=> if j∈(h i).support then clean e k 0 i*Real.exp (u*coverNumber m (h i).support) else 0
     refine clean_budget e p a ?_ ?_ (?_)
     · intro i; exact ite_nonneg (mul_nonneg (cleanNN e _ hk _) (Real.exp_pos _).le) le_rfl
     · intro i hi; by_contra h; change p i≠0 at hi; apply hi; unfold p; rw [other _ _ _ _ h]; split; rw [show (0:E→ℝ) i=0 from rfl,zero_mul]; rfl
     convert! hf j using 1; funext i; unfold comp p; rw [he,became]
lemma uptoP (x:Tine c N I) (hb:1≤b!+t)(v:ℝ)(hv:1≤v)(hh:0<t) : premiumE c N I t v m x ≤ v^m * credits t x:= by exact Mural.stamp _ _ _ _ hv (fun i=>by cases i; exact hh; exact one_pos) _
variable (sL n':ℝ)(m:ℕ)
lemma collected (X:BudgetPoint)(S:Support c)(x₀:Site c)(h:Cents P f g t X.threshold)(hFill: Fill P f g b! b! s w u X.B)(hv:1 ≤v)(hT:0<t) (hc:v^m*u≤ sL)(he:0 ≤ s)(hp:v^m*n' ≤ s)(hn:1 ≤ n')(hJ: Pillars F p q S)(hX:x₀∈S) (hE:∃ k:R→ℝ,(∀ i U,premiumE c N I t v m (F.mist X.threshold i U) ≤ k i) ∧ Ac.Hit (fun i=>(F.addr i).support) X.B k B! a)(hG:G.Stock N X.B s B! t ξ (fun _=>1))(hw:ξ ≤ spareCut w) :
    ∃ (pe p₁:E→ℝ)(q:K→ℝ), Cents P pe q t X.threshold ∧ Fill P pe q B! B! n' w sL X.B ∧0 ≤ p₁ ∧ Ac.Hit (fun i:E=>(P.row i).support) X.B p₁ B! a ∧ (∀ i:E, p₁ i≠0 → x₀∈(P.row i).support ∧ pe i=0) ∧ Firm m Y★ v (pe+p₁) q t X.threshold :=by
   obtain ⟨k,h₁,h₂⟩:=hE; obtain ⟨l,hg,hχ⟩:=hG.price
   have hz:= zero_le_one.trans hv; let A:=v^m; have hA:1≤A:=one_le_pow₀ hv; have hx:=zero_le_one.trans hA; have hn':=zero_le_one.trans hn; have hf i:0 ≤ k i:= (Mural.repay_pos ..).trans (h₁ i 1); have hr i:0 ≤ l i:=(Creek.load_nn ..).trans (hg i 1); let E₀:=clean O.ear k (0:E→ℝ); let u0 (i:E):=A*f i; let e:=clean O.ear 0 u0; let K₀:=clean O.tag l 0; let w₀(j):= A*(g j+ K₀ j)
   have hm j (hi: j∉Set.range O.ear): e j= u0 j:= other _ _ _ _ hi; have hm0 i:e (O.ear i)=0:= became ..; have he':0 ≤ e:=fun i=> toggle O.ear (fun j=> 0 ≤ e j) (fun j=>(hm0 j).ge) (fun j hi=>(mul_nonneg hx (h.pos j)).trans_eq (hm j hi).symm) i
   have he₀:0 ≤ E₀:=cleanNN _ _ hf; have hk₀:0 ≤ K₀:= cleanNN _ _ hr
   have h0 i:g i≤ w₀ i:=le_trans (le_add_of_nonneg_right (hk₀ i)) (le_mul_of_one_le_left (add_nonneg (h.non i) (hk₀ i)) hA)
   have hp' i: 0≤ w₀ i:= (h.non _).trans (h0 _)
   refine ⟨e,E₀,w₀,⟨he', hp',?_,fun i U=>(h.funds i U).trans (h0 i)⟩,⟨by norm_num,hn',?_, ?_⟩,he₀,clean_h F k _ _ O.homeP hf h₂,?_, ⟨fun i=> add_nonneg (he' i) (he₀ i),hp', ?_,?_⟩⟩
   · apply toggle O.ear
     · intro i U; rw [show P.reading X.threshold U (O.ear i)=0 from ?_,map_zero,QCD.Cove.load_zero]; exact he' _; unfold Rise.reading; rw [O.freeP]; unfold masked; simp
     intro i hi U; rw [hm i hi]; exact (h.cost i U).trans (le_mul_of_one_le_left (h.pos _) hA)
   · intro i; refine budget_loosen (budget_mono (budget_scale hx (hFill.χ i)) ?_ ?_) hc; · intro j; exact ite_nonneg (mul_nonneg (he' j) (Real.exp_pos _).le) le_rfl
     intro j; split; next hp=>
       rw [← mul_assoc]; apply mul_le_mul
       · exact toggle O.ear (fun j=>e j≤u0 j) (fun j=>by rw [hm0]; exact mul_nonneg hx (h.pos _)) (fun j h=>(hm j h).le) j
       · exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
       · exact (Real.exp_pos _).le
       exact mul_nonneg hx (h.pos j)
     simp
   · let u':=fun j:K=>(P.front j).place; let p₀ (w:K→ℝ) (j:K):= w j * s^(P.front j).inv.card
     have ht: Ac.Hit u' X.B (p₀ g) B! (Real.exp (-B!)*w):= hitLower u' _ (fun i=>mul_nonneg (h.non i) (pow_nonneg he _)) (fun i=>(P.front i).alive.mono (P.front i).part) (by norm_num : b!- B!=B!) (by norm_num) hFill.ε
     have ht': Ac.Hit u' X.B (p₀ K₀) B! ξ:= faresTax G _ _ _ O.mark hr he hχ
     intro i; refine budget_loosen (budget_mono (budget_plus (ht i) (ht' i)) ?_ ?_) (by unfold spareCut at hw; linarith only [hw]); · intro j; exact ite_nonneg (mul_nonneg (mul_nonneg (hp' _) (pow_nonneg hn' _)) (Real.exp_pos _).le) le_rfl
     intro j; split; next hQ=>
        let z:=u' j; let N:=(P.front j).inv.card; have hz:0<N:=Finset.card_pos.mpr (P.front j).alive; have hA':A*n'^N≤ s^N:=by
           rw [show N=N-1+1 from by omega,pow_succ,pow_succ]; calc _= n'^(N-1)*(A*n'):=by ring
                                                                    _≤ _:=mul_le_mul (pow_le_pow_left₀ hn' ((le_mul_of_one_le_left hn' hA).trans hp) _) hp (mul_nonneg hx hn') (pow_nonneg he _)
        let p:=Real.exp (B!*coverNumber X.B (u' j)); change w₀ j*_ *p≤ (p₀ g j)*p+(p₀ K₀ j)*p; rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        unfold p₀ w₀; rw [←add_mul]; rw [mul_comm A,mul_assoc]; exact mul_le_mul_of_nonneg_left hA' (add_nonneg (h.non _) (hk₀ _))
     next hp=> norm_num
   · apply toggle O.ear
     · intro i _; exact ⟨(O.homeP i).symm ▸ hJ.boast i hX,hm0 i⟩ -- membership projection
     intro i hi hz; exact False.elim (hz (other _ _ _ _ hi))
   · have hc(z:Tine c N I): premiumE c N I t v m z≤ A*credits t z:= Mural.stamp _ _ _ _ hv (fun i=>by cases i; exact hT; exact one_pos) _; apply toggle O.ear
     · intro i V; rw [pullE]; exact (h₁ i V).trans ((became ..).symm.le.trans (le_add_of_nonneg_left (he' _))) -- argument order and inference
     intro i hi V; change _≤ e i + E₀ i; apply le_trans (hc _); rw [rootE P F G O i hi, stamp_cost _ hT,hm i hi]; exact (mul_le_mul_of_nonneg_left (h.cost i V) hx).trans (le_add_of_nonneg_right (he₀ i))
   apply toggle O.tag
   · intro i V; rw [figuresK P F G O i|>.1]; refine le_trans (Mural.stamp _ _ _ _ hv (fun i=>by cases i; exact hT; exact one_pos) _) (mul_le_mul_of_nonneg_left ?_ hx); apply (hg i V).trans; rw [show K₀ _=_ from became O.tag l (0:K→ℝ) i]; exact le_add_of_nonneg_left (h.non _)
   intro i hi V; refine le_trans (Mural.stamp _ _ _ _ hv (fun i=>by cases i; exact hT; exact one_pos) _) (?_); apply mul_le_mul_of_nonneg_left _ hx; rw [(orientK P F G O i hi).1, comp_apply, show Creek.load _ _ = Creek.load (fun _=> t) _ from stamp_cost _ hT]; exact (h.funds i V).trans (le_add_of_nonneg_right (hk₀ i))
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.collected
