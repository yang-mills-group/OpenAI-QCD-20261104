import YM.VMarker.Spare
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
-- heat prices.F wan. 
local notation "B!"=> ((1/32):ℝ)
local notation "b!"=> ((1/16):ℝ)
lemma Pov (X:BudgetPoint)(h:Cents P f g t X.threshold)(hFill: Fill P f g (1/16) (1/16) s w u X.B) (X':BudgetPoint)(hB1:X.B=X'.B)(hB2:X.threshold=X'.threshold) (k:R→ℝ)(hB:F.Book p q)(hk: Ac.Hit (fun i=>(F.addr i).support) X'.B k B! a) (hE:∀ i,∀ j∈ F.z i,Sight (F.addr i).support (p j) m X' t (Reel.speaker q F i) (k i)) (hA: a ≤ spareCut u)(hv:G.Stock N X.B s B! t η (fun _=>1))(hη:η ≤ spareCut w)(ht:0<t) : ∃ (f':E→ℝ)(g':K→ℝ),Cents P f' g' t X.threshold ∧ Fill P f' g' B! B! s w u X.B ∧ (∀ i:R,k i ≤ f' (O.ear i)) ∧ (Y★).Coins f' g' t X.threshold:=by
    let ζ:=Real.exp (-(B!)); have hu:0≤ s:=hFill.cap
    obtain ⟨l,hl,hK⟩:=hv.price; have hkk i:0 ≤ k i:= (Creek.load_nn ..).trans (at_work F k hB X' ht hE i 1); have hll i:0≤ l i:= (Creek.load_nn ..).trans (hl i 1)
    let K₁:= clean O.ear k 0; let K₂:=clean O.tag l 0; let f' i:= f i+ K₁ i; let g' i:= g i+K₂ i; have hf i: f i ≤ f' i:=le_add_of_nonneg_right (cleanNN _ _ hkk i); have hg i: g i ≤ g' i:=le_add_of_nonneg_right (cleanNN _ _ hll i); have H:Cents P f' g' t X.threshold:=⟨fun i=>(h.pos i).trans (hf i),fun i=>(h.non i).trans (hg i), fun i V=>(h.cost i V).trans (hf i),fun i V=>(h.funds i V).trans (hg i)⟩
    refine ⟨f',g',H,⟨ by norm_num, hu, fun i=>?_,fun i=>?_⟩,fun i=>(by unfold f' K₁; rw [became]; exact le_add_of_nonneg_left (h.pos _)),⟨H.pos,H.non,?_,?_⟩⟩
    · have hp:= ticket s P h hFill (by norm_num : B! ≤ b!); have hN:= anchorReach F P.row O.ear k O.homeP hkk (show Ac.Hit (fun i=>(F.addr i).support) X.B k B! a from (by rw [hB1]; simpa using hk)); refine budget_loosen (C:= Real.exp (-(b!- B!))*u+a) ?_ (by unfold spareCut at hA; norm_num; linarith only [hA]); convert budget_plus (hp i) (hN i) using 1; funext j; unfold f'; split; exact add_mul ..; exact (add_zero _).symm
    · let g₀ (k:K→ℝ)i:= k i*s^(P.front i).inv.card; let f i:=(P.front i).place; have hp:Ac.Hit f X.B (g₀ g) B! (Real.exp (-B!)*w):= hitLower f _ (fun i=>mul_nonneg (h.non i) (pow_nonneg hu _)) (fun i=>(P.front i).alive.mono (P.front i).part) (by norm_num : b!- B!=B!) (by norm_num) hFill.ε
      have h': Ac.Hit f X.B (g₀ K₂) B! η:= faresTax G _ _ _ O.mark hll hu hK; refine budget_loosen (C:=Real.exp (-B!)*w+η) ?_ (by unfold spareCut at hη; linarith only [hη]); convert budget_plus (hp i) (h' i) using 1; funext j; unfold g' g₀; split; dsimp only; rw [add_mul]; exact add_mul ..; exact (add_zero _).symm
    · apply toggle O.ear; · intro i V; rw [pullE,hB2]; apply le_trans (at_work F k hB X' ht hE i V); unfold f' K₁; rw [became]; exact le_add_of_nonneg_left (h.pos _)
      intro i hi V; rw [rootE P F G O i hi,stamp_cost _ ht]; exact (h.cost i V).trans (hf i)
    apply toggle O.tag; · intro i V; rw [figuresK P F G O i|>.1]; apply le_trans (hl i V); unfold g' K₂; rw [became]; exact le_add_of_nonneg_left (h.non _)
    intro i hi V; rw [orientK P F G O i hi|>.1,comp_apply,stamp_cost _ ht]; exact (h.funds i V).trans (hg i)
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.Pov
