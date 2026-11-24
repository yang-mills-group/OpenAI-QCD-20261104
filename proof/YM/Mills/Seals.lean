import YM.VMarker.Spare
import YM.Mills.Vivid
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
open SC
local notation "B!"=> ((1/32):ℝ)
local notation "b!"=> ((1/16):ℝ)
def foldP (p:R↪ E)(W:R→ℝ)(r:ℝ)(g:E→ℝ)(x:E):= clean p W g x*(if x∉Set.range p then r else 1)
def gaunt (v:R→ℝ)(Λ:ℝ)(x:E):ℝ:=clean O.ear v (fun _=>Λ) x
lemma gaunt_ge (v:R→ℝ) (h:∀ i,1≤ v i) (b:ℝ)(hb:1≤b)(i:E): 1 ≤ gaunt P F G O v b i:=toggle O.ear (fun i=>1≤gaunt P F G O v b i) (fun i=>by rw [gaunt,became]; exact h i) (fun i hi=>by rw [gaunt,other _ _ _ _ hi]; exact hb) i
private lemma multiply_exp (x b:ℝ)(h:1≤ b) : (Real.exp x-1)*b ≤Real.exp (b*x)-1:=by
    have he:= zero_lt_one.trans_le h
    have hp:0≤ b⁻¹:=(inv_pos.mpr he).le
    have ht:= convexOn_exp.2 (Set.mem_univ (b*x)) (Set.mem_univ (0:ℝ)) hp (sub_nonneg.mpr (inv_le_one_of_one_le₀ h)) (show b⁻¹+(1-b⁻¹)=1 from by ring)
    simp only [smul_eq_mul,mul_zero,Real.exp_zero,add_zero, ←mul_assoc, inv_mul_cancel₀ he.ne',one_mul,mul_one] at ht; have h':=mul_le_mul_of_nonneg_right ht he.le
    field_simp at h'; nlinarith only [h'] -- signature restore
lemma read_vivid (X:BudgetPoint)(h:Cents P f g t X.threshold)(hFill: Fill P f g b! b! s w u X.B)(v:R→ℝ)(Cz Λ:ℝ)(hv:∀ i,1 ≤v i)(hΛ:1≤Λ)(he:SC.Valve F p q t X.threshold X.B B! a v) (hA: Real.exp (-(b!- B!))*u*Λ+a ≤ Cz)(hI:G.Stock N X.B s B! t η (fun _=>1))(hη:η ≤ spareCut w)(ht:0<t) : ∃ (f0 f1:E→ℝ)(g0:K→ℝ), Cents P f0 g0 t X.threshold ∧ Cents P f1 g0 t X.threshold ∧ Fill P f1 g0 B! B! s w Cz X.B ∧ (Y★).Coins f0 g0 t X.threshold ∧ (Y★).Coins f1 g0 t X.threshold ∧∀ i,(Real.exp (f0 i)-1)*gaunt P F G O v Λ i≤ Real.exp (f1 i)-1:=by
    have hu:0≤ s:=hFill.cap
    obtain ⟨Qv,hQ,hH⟩:=he.back; obtain ⟨l,hl,hK⟩:=hI.price; have hkk i:0≤Qv i:= (Creek.load_nn ..).trans (hQ i 1); have hll i:0≤ l i:= (Creek.load_nn ..).trans (hl i 1)
    let K₁ := clean O.ear Qv f
    let A:= gaunt P F G O v Λ -- multiplier credit independent of output structure
    let K1:= fun i=> A i*K₁ i
    let K₂:=clean O.tag l 0; let g' i:= g i+K₂ i; have hg i: g i ≤ g' i:=le_add_of_nonneg_right (cleanNN _ _ hll i)
    have h0 i:0 ≤ K₁ i:=toggle O.ear (fun i=>0≤K₁ i) (fun i=> by unfold K₁; rw [became]; exact hkk i) (fun i hi=>by unfold K₁; rw [other _ _ _ _ hi]; exact h.pos _) i -- annotation
    have hZ : ∀ i,K₁ i ≤ K1 i:=fun i=>le_mul_of_one_le_left (h0 i) (gaunt_ge P F G O v hv Λ hΛ i)
    have hx : Cents P K₁ g' t X.threshold:=by
       refine ⟨h0,fun i=>(h.non i).trans (hg i),?_,fun i V=>(h.funds i V).trans (hg i)⟩; apply toggle O.ear
       · intro i V; have hx:P.reading X.threshold V (O.ear i)=0:=by
                     unfold Rise.reading; rw [O.freeP]; unfold masked; simp
         rw [hx,map_zero,QCD.Cove.load_zero]; exact h0 (O.ear i)
       intro i hi V; unfold K₁; rw [other _ _ _ _ hi]; exact h.cost i V
    have hf: (Y★).Coins K₁ g' t X.threshold:=by
       refine ⟨hx.pos,hx.non,?_,?_⟩
       · apply toggle O.ear
         · intro i V; rw [pullE]; exact (hQ i V).trans_eq (became ..).symm
         intro i hi V; rw [rootE P F G O i hi,stamp_cost _ ht]; exact hx.cost i V
       apply toggle O.tag
       · intro i V; rw [figuresK P F G O i|>.1]; apply le_trans (hl i V); unfold g' K₂; rw [became]; exact le_add_of_nonneg_left (h.non _)
       intro i hi V; rw [orientK P F G O i hi|>.1,comp_apply,stamp_cost _ ht]; exact (h.funds i V).trans (hg i)
    refine ⟨K₁,K1,g',hx,⟨fun i=>(h0 i).trans (hZ i),hx.non,fun i V=> (hx.cost i V).trans (hZ i),hx.funds⟩,⟨by norm_num, hu, fun i=>?_,fun i=>?_⟩,hf,{ hf with pos := fun i=>(h0 i).trans (hZ i), ready:= fun i V=>(hf.ready i V).trans (hZ i)},fun i=>multiply_exp (K₁ i) (A i) (gaunt_ge P F G O v hv Λ hΛ i)⟩ -- inspect Coin
    · have hp:= ticket s P h hFill (by norm_num : B! ≤ b!); let Q₁ i:=v i*Qv i
      have hv' i:0 ≤ Q₁ i:=mul_nonneg (zero_le_one.trans (hv i)) (hkk i); let W:= clean O.ear Q₁ 0
      have hN:= anchorReach F P.row O.ear Q₁ O.homeP hv' hH; let W':=fun i=> Λ*f i; let Kx i:= W i + W' i
      have hVs(j):K1 j≤ Kx j:= toggle O.ear (fun j=> K1 j ≤ Kx j) (fun j=>by unfold K1 Kx W; unfold K₁ A gaunt; rw [became,became,became]; exact le_add_of_nonneg_right (mul_nonneg (by linarith) (h.pos _))) (fun j hj=>by unfold K1 Kx W; unfold K₁ A gaunt; rw [other _ _ _ _ hj,other _ _ _ _ hj,other _ _ _ _ hj]; exact (le_add_of_nonneg_left (show (0:ℝ) ≤ 0 from le_rfl))) j
      have ht:Anchored (fun i=>(P.row i).site) Kx (fun i=>coverNumber X.B (P.row i).support) B! (a+Λ*(Real.exp (-(b!-B!))*u)):=by
        intro j; convert! budget_plus (hN j) (budget_scale (by exact zero_le_one.trans hΛ) (hp j)) using 1; funext i; unfold Kx; split; · rw [add_mul,mul_assoc]
        simp only [mul_zero,add_zero] -- adjust
      refine budget_loosen (C:=a+Λ*(Real.exp (-(b!-B!))*u)) ?_ (by linarith only [hA]); apply budget_mono (ht i); exact fun i=>ite_nonneg (mul_nonneg ((h0 i).trans (hZ i)) (Real.exp_pos _).le) le_rfl
      intro i; split; exact mul_le_mul_of_nonneg_right (hVs i) (Real.exp_pos _).le; exact le_rfl
    · let g₀ (k:K→ℝ)i:= k i*s^(P.front i).inv.card; let f i:=(P.front i).place; have hp:Ac.Hit f X.B (g₀ g) B! (Real.exp (-B!)*w):= hitLower f _ (fun i=>mul_nonneg (h.non i) (pow_nonneg hu _)) (fun i=>(P.front i).alive.mono (P.front i).part) (by norm_num : b!- B!=B!) (by norm_num) hFill.ε
      have h': Ac.Hit f X.B (g₀ K₂) B! η:= faresTax G _ _ _ O.mark hll hu hK; refine budget_loosen (C:=Real.exp (-B!)*w+η) ?_ (by unfold spareCut at hη; linarith only [hη]); convert budget_plus (hp i) (h' i) using 1; funext j; unfold g' g₀; split; dsimp only; rw [add_mul]; exact add_mul ..; exact (add_zero _).symm
end YM.MassiveQCD.Twist
#print axioms YM.MassiveQCD.Twist.read_vivid
