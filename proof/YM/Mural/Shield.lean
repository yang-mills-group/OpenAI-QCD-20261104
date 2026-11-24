import YM.Mural.Mast
import YM.Mills.Seals
/-! # hit economy for a single insertion at a root. Existing unmarked preparation values, prices enhanced in place.
  Keep rootHit through covering conversion. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open QCD QCD.Grass QCD.Creek QCD.Lat Lattice Finset RG Wilson Function Loom QCD.Cove
open MeasureTheory NormedSpace Filter
open Kites Ruby Finch Stew Stew.Phased Reggae MassiveQCD MassiveQCD.Twist MassiveQCD.Ribbon MassiveQCD.Cupola Relight MassiveQCD.Plate
open scoped Topology BigOperators ContDiff Classical Matrix
variable {A B I E J K D U:Type}[Fintype I] {f c:Side}{N n:ℕ}
open Stitch Jets Jets.Touch Push.AbsoluteSums Ruby Tablet Footprint Dust Patron
variable (P:Rise f N E K) (F:Reel f N I D)(G:Film f N I U)(O: Twist.Register P F G)
local notation "Y★"=> result P F G O
variable {q:I→Bool}{p:I→Site f}{z t s s1 h a v u ε q0 w ξ η x:ℝ}{m:ℕ}{g:E→ℝ}{k:K→ℝ}
lemma tax_spread {i:D→ℝ}(X:D→Support f)(Y:D→Support c)(r:Ratio c f)(j:Site f){l M n:ℕ}(hC:reserve a v (conversion r l) ε)(he:Ac.Hit X M i a h)(hx:∀ u,j∈X u)(h0:∀ x,0≤ i x)(hr:∀ u,Y u ⊆ enlargement r l n (X u))(hb:0<n)(hm:M≤2*n): Ac.Hit Y n i v (Real.exp (v*preCost l)*h):=by
   intro u; refine budget_mono (budget_scale (Real.exp_pos _).le (he j)) (fun x=>?_) (fun x=>?_)
   · exact ite_nonneg (mul_nonneg (h0 _) (Real.exp_pos _).le) le_rfl
   split; next hp=>
     rw [if_pos (hx _)]; rw [mul_left_comm (Real.exp (v*_)) (i x),← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (h0 _)
     apply Real.exp_monotone; have hv: (coverNumber n (Y x):ℝ)≤ preCost l + conversion r l*coverNumber M (X x):=(Nat.cast_le.mpr (Lattice.Corona.cover_mono (hr x) n)).trans (footprint r l n M _ hb hm); have ht:(0:ℝ) ≤ (coverNumber M (X x):ℝ):=Nat.cast_nonneg _
     have hh:= mul_le_mul_of_nonneg_left hv hC.1; nlinarith only [hh,mul_le_mul_of_nonneg_right (show v*conversion r l≤a by linarith only [hC.2.1,hC.2.2]) ht]
   next hr'=>exact (budget_scale (Real.exp_pos _).le (he j)).1 _
lemma each_cost {B:Type}{H:D→Support f}{u:D→ℝ}(i:Site f)(h:∀ j,i∈H j)(he:Ac.Hit H m u a ξ)(hk:0≤a)(hr:∀ j,0≤u j)(j:D) : u j≤ξ:=by
   have hp:=budget_sum (he i) {j}; rw [sum_singleton,if_pos (h _)] at hp; exact (le_mul_of_one_le_right (hr _) (Real.one_le_exp (mul_nonneg hk (by positivity)))).trans hp
lemma areasM {u:E→ℝ}{H:E→Support f}(h:∀ j, H (O.ear j)=(F.addr j).support)(p:D→ℝ)(hz:0≤p)(he:Ac.Hit (fun j=> (F.addr j).support) m p a v): Ac.Hit H m (clean O.ear p 0) a v:=by
   intro i; let g j:= if i∈H j then clean O.ear p 0 j * Real.exp (a*coverNumber m (H j)) else 0
   have hv j:0 ≤g j:=ite_nonneg (mul_nonneg (cleanNN _ _ hz _) (Real.exp_pos _).le) le_rfl
   refine clean_budget O.ear g _ hv ?_ ?_
   · intro i; contrapose; intro hx; change ¬ g i ≠0; simp [g,other _ _ _ _ hx]
   convert he i using 1; funext j; simp only [Function.comp_apply,g,became,h]
lemma costToll (hv:1 ≤z)(hk:0<t)(x:Tine f N I): premiumE f N I t z n x ≤ z^n * credits t x:=stamp _ _ _ _ hv (by rintro (i|i); exact hk; exact one_pos) _
local notation "A!"=>(1/16:ℝ)
local notation "B!"=>(1/32:ℝ)
lemma vouchers (X:BudgetPoint)(hp:Cents P g k t X.threshold)(hX:Fill P g k A! A! s 1 u X.B)
   (hv :1 ≤z)(hs:0<s1)(hFunds:h>0)(he:z^n*u  ≤ w)(hz:z^n*s1 ≤ s)
   (hg:Film.Stock N G X.B s1 B! t η (fun _=>1))(hρ:z^n*η ≤ spareCut 1)(ht:0<t)
   (j:Site f)(hi:∀ i,j∈ (F.addr i).support)(hk:∃ p:D→ℝ,(∀ i Y, premiumE f N I t z n (Reel.mist F X.threshold i Y)≤p i)∧ Ac.Hit (fun i=>(F.addr i).support) X.B p B! h):
   ∃ (B:E→ℝ)(Z:E→ℝ)(C:K→ℝ),
        Cents P B C t X.threshold ∧
        Fill P B C B! B! s1 1 w X.B ∧
        Firm n Y★ z (B+Z) C t X.threshold ∧ 0≤ Z ∧
        Ac.Hit (fun i=> (P.row i).support) X.B Z B! h ∧ ∀ i:E, Z i ≠0→ j∈ (P.row i).support∧ B i=0:=by
   obtain ⟨p,h₀,h₁⟩:=hk; obtain ⟨v,hK,hQ⟩:=hg.price; have hx i:0≤p i:=(repay_pos ..).trans (h₀ i 1); have hkk i:0≤v i:= (load_nn ..).trans (hK i 1); let Z:= clean O.ear p 0; let b:= z^n; have hb:1≤ b:= one_le_pow₀ hv; have hb':0≤b:=zero_le_one.trans hb
   let Kx:=clean O.tag v 0; let β : E→ℝ:= clean O.ear (fun _=>0) (fun i=> b*g i); let Cx i:= b*(k i+Kx i)
   have hκ :∀ i,k i ≤ Cx i:= fun i=>le_trans (le_mul_of_one_le_left (hp.non _) hb) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (cleanNN _ _ hkk _)) hb'); have hΦ':0≤ Z:= fun i=> cleanNN _ _ hx _
   have HI i : β (O.ear i)=0:=became ..
   have HD i (h:i∉Set.range O.ear):β i= b*g i:=other _ _ _ _ h
   have hΦ:Cents P β Cx t X.threshold:=by
      refine ⟨toggle O.ear _ (fun i=>(HI i).symm ▸ le_rfl) (fun i h=> (HD i h).symm ▸ mul_nonneg hb' (hp.pos _)),fun i=>(hp.non i).trans (hκ i),?_,fun i x=>(hp.funds i x).trans (hκ i)⟩
      apply toggle O.ear
      · intro i U; unfold Rise.reading; rw [O.freeP,HI]; unfold masked; simp [load,wscale]
      intro i hx U; rw [HD i hx]; exact (hp.cost i _).trans (le_mul_of_one_le_left (hp.pos _) hb)
   have hBi:∀ i,β i≤ b*g i:=toggle O.ear _ (fun i=>(HI i).le.trans (mul_nonneg hb' (hp.pos _))) (fun i hi=>(other _ _ _ _ hi).le)
   refine ⟨β,Z,Cx,hΦ,⟨by norm_num, hs.le,fun i=>?_,fun i=>?_⟩,⟨fun i=>add_nonneg (hΦ.pos _) (hΦ' i),hΦ.non,?_,?_⟩,hΦ',areasM P F G O (u:=Z) (fun i=> congr_arg RegularAddress.support (O.homeP i)) p hx h₁,?_⟩ -- (fun i=> congr_arg RegularAddress.support (O.homeP i)) placeholder
   · refine budget_loosen (C:=b*u) (budget_mono (budget_scale hb' (hX.χ i)) (fun t=>ite_nonneg (mul_nonneg (hΦ.pos t) (Real.exp_pos _).le) le_rfl) (fun t=>?_)) he
     split; next h=> dsimp only; rw [←mul_assoc b]; apply mul_le_mul (hBi t) (Real.exp_monotone ?_) (Real.exp_pos _).le ((hΦ.pos t).trans (hBi t)); exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
     next _=> rw [mul_zero]
   · let V x:=(P.front x).inv.card; let f i:=(P.front i).place
     have hh1 : Ac.Hit f X.B (fun i=> b*k i*s1^(V i)) A! 1:=by -- hp name collision!
       apply Labels.raise_prices _ _ (w:=fun i=> k i*s^(V i)) (fun i=>?_ ) hX.ε (fun i=>?_)
       · exact mul_nonneg (mul_nonneg hb' (by exact hp.non _)) (pow_nonneg hs.le _)
       have hu : V i ≠ 0:= (card_pos.mpr (P.front i).alive).ne'
       have hE:b*s1^V i ≤ s^V i:=by
           calc
             b*_ ≤ b^V i * s1^V i :=mul_le_mul_of_nonneg_right (le_self_pow₀ hb hu) (pow_nonneg hs.le _)
             _ ≤ s^V i:=by rw [← mul_pow]; gcongr -- edit
       rw [mul_comm b, mul_assoc]; exact mul_le_mul_of_nonneg_left hE (hp.non _)
     have hh2 : Ac.Hit f X.B (fun i=> b*k i*s1^V i) B! (Real.exp (-B!)*1):= hitLower f _ (fun i=> mul_nonneg (mul_nonneg hb' (hp.non _)) (pow_nonneg hs.le _)) (fun i=>(P.front i).alive.mono (P.front i).part) (by norm_num:A!-B!=B!) (by norm_num) hh1
     have h' : Ac.Hit f X.B (fun i=>Kx i*s1^V i) B! η:= faresTax G _ _ _ O.mark hkk hs.le hQ; refine budget_loosen (C:=Real.exp (-B!)*1+b*η) ?_ (by unfold spareCut at hρ; linarith); convert budget_plus (hh2 i) (budget_scale hb' (h' i)) using 1; funext j; unfold Cx; split; next H'=> dsimp only; ring -- instances
     next H' => simp only [mul_zero,add_zero]
   · apply toggle O.ear
     · intro i U; rw [pullE]; apply (h₀ i U).trans; rw [Pi.add_apply,show Z (O.ear i)=_ from became ..]; exact le_add_of_nonneg_left (hΦ.pos _)
     intro i he U; rw [rootE P F G O i he]; change premiumE _ _ _ _ _ _ _ ≤ β i+ Z i; unfold β; rw [other _ _ _ _ he]; apply le_trans (costToll hv ht ..); rw [stamp_cost _ ht]; exact (mul_le_mul_of_nonneg_left (hp.cost i _) hb').trans (le_add_of_nonneg_right (hΦ' i))
   · apply toggle O.tag
     · intro i U; rw [(figuresK P F G O i).1]; apply (costToll hv ht ..).trans; unfold Cx Kx; rw [became]; exact mul_le_mul_of_nonneg_left ((hK i U).trans (le_add_of_nonneg_left (hp.non _))) hb'
     intro i h U; rw [(orientK P F G O i h).1]; apply (costToll hv ht ..).trans; unfold Cx; rw [comp_apply, stamp_cost _ ht]; exact mul_le_mul_of_nonneg_left ((hp.funds i U).trans (le_add_of_nonneg_right (cleanNN _ _ hkk _))) hb'
   apply toggle O.ear; exact fun i _=>⟨O.homeP i|>.symm ▸ hi _,became ..⟩; intro i hi hh; exact False.elim (hh (other _ _ _ _ hi))
end YM.QCD.Mural
#print axioms YM.QCD.Mural.vouchers
