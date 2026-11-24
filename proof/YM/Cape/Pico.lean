import YM.Cape.Glean
/-!
# Handling soft mask terms in marked K transactions
Bank plane implementation. Fixed old unmarked representation. Right Spine.
Soft entries appear precisely when W overlaps flags; we do not substitute an all-flat complement.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U:Type}[Fintype I]
variable (p:I→Site c)(q:I→Bool) (Y:Lure c N I Z) (F:Film c N I D)(M: Patron.Rail c N U)
variable {t v:ℝ}
local notation "K"=> Keys c N
local notation "R"=> Ribbon.Spine I
local notation "Φ"=> banknote N p v
local notation "Sh"=> withdraw N p v
local notation "φ"=> rootR R (Keys c N)
local notation "X"=> torah p F M v
local notation "Z'"=> vesta p Y v
local notation "P"=> Stalk p Y F M v
local notation "Γ"=> fog p Y F M v
variable (hY:Y.On p q t) (hF:F.Beat N p q t)(hM:M.Reg t)(hC:∀ i,Cove.shadeG (M.warp i))(hP:0<v)
local notation "T!"=> Trail Z' X t
local notation "Cz"=> Cob p Y F M v
local notation "H"=> coverP p Y F M v t

open Jets.Touch Footprint Trees GasP Creek
-- total not beyond Vale.A
variable {w:Z→ℝ}{g:U⊕ D→ℝ}{h:ℝ}{a s b m A B e ε δ u z κ C x:ℝ}{n:ℕ}
include hY hP
lemma niag (i:Z)(V:Grid c): Ruby.sparkY Z' V i=Φ (Y.wick i V):=by
    change exp (Φ (Y.wick i V))-1=_; rw [← map_exp (Φ) (Φ).toLinearMap.toContinuousLinearMap.continuous, ← map_one (Φ),← map_sub,Elevator.nilM (Y.wick i V) (hY.shades i V).1 (hY.enough i)]
omit hY hP in
lemma token_bill {v:ℝ} {T:Finset I} (x:Tine c N I)(hp:Polite q T x)(h:0<v) : ‖token c (ample N I) v (banknote N p v x)‖= Tablet.credits v x:=by -- edit
    change Creek.load (fun _=>v) (Ribbon.pen N p v x.val)=_; rw [← hp.exact,Ribbon.penkin N p v _ h,Stitch.Tablet.polite_bill _ _ hp h]
include hM hF
lemma prompted {T':P}(V:Grid c) : Φ (Sh ((T!).warp T' V))=(T!).warp T' V:=by
    change Φ (Sh (payer ..))= payer ..; unfold payer; split; swap; · rw [map_zero,map_zero]
    rw [map_prod,map_prod]; refine prod_congr rfl ?_; intro j _; rw [tint p q Y F M hY hF hM hP]; rcases j with j|j; exact rfl; change Φ (exp (_)-1)=sparkY _ _ _; rw [niag p q Y hY hP j V,Elevator.nilM (Y.wick j V) (hY.shades ..).1 (hY.enough _)]
omit hM hY
-- Combine unmarked.M and tagged Film prior. two input investments
local notation "Mk"=> torah p F M v
lemma unitedQ (h:Quits M n a s b v) (hx:F.Stock N n s b v m (fun _=>1)): Quits X n (a+m) s b v:=by
    obtain ⟨f,hf,Hf⟩:=h.cost; obtain ⟨u,hV,hx⟩:=hx.price; let g:=Sum.elim f u
    refine ⟨g,?_,?_⟩
    · convert Labels.together _ _ _ hf hx using 1; all_goals first|rfl|skip
      all_goals funext i; rcases i with i|i <;> first|rfl | skip
      simp only [Film.fares,taxed,g,torah,oriD,Sum.elim_inr,Film.addressSets,abs_one,prod_const_one,one_mul]
    rintro (i|j) V; · change ‖token c _ _ (banknote N p v (φ (M.warp i V)))‖≤_; rw [Plate.real_sector]; exact (Plate.payT (Y:=Ruby.Hue.mk (fun j=>(M.addr j).place) M.warp) ..).trans_le (Hf i V) -- payT orientation
    exact (token_bill p q _ (hF.budget j V).1 hP).trans_le (hV j V)
include hM hY
lemma reward (i:P)(V:Grid c)(hp:0 ≤ w)(hf:0 ≤ g)(hx:∀ i,Stitch.Tablet.credits v (Y.wick i V) ≤ wig w i)(he:∀ i,‖token c (ample N I) v ((X).warp i V)‖ ≤ g i):‖token c (ample N I) v ((T!).warp i V)‖≤ fair Z' X w g i:=by
    change ‖token c _ _ (payer ..)‖ ≤ _; unfold payer; split; swap; · rw [map_zero,norm_zero]; exact fairness _ _ hp hf i
    apply (Loom.folkl _ _ _).trans; apply prod_le_prod (fun _ _=>norm_nonneg _); intro j _; rcases j with j|j; exact he j
    change ‖token c _ _ (sparkY _ _ _)‖≤wig w j; rw [niag p q Y hY hP j V, token_bill p q _ (hY.shades j V).1 hP]; exact hx j
omit hM hY hF hP
-- budgets root.Ruby.Metro normalized natural levels
lemma scoring (G:ℝ)(hp:0 ≤ w)(hf:0 ≤ g)(hw:Ac.Hit Y.spot n w (a+b+1) G) (hh:Ac.Hit (Ruby.home X) n ((metal X G)*taxed (oriD X) g B) (a+b) C)(hb:C+C*Animals.ballCost n*G ≤ m)(ha:0≤a)(hp':0 < b)(hK:degreePrice n m b ≤ δ)(hm:0 < m)(hg:δ < 1)(hT:1 ≤ B): Ac.Hit (Ruby.home T!) n (taxed (oriD T!) (fair Z' X w g) B) a (m*(1-δ)⁻¹) :=by
   have hs:(0:(U⊕ D)→ℝ) ≤ taxed (oriD X) g B:=fun j => mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (hf j); refine priceV Z' X (k:=b) hp hf hT ?_ ha; refine ⟨hm,hp',hK,hg,fun i=> mul_nonneg (hs i.site) (prod_nonneg fun _ _=> wig_nn hp _),fun i=> budget_loosen (toned Z' X ?_ hp hs (by linarith) hh hw i) hb⟩
   intro i; refine budget_mono (hw i) (fun j=> ?_) (fun j=> ?_)
   · split; exact mul_nonneg (hp _) (Real.exp_pos _).le; exact le_rfl
   rw [show (Z').bud=Y.spot from rfl]; split; next hv=> refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hp _); exact mul_le_mul_of_nonneg_right (by linarith : a+b≤a+b+1) (Nat.cast_nonneg _)
   next _=> exact le_rfl
include hM hF hY hP
lemma arise (hp:0 ≤ w)(hf:0 ≤ g)(hx:∀ i V,Stitch.Tablet.credits v (Y.wick i V) ≤ wig w i)(he:∀ i V,‖token c (ample N I) v ((X).warp i V)‖ ≤ g i) (hr:Ac.Hit (Ruby.home T!) n (taxed (oriD T!) (fair Z' X w g) B) a m): Film.Stock N H n B a v m (fun _=>1) :=by
   let P0 i:= fair Z' X w g i; let D:Cz→ℝ:= fun i=> P0 i.val; refine ⟨D,?_,?_⟩
   · intro i V; have hx':=innerP p q Y F M hY hF hM hP i.val V
     change Tablet.credits v (Sh ((T!).warp i.val V)) ≤ _; rw [← token_bill p q _ hx'.1 hP,prompted p q Y F M hY hF hM hP V]; exact reward p q Y F M hY hF hM hP i.val V hp hf (fun i=>hx i V) (fun i=>he i V)
   intro i; let C:Cz→ℝ:=Film.fares N H D (fun _=>1) B; have hv:C=(fun j=>taxed (oriD T!) P0 B j.val):=by unfold C Film.fares; simp only [abs_one, prod_const_one,one_mul]; rfl
   have hW:= budget_pull (fun i:Cz=>i.val) Subtype.val_injective (hr i); unfold C at hv; rw [hv]; exact hW
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.arise
