import YM.Mural.Bison
/-! # payout to quorum reel. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon Push.AbsoluteSums
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
variable {V:Type*} [NormedCommRing V] [NormedAlgebra ℂ V] {f c:Side}
variable {I E:Type}{N:ℕ} (Z:PrintR f N Rank I E) (D₁ D₂: Grid f→ Mat)(z:ℂ)(S:Support f)
local notation "Ψ"=> Tine f N Unit
local notation "Tz"=> trestle Z D₁ D₂ z
local notation "Z★" i=>PrintR.regE Tz i
local notation "Y★" i=> PrintR.regK Tz i
variable (O:BudgetPoint)(p a b v w θ η ξ r:ℝ)
-- smooth proof generic crypto payments. leverage triangular caps.
lemma diam (H: V→ℝ) (ht:∀ X: Rank→V,H (∑ i,X i)≤∑ i,H (X i))(hV:∀ c:ℂ, ∀ X:V,H (c • X) = ‖c‖ * H X)(hz:H 0=0) (h:∀ x,0 ≤ H x) (u v:Mat)(p:Option Rank→ V)(f:Rank→ℝ)(hp:∀ i,H (p (some i))≤ f i) (i:Option Rank)(hy:∀ i j, ‖z‖*‖doll u v i j‖≤a) : H (muster u v z p i)≤ ∑ i:Rank,a*f i:=by
   have hh:0≤a:= (mul_nonneg (norm_nonneg z) (norm_nonneg _)).trans (hy (0,0) (0,0))
   cases i with | none=> exact hz.trans_le (sum_nonneg fun i _=> mul_nonneg hh ((h _).trans (hp i))) | some i=>
        unfold muster tot; dsimp only; rw [hV]; refine ((mul_le_mul_of_nonneg_left (ht _) (norm_nonneg _)).trans ?_); rw [mul_sum]; apply sum_le_sum; intro k _; rw [hV,← mul_assoc]; exact mul_le_mul (hy i k) (hp k) (h _) hh
-- maybe `tall_h pay` monotone.P.O
variable (H: Levy Z O r w p b η θ ξ) -- p old threshold. α log & b K.
variable (hp:∀ i:Grid f,∀ j k,‖z‖* ‖doll (D₁ i) (D₂ i) j k‖≤a) (ht:1 ≤ w) (hr:1 ≤r)
variable (ρ :ℝ)
local notation "Jg"=>Fintype.card Rank
variable (v₀:ℝ)
include H hp
set_option maxHeartbeats 540000 in
lemma esteem (hB:0 ≤ v₀)(hV: v₀ ≤ θ) (e k:ℝ)(he:e ≤ p) (hk:k≤ b) : Levy Tz O r w e k (Jg * (a*η)) v₀ (Jg *(a*ξ)):=by
    have ha: 0≤ a:= (mul_nonneg (norm_nonneg z) (norm_nonneg _)).trans (hp 1 (0,0) (0,0)); have hv:hB=hB:=rfl
    choose g ht hT using fun i:Rank=> H.budget (some i); let u i:= ∑ j:Rank,a*g j i; choose t hh hZ using fun i:Rank=> (H.fare (some i)).price
    let fE:= premiumE f N Unit w r 4; have hE i j:0≤g i j:= (repay_pos ..).trans (ht i j 1)
    constructor
    · intro i; refine ⟨u,fun j V=>?_ , fun j=>?_⟩
      · rw [vellum]; exact diam z a fE (fun X=>by unfold fE premiumE; rw [map_sum]; exact repay_sum ..) (fun z X=>by unfold fE premiumE; rw [map_smul,repayL]) (by unfold fE premiumE; rw [map_zero,repay_nil]) (fun x=> repay_pos ..) (D₁ V) (D₂ V) (fun i=>(Z.regE i).mist O.threshold j V) (fun i=>g i j) (fun i=> ht i j V) i (hp _)
      have hx:= budget_over (κ:=Rank) univ _ _ (fun i _=>budget_scale ha (hT i j))
      refine budget_loosen (budget_mono hx ?_ ?_) ?_
      · intro i; exact ite_nonneg (mul_nonneg (sum_nonneg fun j _=> mul_nonneg ha (hE j i)) (Real.exp_pos _).le) le_rfl
      · intro i; split; next hW=> simp_rw [if_pos (show j∈Z.mrR i from hW)]; unfold u; rw [sum_mul]; apply sum_le_sum; intro r _; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he ?_)) (mul_nonneg ha (hE r i)); positivity
        exact hx.1 _
      simp
    intro i; let u j:=∑ s:Rank,a*t s j
    have hg i j:0≤ t i j:= (Creek.load_nn ..).trans (hh i j 1)
    refine ⟨u,fun j V=>?_ , ?_⟩
    · let ZG:= Tablet.credits (c:=f) (N:=N) (I:=Unit) w
      exact diam z a ZG (fun X=>by unfold ZG Tablet.credits; rw [map_sum]; exact load_sum ..) (fun z X=>by unfold ZG Tablet.credits; rw [map_smul,load_scale]) (by unfold ZG Tablet.credits; rw [map_zero,QCD.Cove.load_zero]) (fun _=> load_nn ..) (D₁ V) (D₂ V) (fun i=>Z.etaK i j V) (fun i=>t i j) (fun i=> hh i j V) i (hp _)
    intro j; let F:= Y★ i; let X(k:E):= (F.addr k).place; have hT:= budget_over (κ:=Rank) univ _ _ (fun s _=>budget_scale ha (hZ s j))
    refine budget_loosen (budget_mono hT ?_ ?_) ?_
    · intro k; split; next h=> unfold Film.fares GasP.taxed; simp only [abs_one,prod_const_one,one_mul]; exact mul_nonneg (mul_nonneg (pow_nonneg hB _) (sum_nonneg fun j _=>mul_nonneg ha (hg j k))) (Real.exp_pos _).le
      next h=> exact le_rfl
    · intro t'; have hm i':((Z.regK (some i')).addr t').place=X t':=rfl; simp_rw [hm]; change (if j∈X t' then _ *Real.exp (k* _) else 0) ≤_; split
      next hW=>
         unfold Film.fares GasP.taxed; simp only [abs_one,prod_const_one,one_mul]; unfold u; rw [mul_sum,sum_mul]; apply sum_le_sum; intro r _; let p:=(Z.srcK.addr t').inv.card; let y:=coverNumber O.B (X t'); change v₀^p*(a*_)*Real.exp (k*y)≤ a*(θ^p*t r t'*Real.exp (b*y))
         rw [← mul_assoc a,mul_left_comm a]; exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hV _) (mul_nonneg ha (hg _ _))) (Real.exp_monotone (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _))) (Real.exp_pos _).le (by have H:= hg r t'; have HH:= hB.trans hV; positivity)
      next hX=>
         -- match hx; current transformed filter after simp? inspect
         simp
    simp
end YM.QCD.Comet
#print axioms YM.QCD.Comet.esteem
