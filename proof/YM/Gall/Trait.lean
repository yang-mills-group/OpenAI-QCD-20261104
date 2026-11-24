import YM.Gall.Cone
import YM.Gall.IvyT
/-! Ward gradient bill. Two multipole's far order estimate ACTUAL Berry Tally. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s:ℝ}{c:Side}{n j d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
variable (P:BudgetPoint)(g:su.Color)(X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)(T:Taper)
variable {F H:∀ c:Side, Cray c}
lemma payout(h:Dart p F)(hp:p ≤ P.power): ∃ C:ℝ,0<C∧∀ c:Side,P.dirBound 0 (ink g (C⁻¹ • F c)):=by
    obtain ⟨f,hf,he⟩:= h; let C:=1+f*‖g‖/P.threshold; have hC:0<C:= by unfold C; positivity[P.threshold_pos]
    refine ⟨C,hC,fun c i=>?_⟩; change ‖(C⁻¹ • F c) i • g‖≤ _; rw[Pi.smul_apply,norm_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hC).le]; rw[mul_assoc]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (he c i) (norm_nonneg _)) (inv_pos.mpr hC).le).trans ?_
    rw [separation, sub_zero]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (peg_p i.1 _ _ hp).2 P.threshold_pos.le); rw [inv_mul_le_iff₀ hC]; rw [←mul_assoc C, show C*P.threshold=P.threshold+f*‖g‖ from (by unfold C; rw[add_mul,one_mul, div_mul_cancel₀ _ P.threshold_pos.ne'])]; nlinarith [pin_peg i.1 p,P.threshold_pos]
lemma stepCost(h:Dart p F)(hp:p ≤ P.power)(he:Dart q H)(hQ:q≤ P.power)(hm:2 ≤ P.order): ∃ C:ℝ,0 ≤ C ∧ ∀ (c:Side) (Y:Density c 6)(ν:ℝ)(n j:ℕ)(a:ℝ), Tutor 0 P Y ν n j a → ‖trade Y g (F c) (H c)‖ ≤ C*a:=by
    obtain ⟨x,hx,h⟩:=payout P g h hp; obtain ⟨y,hy,hY⟩:=payout P g he hQ; refine ⟨x*y,(mul_pos hx hy).le,fun c Y v n j a hT=>?_⟩
    let X:= x⁻¹ • F c; let W:= y⁻¹ • H c
    let M:= trade Y g; let hL:= shrub_p Y hT.smooth; have hv:‖M X W‖≤ a:=by
        rw [show M X W= _ from trailV g X W (shrub Y) hL hm]; let V: Lat.Fields c 6→L[ℝ]ℂ:= (coef (∅:Finset (Pairs (Modes c 6)))).toContinuousLinearMap.restrictScalars ℝ
        let l:=[ink g X,ink g W]; change ‖leftDerivs (V ∘ Y) l 1‖≤ a; rw[left_linear V l hT.smooth hm]; apply (one_price _).trans; refine hT.large _ hm ?_ ; intro i hi; rcases List.mem_cons.mp hi with rfl|hi; exact h _; obtain rfl:= List.mem_singleton.mp hi; exact hY _
    have hh:x • X= F c:=smul_inv_smul₀ hx.ne' _; have he:y • W= H c:=smul_inv_smul₀ hy.ne' _; change ‖M _ _‖≤_
    rw [←hh, ←he,map_smul M,ContinuousLinearMap.smul_apply,map_smul,smul_smul,norm_smul, Real.norm_of_nonneg (mul_pos hx hy).le]; exact mul_le_mul_of_nonneg_left hv (mul_pos hx hy).le
-- singular budget.Full
variable (k: Axis)(b: Cover)(h: ballU k b s)
set_option quotPrecheck false
local notation "B!" X:arg=> fling g T X
local notation "Wℓ"=> loot T g k b X s
local notation "Qℓ"=> wax T g k b Y s
local notation "Sℓ"=> whip g k -- check params out
local notation "Kℓ"=> whirr g k
variable (hP:3≤ P.power)(ht:2 ≤ P.order)
include h hP ht
lemma shipped : ∃ C:ℝ,0≤ C ∧ ∀ (c:Side)(Z:Density c 6)(v:ℝ)(n j:ℕ)(a:ℝ), Tutor 0 P Z v n j a→ GaugeInvariant (shrub Z) → ‖trade Z g (floats b (B! X)) (floats b (B! Y)) - (trade Z g (B! X) (B! Y)+ s • trade Z g (B! X) (B! (radial Y k)))‖ ≤ (c.val:ℝ)⁻¹ * (C*a):=by
    obtain ⟨R,hR,hQ⟩:=stepCost P g (listen T g X) (by omega) (sunWax T g k b h Y) hP ht; obtain ⟨A,hA,hE⟩:=stepCost P g (sunLoot T g k b h X) hP (wagons (listen T g Y) b (nearbyB _ _ h)) (by omega) ht
    refine ⟨R+A,add_nonneg hR hA,fun c Z v n j a hT hl=>?_⟩
    let f:= trade Z g; let L:Cray c:= floats b (B! X); let Y': Cray c:= floats b (B! Y)
    let g':=whip (s:=s) g k X c; let v':=whirr (s:=s) g k Y c
    have hX: L= Wℓ c+(B! X+g'):=by unfold loot L; rw[sub_add_cancel]
    have hy: Y'= Qℓ c+(B! Y+s • B! (radial Y k)+v'):=by unfold wax Y'; rw[sub_add_cancel]
    have hs:= shrub_p Z hT.smooth
    have hb(i:Cray c) : f i v'=0 ∧ f g' i=0:= ⟨shrine g i (shrub Z) hl _ hs ht, summit g i (shrub Z) hl _ hs ht⟩
    have hz : f L Y'-(f (B! X) (B! Y)+s • f (B! X) (B! (radial Y k)))= f (B! X) (Qℓ c)+ f (Wℓ c) Y':=by
          let T':=f (B! X)
          have hg: T' Y'=T' (Qℓ c)+(T' (B! Y)+s • T' (B! (radial Y k))):=by nth_rw 1 [hy]; rw[map_add,map_add,map_add,map_smul,show T' v'=0 from (hb _).1,add_zero]
          rw[hX,map_add,map_add,ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,(hb _).2,add_zero,show f _ Y'= _ from hg]; dsimp only [T']; abel
    let x:= (c.val:ℝ); have hp:0 < x:=by unfold x; positivity
    have hF: ‖x • f (B! X) (Qℓ c)‖ ≤ R*a:=by rw [← map_smul]; exact hQ _ _ _ _ _ _ hT
    have hG: ‖x • f (Wℓ c) Y'‖ ≤ A*a:=by rw [← ContinuousLinearMap.smul_apply,←map_smul]; exact hE _ _ _ _ _ _ hT
    change ‖f L Y'-_‖≤_; rw[hz,←div_eq_inv_mul]; apply (le_div_iff₀ hp).2; rw [mul_comm,show x= ‖x‖ from (Real.norm_of_nonneg hp.le).symm, ← norm_smul, smul_add]; exact (norm_add_le ..).trans ((add_le_add hF hG).trans_eq (add_mul ..).symm)
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.shipped
