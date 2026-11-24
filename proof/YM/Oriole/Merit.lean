import YM.Oriole.Cactus
import YM.Oriole.Tree
/-! Contract Σ.All. Strong two-ended estimate.We.Pay. End normalized true endpoint Rφ.Execution.A note offX equality calibr. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open Function Finset Filter UV Lattice Wilson QCD QCD.Grass Poised Poised.Stative Module Poised.Display Poised.Plans Poised.Plans.Stamp.Stair Lat RG
open scoped Matrix Matrix.Norms.L2Operator BigOperators ContDiff Topology Classical TensorProduct
variable (a b:Flavor 6)(g:Bool){n m:ℕ}{s δ v η B Z ε Γ:ℝ}
local notation "F"=> flame a b g 8 (by decide)
local notation "L"=> arbor a b g
local notation "Q" => Lat.wave (claw g 0)
variable (t:Bool)(x y z: Label 8)
local notation "p"=> one_jet t 0
local notation "q"=> one_jet (!t) 0
lemma eq_mul (α β γ t:ℂ): t • Style a b g α β γ= Style a b g (t*α) (t*β) (t*γ):=by unfold Style; rw[smul_add,smul_add,smul_smul,smul_smul,smul_smul]
lemma eq_diff (α β γ θ η κ:ℂ) : Style a b g α β γ - Style a b g θ η κ = Style a b g (α-θ) (β-η) (γ-κ):=by unfold Style; rw [sub_smul α θ F,sub_smul β η (L true),sub_smul γ κ (L false)]; abel
local notation "PV"=>parL t g
local notation "PW"=>parR t g
lemma para : ‖parL t g‖≤1∧‖parR t g‖≤1:=by cases t<;>cases g<;>simp [parL,parR,idealR,poli]
variable (P:ℕ→BudgetPoint)(K w v:ℕ→ℝ)(X:ℕ→Label 8)(S:ℕ→ℝ){L0 e₁ εK Ax Fs T Z M ξ ψ α :ℝ}
local notation "PY" i:arg=> (K i:ℂ) • X i
local notation "ST" i:arg=> K i*S i/(w i)^2
variable (hh:Voyage P K v L0 Ax e₁ εK X w S n Fs T Z)
local notation "α'"=>4*L0*Ax
-- NOTE D from h.axes
local notation "Wb"=> (Fintype.card (Rings 8):ℝ)*4*L0
local notation "D"=> Wb*Z*Fs^6
local notation "E"=> Wb*2*εK
local notation "y'" i:arg=> T+2*((α'+1)* i)
local notation "Va"=> laps 6 F
local notation "J" m:arg=> ((ψ*Va+Va*α*(y' m))+E*(y' m))
local notation "Hv" m:arg => D*(J m)+E*(y' m)+e₁*m
local notation "H★" => (laps 8 (L true)*(1+ξ)+laps 8 (L false)*(1+ξ))
-- PLOT parameter before epochs.En. Earn θ≤height. ψ=mass horizon bound. ξ supplied from Beacon Era.Y proof. intention take Tol_B.Price layout.
variable (ℓ:ℂ)(x₀ x₁ x₂ z₀ z₁ z₂:ℂ) (hp:X 0=Style a b g x₀ x₁ x₂)(hz:X n=Style a b g z₀ z₁ z₂) (hν:‖z₁ - parL t g‖+‖z₂-parR t g‖ ≤ ξ)
variable (hB:‖(K 0:ℂ)*x₀+ℓ‖ ≤ α*(K 0*S 0/(w 0)^2)) (hψ : ‖ℓ‖ ≤ ψ) (hA:0≤α)
include hp hz hν hB hψ hA hh
lemma elic (hM:0<M)(hJ:J M+((n:ℝ)*(Hv M)+ H★)< M) : ‖(K 0:ℂ)*x₀+ℓ‖ ≤ α*(y' M) ∧ (‖(K 0:ℂ)*x₁-parL t g‖ + ‖(K 0:ℂ)*x₂-parR t g‖) ≤ (tariff a b true+tariff a b false)*((n:ℝ)*(Hv M))+ ξ:=by
     have hz₁: ‖z₁‖ ≤1+ξ:=by obtain ⟨ha,hb⟩:= para g t; linarith only [ha, hν, norm_nonneg (z₂-PW), norm_sub_norm_le z₁ PV]
     have hz₂: ‖z₂‖ ≤1+ξ:=by obtain ⟨ha,hb⟩:=para g t; linarith only [hb,hν,norm_nonneg (z₁-PV),norm_sub_norm_le z₂ PW]
     let v'(i:ℕ):=PY i; let s'(i:ℕ):= ST i
     have hv : laps 6 (PY 0) ≤ ψ*Va+Va*α*(ST 0):=by
          let t:= (K 0:ℂ)*x₀; have h1:t= (t+ℓ)-ℓ:= (add_sub_cancel_right ..).symm; have he: ‖t‖≤α*(ST 0)+ψ:= (by nth_rw 1 [h1]; exact (norm_sub_le ..).trans (add_le_add hB hψ)); rw[hp, Oriole.eq_mul,moneyA]; exact (mul_le_mul_of_nonneg_right he (laps_nn ..)).trans_eq (by ring)
     have hVn: v' n=X n:=by unfold v'; rw [hh.trusts,Complex.ofReal_one,one_smul]
     have hw:laps 8 (PY n) ≤ H★:=by rw [show PY n= _ from hVn,hz]; exact (moneyB ..).trans (add_le_add (mul_le_mul_of_nonneg_left hz₁ (laps_nn ..)) (mul_le_mul_of_nonneg_left hz₂ (laps_nn ..)))
     have ht:= axes _ _ _ L0 Ax e₁ εK _ _ _ _ _ hh hv -- signature check
     obtain ⟨hr,hx,hy⟩:= vernal v' s' ht (mul_nonneg (laps_nn ..) hA) (mul_nonneg ((norm_nonneg _).trans hψ) (laps_nn ..)) hM ((add_le_add_right (add_le_add_right hw _) _).trans_lt hJ)
     refine ⟨hB.trans (mul_le_mul_of_nonneg_left hy hA),?_⟩; let χ:ℂ:= K 0; have h1: ‖χ*x₁-z₁‖ ≤ tariff a b true*(n*(Hv M)):=by
          apply le_trans _ (mul_le_mul_of_nonneg_left hx (tariffs a b true)); rw [hVn,show v' 0= _ from congr_arg ((χ:ℂ) • ·) hp,hz,eq_mul,eq_diff]; exact mission a b g true ..
     have h2: ‖χ*x₂-z₂‖ ≤ tariff a b false*(n*(Hv M)):=by apply le_trans _ (mul_le_mul_of_nonneg_left hx (tariffs a b false)); rw [hVn,show v' 0= _ from congr_arg ((χ:ℂ) • ·) hp,hz,eq_mul,eq_diff]; exact mission a b g false ..
     linarith only [norm_sub_le_norm_sub_add_norm_sub (χ*x₁) z₁ PV, norm_sub_le_norm_sub_add_norm_sub (χ*x₂) z₂ PW,h1,h2,hν]
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.elic
