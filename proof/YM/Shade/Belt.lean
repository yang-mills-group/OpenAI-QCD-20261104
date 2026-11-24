import YM.Shade.Ozone
import YM.Tarn.Spoil
import YM.Alum.Chord
/-!
   Exact anchored penny stacks for central matched-PC layer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Filter Set Metric
open Lattice Cells QCD QCD.Lat UV Lattice Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.CardsT Intag.Vale GaugeP Rolls
open scoped Topology ContDiff BigOperators Classical
variable {C:Sequence} {k i j ℓ n:ℕ}{X:Type} [AddCommGroup X][Module ℝ X]
noncomputable abbrev button (C:Sequence)(i:ℕ) (s:Cover)(z:stalk C i) (x:Insertion (C.S.side (C.R i) (C.N i)) 6) := ((C.A i).regulator.average) (z s * x) -- performance
noncomputable def rod2 (C:Sequence)(i:ℕ)(z:stalk C i): Insertion (C.S.side (C.R i) (C.N i)) 6 →ₗ[ℝ]ℂ where
    toFun x:= button C i 0 z x
    map_add' x y:=by unfold button; rw [mul_add,map_add]
    map_smul' t x:=by unfold button; rw [mul_smul_comm]; exact map_smul (((C.A i).regulator.average).restrictScalars ℝ) t _
variable (h:stalk C i)
local notation "R" j:arg i:arg=> ratioTo C.S i j
variable (w:Averaging)(a:Axis)(x:Cover)
noncomputable abbrev spotB (S:Scheme)(j ℓ n:ℕ)(x:E4)(v: Cover):=ratioTo S n ℓ • (ratioTo S ℓ j • bead (S.spacing j) x)+v
noncomputable abbrev penC (S:Scheme)(j ℓ:ℕ)(x:E4):= ratioTo S ℓ j • (bead (S.spacing j) x)
lemma filtra (h:Cover → X)(x u:Cover): Averaging.filter w n (fun x=>h (x+u)) x= Averaging.filter w n h (x+u):=by rw [Rolls.roles, Rolls.roles]; apply Rolls.driftRoll
lemma togetherT (f g:Cover→ X): Averaging.filter w n (f-g)=Averaging.filter w n f-Averaging.filter w n g:= eq_sub_of_add_eq (by rw [roles,roles, roles, ←training, sub_add_cancel])
local notation "αᴺ"=> C.S.spacing (C.N i)
local notation "s" j:arg=> C.S.spacing j
local notation "Γ"=> MassFields.isotropic
local notation "V"=> MassFields.atVector a
lemma moneyM (Q: Insertion (C.S.side (C.R i) (C.N i)) 6 →ₗ[ℝ] X) (hJ:ℓ ≤ C.N i):∃ f:↥(Lattice.box (flex C.S ℓ (C.N i)))→ℝ,(∀ i,0 ≤ f i)∧(∑ i,f i)= 1 ∧ Q (CardsT.checkedT Γ (ratioTo C.S (C.N i) ℓ) (Rolls.nick αᴺ⁻¹ a h) x) = ∑ i':↥(Lattice.box (flex C.S ℓ (C.N i))), f i' • (((s ℓ)⁻¹/2) • (Q (h (ratioTo C.S (C.N i) ℓ • x+i'.val+ratioTo C.S (C.N i) ℓ • step a))-Q (h (ratioTo C.S (C.N i) ℓ • x+i'.val-ratioTo C.S (C.N i) ℓ • step a)))):=by
      let J:=ratioTo C.S (C.N i) ℓ; let u:=J • x; let b:Cover:= J • Lattice.step a; let F(x):= h (x+b); let G(x):= h (x+ -b)
      have hK : CardsT.checkedT Γ J (nick αᴺ⁻¹ a h) x=((s ℓ)⁻¹/2) • CardsT.checkedT V J (F-G) x:=by
           unfold checkedT; rw [stepwise h a x hJ,togetherT, smul_add, smul_sub J x,Pi.sub_apply]; unfold F G; rw [filtra,filtra, sub_eq_add_neg (J • x)]
      obtain ⟨f,hf,h1,hT⟩:=strummed C.S x V (F-G) hJ; refine ⟨f,hf,h1,?_⟩; change Q (checkedT Γ J _ x)=_; rw [hK]; unfold checkedT; change Q (_ • Averaging.filter V (ratioTo C.S (C.N i) ℓ) (F-G) _)=_; rw [hT,map_smul,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i' _; rw [map_smul,Pi.sub_apply, map_sub, smul_comm]; unfold F G; rw [← sub_eq_add_neg (ratioTo C.S (C.N i) ℓ • x+i'.val)]
lemma fleck {x:E4}(hj:j≤ℓ)(he:ℓ≤ C.N i)(z:Cover)(hz:z∈ Lattice.box (flex C.S ℓ (C.N i))) : dist (digit (C.S.spacing (C.N i)) (spotB C.S j ℓ (C.N i) x z)) x≤202*C.S.spacing j:=by
    have h:=port i ℓ he z hz; unfold spotB; rw [digit_plus,← gears he,← gears hj]; change dist _ x≤_; rw [dist_eq_norm]; rw[add_comm _ (digit _ z), add_sub_assoc]; refine (norm_add_le ..).trans ?_; rw[← dist_eq_norm]; linarith only [h,spacing_antitone C.S hj,smoothV (space0 C.S j) x]
lemma printF (w:ℝ): digit w (Lattice.step a)=w • basis a:=by
    unfold digit; have hp: vector (step a)=basis a:=by ext i; by_cases h:a=i; subst i; simp [vector,Lattice.step,basis_eq]; simp [vector,Lattice.step,basis_eq,h, Ne.symm h]
    rw[hp]
lemma flanks (he:ℓ ≤ C.N i) : digit αᴺ (x+ ratioTo C.S (C.N i) ℓ • Lattice.step a)=digit αᴺ x+C.S.spacing ℓ • basis a ∧ digit αᴺ (x-ratioTo C.S (C.N i) ℓ • Lattice.step a)=digit αᴺ x - C.S.spacing ℓ • basis a:=by rw [digit_plus, ← gears he, printF,sub_eq_add_neg x,digit_plus,digit_neg,← gears he,printF,sub_eq_add_neg]; exact ⟨rfl,rfl⟩
lemma purseL {I:Type*}[Fintype I](f:I→ℝ)(B:ℝ)(P:I→ℂ)(x:ℂ)(h:∀ i,0≤ f i)(hs:(∑ i,f i)=1)(hf:∀ i, ‖P i-x‖ ≤ B):‖(∑ i,f i • P i)-x‖ ≤ B:=by
     conv_lhs=> arg 1;arg 2;rw [show x=(∑ i,f i) • x from (by rw[hs,one_smul]),Finset.sum_smul]
     rw [← Finset.sum_sub_distrib]; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun i=>f i * B) (fun i _=>?_)) (le_of_eq ?_)); rw [← smul_sub,norm_smul,Real.norm_of_nonneg (h i)]; exact mul_le_mul_of_nonneg_left (hf i) (h i); rw [←Finset.sum_mul,hs,one_mul]
end YM.Massive.Needle
#print axioms YM.Massive.Needle.moneyM
#print axioms YM.Massive.Needle.fleck
#print axioms YM.Massive.Needle.flanks
