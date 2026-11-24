import YM.Massive.Pith.Phases
import YM.QCD.Entr.Base
/-! The flavor filter Vᵢ Φ applied to identity and the spin lines. The norms used by the base cape still apply. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- parallel unfold cases
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick Port Entr
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
variable (b:Flavor N)
local notation "J"=> Modes c N
abbrev lightOn (b:Flavor N)(i: Modes c N):ℝ:=if b=i.2 then 1 else 0
def idP (b:Flavor N):Matrix J J ℂ := flute (Lat.Row c) (Matrix.diagonal (fun i=> (if b=i then 1 else 0)))
abbrev knob (c:Side)(b:Flavor N):= sways (Pith.idP (c:=c) b)
lemma diagP : idP (c:=c) b=Matrix.diagonal fun i:J=>(lightOn b i:ℂ):= (full (Lat.Row c) _).trans (by apply congr_arg Matrix.diagonal; funext i; unfold lightOn; split <;> simp [*]) -- syntax
lemma knob_wash (x:EvenA c N) : (knob c b x).val=wscale (Sum.elim (lightOn (c:=c) b) (lightOn b)) x.val:=by
   apply congr_arg (fun Y:Matrix (Pairs J) (Pairs J) ℂ=> changeVars Y x.val); ext i j; rw [diagP]; cases i with
   | inl i=> cases j with
      | inl j=> by_cases hp:i=j<;> simp [Matrix.diagonal_apply,hp]
      | inr j=> simp [Matrix.diagonal_apply]
   | inr i=> cases j with
      | inl j=> simp [Matrix.diagonal_apply]
      | inr j=> by_cases hp:i=j<;> simp [Matrix.diagonal_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,hp]
variable (v:EvenA c N)
lemma wagesP {t:ℝ} (o:Site c)(ht:0 ≤ t): Sen o t (knob c b v) ≤ Sen o t v:=by
    let f := Sum.elim (lightOn (c:=c) b) (lightOn (c:=c) b); have he(i: Pairs J): ‖(f i:ℂ)‖≤1:=by cases i <;> dsimp only [f,Sum.elim_inl,Sum.elim_inr,lightOn] <;> split <;> norm_num
    unfold Sen Stew.plank; rw [knob_wash,pricesD _ ht,pricesD _ ht]; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_left _ (starch_pos _ ht _); rw [wax,map_sum,sum_eq_single i]; rotate_left
    · intro j _ hj; rw [map_smul,map_smul,read_other _ _ (Ne.symm hj),smul_zero,smul_zero]
    · simp
    rw [map_smul,map_smul,Grass.read,norm_smul,norm_smul,norm_one,mul_one,norm_prod]; apply mul_le_of_le_one_right (norm_nonneg _); exact (prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=> he _)).trans_eq prod_const_one
lemma carriesP (Y:Support c) (h:Gated Y v): Gated Y (knob c b v):=by
   change ((knob c b v).val)∈_
   rw [knob_wash,wscale]; apply Cove.effects _ _ v.val h; intro i hi; rw [Grass.change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq]; exact Subalgebra.smul_mem _ (Creek.marked _ _ hi) _
lemma commuteP (x: Sheet c): Commute (idP b) (Lat.copies N x):= Sway.column ..
lemma vow (X: Sheet c): knob c b (sways (copies N X) v)= sways (copies N X) (knob c b v):=by unfold knob; rw [leaps,leaps,(commuteP b X).eq]
lemma songP : knob c b (Regal c N v)=Regal c N (knob c b v):=by
   change knob c b (sways _ ((OrbitG.spark _).passL _))=sways _ ((OrbitG.spark _).passL _)
   rw [show idol c N=copies N (Lat.chirality c) from rfl,vow b]; exact congr_arg _ (novel (idP b) v).symm
lemma finance (hp:Phases v): Phases (knob c b v):=by
    intro w hw; unfold knob; rw [leaps]; have hf:= congr_arg (sways (idP b)) (hp w hw); rw [leaps] at hf; refine Eq.trans (congr_arg (fun x=> sways x v) ?_) hf
    rw [idP,full,full]; ext i j; by_cases h:i=j <;> simp [h,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.diagonal_apply,mul_comm]
lemma pure (S:Sheet c): (knob c b (paleF N S)).val=form (Matrix.blockDiagonal (fun i:Flavor N=> if b=i then S else 0)):=by
    change disguise _ (form _) =_
    rw [disguise,form_map,Matrix.transpose_transpose]; refine congr_arg form ?_ -- inspect input matrices
    have hf : star (idP (c:=c) b)=idP (c:=c) b:=by rw [diagP]; ext i j; by_cases h:i=j <;> simp [Matrix.diagonal_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,h,Ne.symm]
    rw [hf, diagP]; ext ⟨i,x⟩ ⟨j,y⟩; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; rcases eq_or_ne x y with rfl|h <;> by_cases h':b=x <;> simp [copies,Matrix.blockDiagonal_apply,lightOn,h'] ; all_goals simp [h]
lemma profileK (i:Flavor N)(S:Sheet c): feeF i (knob c b (paleF N S))=if b=i then S else 0:=by
    ext x y; unfold feeF; rw [pure,gravid]; split <;> simp [Matrix.blockDiagonal_apply, *]
end YM.QCD.Pith
#print axioms YM.QCD.Pith.pure
