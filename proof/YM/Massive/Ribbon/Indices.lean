import YM.Massive.Target.Calibration
import YM.Massive.Ribbon.Cross
import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-! # Spin derivative coordinate group. Ordinary polynomial version, degree fence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open scoped BigOperators Topology Matrix ComplexOrder Classical
variable {d : ℕ} (p q:EuPin)(x y:Multi d)
local notation "A"=> MvPolynomial Axis ℂ
open MvPolynomial
noncomputable abbrev token (p:Multi d): Axis →₀ℕ:= Finsupp.equivFunOnFinite.symm (power p)
noncomputable def walk (p:Multi d): A:= monomial (token p) 1
@[simp] lemma token_act(i:Axis): token x i=power x i:=Finsupp.equivFunOnFinite_symm_apply_apply ..
lemma walking : walk x=∏ i:Axis,(MvPolynomial.X i)^power x i:=by unfold walk; rw [monomial_eq,map_one,one_mul,Finsupp.prod_fintype]; simp; intros; simp -- check separate
lemma weightF (Q:Axis →₀ ℕ): Finsupp.weight 1 Q=∑ i,Q i:=by rw [Finsupp.weight_apply,Finsupp.sum_fintype]; simp; intros; simp
lemma token_eq (v w:Multi d) : token v=token w ↔ v=w:=by
   refine ⟨fun h=>Subtype.ext ?_,fun h=>congr_arg _ h⟩; funext i; apply Fin.ext; exact congr_arg (fun f:Axis→₀ ℕ=> f i) h
lemma token_onto (v:Axis→₀ ℕ)(h:Finsupp.weight 1 v ≤ d): ∃ p:Multi d, token p=v:=by
   rw [weightF] at h; have ht (i:Axis):v i<d+1:=lt_of_le_of_lt ((single_le_sum (fun j _=> Nat.zero_le (v j)) (mem_univ i)).trans h) d.lt_succ_self
   exact ⟨⟨fun i=> ⟨v i,ht i⟩,h⟩,DFunLike.ext _ _ fun i=>token_act ..⟩
noncomputable def stencilFrame (u:EuPin)(i:Axis): A:= ∑ j:Axis,MvPolynomial.C (u.coord.val j i:ℂ)*MvPolynomial.X j
noncomputable abbrev changeP (u:EuPin): A →ₐ[ℂ] A:= MvPolynomial.aeval (stencilFrame u)
lemma modulated : changeP p (walk x)= ∏ i:Axis, (stencilFrame p i)^power x i:=by rw [walking,map_prod]; simp only [map_pow,changeP,aeval_X]
lemma modal : multiMove p x y= coeff (token y) (changeP p (walk x)):=by rw [modulated]; rfl
lemma heights : (changeP p (walk x)).IsHomogeneous (UV.order (power x)):=by
   have ht(i:Axis): (stencilFrame p i).IsHomogeneous 1:= IsHomogeneous.sum _ _ 1 fun j _=> MvPolynomial.isHomogeneous_C_mul_X ..; rw [modulated]; exact IsHomogeneous.prod _ _ _ (fun i _=> (by simpa using (ht i).pow (power x i)))
lemma invariant_level (h:multiMove p x y ≠0): UV.order (power y)=UV.order (power x):=by rw [modal] at h; have hh:= (heights p x) h; rw [weightF] at hh; exact hh
lemma collect : changeP p (walk x)= ∑ i:Multi d, multiMove p x i • walk i:=by
   ext1 e; rw [coeff_sum]; by_cases he:∃ y:Multi d,token y=e
   · obtain ⟨y,rfl⟩:=he; rw [sum_eq_single y,_root_.MvPolynomial.coeff_smul]; simp [modal, walk] -- goals
     · intro i _ hi; simp only [walk,coeff_smul,coeff_monomial,token_eq,if_neg hi,smul_zero]
     simp
   have hp:(∀ i:Multi d,token i≠e):=not_exists.mp he; have hv: coeff e (changeP p (walk x))=0:=not_ne_iff.mp fun hx=> he (token_onto _ ((heights p x hx).le.trans x.property)); rw [hv]; exact (sum_eq_zero fun i _=> by simp [walk,coeff_monomial,hp]).symm
lemma spin_coord_mul : changeP (p*q)=(changeP p).comp (changeP q):=by
   ext1 i; simp only [changeP, AlgHom.comp_apply, aeval_X]; unfold stencilFrame; simp_rw [map_sum,map_mul,aeval_X,aeval_C];
   simp only [show (p*q).coord.val=p.coord.val*q.coord.val from rfl, Matrix.mul_apply, Complex.ofReal_sum,map_sum,sum_mul,Complex.ofReal_mul,mul_sum,map_mul]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; change _= C _*_; ring -- C arg inference
lemma stage (i:Axis) : stencilFrame 1 i = MvPolynomial.X i:=by unfold stencilFrame; simp [show (1:EuPin).coord.val=1 from rfl, Matrix.one_apply, apply_ite,ite_mul]
lemma spin_coord_id : changeP 1=AlgHom.id ℂ A:=by ext i; simp [changeP,stage]
def trM (d:ℕ) (p:EuPin) : Matrix (Multi d) (Multi d) ℂ:=Matrix.of (multiMove p)
@[simp] lemma tr_at : trM d p x y=multiMove p x y:=rfl
lemma row_table (d:ℕ) : trM d (p*q) = trM d q * trM d p:=by
   ext i j; rw [tr_at,modal,spin_coord_mul,AlgHom.comp_apply, collect, map_sum,coeff_sum,Matrix.mul_apply]; apply sum_congr rfl; intro k _; rw [map_smul, coeff_smul, ← modal, tr_at, tr_at]; rfl
lemma row_id (d:ℕ) : trM d 1=1:=by ext i j; rw [tr_at,modal,spin_coord_id]; simp only [AlgHom.id_apply,walk,coeff_monomial,token_eq,Matrix.one_apply] -- ...
lemma row_star : star (multiMove p x y)=multiMove p x y:=by
    have ht(i:Axis): MvPolynomial.map (starRingEnd ℂ) (stencilFrame p i)=stencilFrame p i:=by
         unfold stencilFrame; simp
    rw [modal,modulated]; have he(f:A): star (coeff (token y) f)=coeff (token y) (MvPolynomial.map (starRingEnd ℂ) f) := (MvPolynomial.coeff_map (starRingEnd ℂ) f (token y)).symm; rw [he]; simp only [map_prod,map_pow,ht]
end YM.Massive.UV
#print axioms YM.Massive.UV.row_table
