import YM.Massive.Ribbon.Euph
import YM.Massive.Target.Calibration
/-! # Charge transformation on the raw polynomial table/coordinate space.

The offshell labels require simultaneous action on G and W spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass TensorProduct
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d:ℕ}
local notation "T" => SpinMode d
local notation "K" => starRingEnd ℂ

lemma label_law (x : Pol d) : x∈ labels d ↔ x∈ cap d ∧ ∀ u,colorAct u x=x:=by simp [labels,sub_eq_zero]
lemma reflMat (c:su.Color): su.colorMat (reflectColor c)= which true (su.colorMat c):=by
   let A:Mat:=su.colorMat c; change su.colorMat (su.projectColor (which true A))=_; apply Gauge.colorMat_project_self; refine (lie_iff _).mpr ⟨?_,?_⟩; have ha:= (lie_iff _).mp (su.colorMat_mem c); change star A= -A ∧ _ at ha; rw [which_star,ha.1]; ext; simp [which]
   rw [bar_trace A, show A.trace=0 from ((lie_iff _).mp (su.colorMat_mem c)).2,star_zero]
lemma which_double (u:Mat): which true (which true u)=u:=by ext; simp [which]
lemma refl_inv : Function.Involutive reflectColor:= fun _=> su.colorMat_injective (by rw [reflMat,reflMat,which_double])
lemma conjugate_inv : Function.Involutive conjugate:= fun _=> su.mat_injective (show which true (which true _) = _ from which_double _)
lemma reflPaint (c:su.Color)(u:su.El) : reflectColor (su.adjoint u c) = su.adjoint (conjugate u) (reflectColor c):=by
   apply su.colorMat_injective; rw [Gauge.mat_adjoint,reflMat,reflMat,Gauge.mat_adjoint]; unfold Gauge.conjugate -- star? 
   let U:=colour u; let L:Mat:=su.colorMat c; change which true (U*L*star U) = which true U*which true L*star (which true U); rw [which_mul,which_mul]; congr 1
lemma repaints (u:su.El)(X:Labels.Taylor su d) : recolor (Labels.Taylor.paint u X) = Labels.Taylor.paint (conjugate u) (recolor X):=by
   apply Subtype.ext; funext; ext1; exact reflPaint ..
abbrev wore : GPol→ₐ[ℂ] GPol:= Labels.changed (fun _=>recolor)
abbrev dyesG (u:su.El) : GPol→ₐ[ℂ] GPol:=Labels.changed (fun _=> Labels.Taylor.paint u)
lemma recol_inv : Function.Involutive (recolor (j:=d)):=by intro x; apply Subtype.ext; funext; ext1; exact refl_inv _
lemma wore_inv : Function.Involutive wore:=by
   intro x; apply Labels.eval_ext
   intro J; simp_rw [wore, Labels.eval_changed]; apply congr_arg (fun i=> Labels.read i x); funext; exact recol_inv _
lemma wore_colors (u:su.El)(x:GPol) : wore (dyesG (conjugate u) x)=dyesG u (wore x):=by
    unfold wore dyesG; apply Labels.eval_ext; intro J; simp_rw [Labels.eval_changed]; apply congr_arg (fun i=>Labels.read i x); funext i; exact (repaints u _).symm

lemma under_spin (X:Spike): spinTable (d:=d) X= turned 1 (wave X):=by rw [ribbon,row_id]; ext ⟨⟨i,w⟩,a⟩ ⟨⟨j,z⟩,b⟩; by_cases he:a=b <;> by_cases hv:i=j <;> simp [spinTable,Kit.choir,Matrix.blockDiagonal_apply,he,hv]
@[simp] lemma spin_one : spinTable (d:=d) 1=1:= by rw [under_spin,wave_one,cool]
lemma spin_mul (X Y:Spike): spinTable (d:=d) X*spinTable Y=spinTable (X*Y):=by rw [under_spin,under_spin,under_spin,reel,mul_one,wave_mul]
lemma invertC : -(chargeMatrix⁻¹).transpose= -chargeMatrix:=by
    have h: chargeMatrix⁻¹= -chargeMatrix := Matrix.inv_eq_right_inv (by rw [Matrix.mul_neg, Clifford.charge_sq,neg_neg]) -- inv_eq
    rw [h, transpose_neg, Clifford.transpose_charge, neg_neg]
lemma mono_color (u:su.El) : colorTable (d:=d) (conjugate u)=(star (colorTable u)).transpose:=by
    ext i j; by_cases he:i.2=j.2∧i.1.1=j.1.1; swap; · simp [colorTable, he, Matrix.star_eq_conjTranspose]
    simp only [colorTable, Matrix.star_eq_conjTranspose, transpose_apply, conjTranspose_apply, Matrix.of_apply,if_pos he]
    rw [colour_conjugate]; simp [touch, which,colour, Matrix.one_apply, apply_ite (K)]
lemma mono_color' (X:Spike)(u:su.El) : spinTable (d:=d) X*colorTable u=colorTable u*spinTable X:=by rw [under_spin,groom,reel,reel,(interlace (colour u) X).eq]
lemma mono_color'' (X:Spike)(u:su.El) : spinTable (d:=d) X*(star (colorTable u)).transpose=(star (colorTable u)).transpose*spinTable X:=by rw [← mono_color,mono_color']
abbrev masq (d:ℕ): Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ := fromBlocks 0 (spinTable chargeMatrix) (spinTable (-(chargeMatrix⁻¹).transpose)) 0
abbrev noir (u:su.El)(d:ℕ): Matrix (Pairs (SpinMode d)) (Pairs (SpinMode d)) ℂ := fromBlocks (colorTable u) 0 0 (star (colorTable u)).transpose
lemma masq_sq (d:ℕ) : masq d*masq d=1:=by unfold masq; rw [invertC,fromBlocks_multiply,spin_mul,spin_mul, Matrix.mul_neg, Matrix.neg_mul, Clifford.charge_sq]; simp; congr; exact Subsingleton.elim .. 
lemma paint_c (d:ℕ)(u:su.El): noir (conjugate u) d*masq d=masq d*noir u d:=by
   unfold noir masq; rw [fromBlocks_multiply,fromBlocks_multiply, ←mono_color (u:=conjugate u), conjugate_inv u, mono_color u] -- order! no after notation? cancels first
   simp only [Matrix.mul_zero, Matrix.zero_mul,add_zero,zero_add,mono_color',mono_color'']
lemma tracks_c (i j : Pairs T)(h:letterWeight i≠letterWeight j) : masq d i j=0:=by
   unfold masq; simp_rw [under_spin]; rcases i with i|i <;> rcases j with j|j
   · rfl
   · exact trails 1 _ _ _ h
   · exact trails 1 _ _ _ h
   rfl
lemma cap_c (x:Pol d)(h:x∈cap d): chargeAct x∈cap d:=changeCap (masq d) tracks_c _ _ h
lemma multipleChange {A B C:Type*}[Fintype A][Fintype B][Fintype C](S :Matrix A B ℂ)(R: Matrix B C ℂ)(X:Alg A): changeVars R (changeVars S X) = changeVars (S*R) X:=by rw [change_mul]; rfl
lemma inv_c : Function.Involutive (chargeAct (d:=d)):=by
    intro x; induction x using TensorProduct.induction_on with
    | zero=> simp
    | tmul x y=> unfold chargeAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (wore_inv x) (show changeVars _ (changeVars _ y)= _ from by rw [multipleChange, masq_sq, change_one]; rfl)
    | add x y hx hy=> simp only [map_add,hx,hy]
lemma dance_c (u:su.El)(x:Pol d) : chargeAct (colorAct (conjugate u) x)=colorAct u (chargeAct x):=by
    induction x using TensorProduct.induction_on with
    | zero=> simp
    | tmul x y=> unfold chargeAct colorAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (tmul ℂ) (wore_colors _ _) (show changeVars _ (changeVars (noir _ _) y) = changeVars (noir _ _) (changeVars _ y) from by rw [multipleChange,multipleChange,paint_c _ u])
    | add x y hx hy=> simp only [map_add,hx,hy]
lemma label_c (x:Label d): chargeAct x.val∈labels d:=by
   have h:= (label_law _).mp x.property; exact (label_law _).mpr ⟨ cap_c _ h.1, fun u=> (dance_c u x.val).symm.trans (by rw [h.2])⟩
noncomputable def chargeCore (d:ℕ): Label d≃ₗ[ℂ] Label d where
   toFun x:=⟨_,label_c x⟩
   invFun x:=⟨_,label_c x⟩
   left_inv x:=Subtype.ext (inv_c x.val)
   right_inv x:=Subtype.ext (inv_c x.val)
   map_add' _ _:=Subtype.ext (map_add chargeAct _ _)
   map_smul' _ _:=Subtype.ext (map_smul chargeAct _ _)
end YM.Massive.UV
#print axioms YM.Massive.UV.chargeCore
