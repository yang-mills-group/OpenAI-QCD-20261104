import YM.Arise.Stone
import YM.Planned.PRIMARY_INTEGRAL_295.Positions
/-! # Ambient finest-probe chart. Back observable pull is exact sym linear. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open Labels Maxwell
variable {r n m i j k d:ℕ}
variable {F M:Type*}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup M][NormedSpace ℝ M]
variable {G:Gauge}(a b:Axis)(p:PlaqAxes)(x:E4)
-- ordinary permutation frame at level j.
abbrev Window (k:ℕ):= Fin k→Axis
abbrev Proto (k:ℕ):=PlaqAxes × Window k
abbrev Motif (d:ℕ):= (i: Fin (d+1)) × Proto i.val
abbrev Tube (G:Gauge)(d:ℕ):= Motif d × G.ColorIndex
abbrev Ink (G:Gauge)(d:ℕ):= Tube G d→ℝ
abbrev codec {T:Type*}(v: Finset T)(h:T→F):=∑ i∈v,h i -- placeholder
local notation "Cg"=>G.Color
noncomputable def scroll (Y:Proto j→Cg)(a b:Axis): Window j→Cg:= if h:a<b then (fun w:Window j=> Y (⟨(a,b),h⟩,w)) else if h:b<a then (fun w:Window j=> -Y (⟨(b,a),h⟩,w)) else fun _=>0
lemma scroll_next (Y:Proto j→G.Color)(w:Window j): scroll (G:=G) Y p.val.1 p.val.2 w=Y (p,w):=by rw [scroll,dif_pos p.property]
lemma scroll_flip (Y:Proto j→G.Color)(w: Window j): scroll (G:=G) Y b a w= -scroll (G:=G) Y a b w:=by
    rcases lt_trichotomy a b with h|h|h
    · simp only [scroll, h, not_lt_of_gt h, ↓reduceDIte]
    · subst b; simp [scroll]
    simp only [scroll,h,not_lt_of_gt h,↓reduceDIte,neg_neg]
noncomputable def spanM (Y: Proto j→Cg)(a b:Axis)(x:E4): Cg:= ∑ w:Window j,(∏ i, x (w i)) • (((j.factorial:ℝ)⁻¹) • scroll (G:=G) Y a b w)
lemma spunM (Y:Proto j→Cg): spanM (G:=G) Y a b x= -spanM (G:=G) Y b a x:=by unfold spanM; rw [←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; rw [scroll_flip]; simp
lemma owns_Y (Y:Proto j→Cg): ∃ A: T E4 G.Color j,Tensor.Sym A∧ spanM (G:=G) Y a b=Tensor.diagonal A:=by
    open Planned.PrimaryIntegral295.Place in
      apply pure_sym; apply exact_of_smooth; swap
      · intro x t; unfold spanM; simp_rw [Finset.smul_sum, PiLp.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_fin,mul_smul]
      unfold spanM; fun_prop
noncomputable def spunZ (Y: Proto j→ G.Color): Maxwell.TwoJet G.Color j:= fun a b=>Classical.choose (owns_Y (G:=G) a b Y) -- hidden G
lemma sym_Y(Y: Proto j→Cg): Tensor.Sym (spunZ (G:=G) Y a b):=(Classical.choose_spec (owns_Y (G:=G) a b Y)).1
lemma yow(Y: Proto j→Cg): diagonal (spunZ (G:=G) Y a b)=spanM (G:=G) Y a b:=(Classical.choose_spec (owns_Y (G:=G) a b Y)).2.symm
lemma norm_Y (Y:Proto j→Cg):spunZ (G:=G) Y b a = -spunZ (G:=G) Y a b:=by
     let U:=spunZ (G:=G) Y a b; apply Tensor.ext_diag _ _ (sym_Y b a Y) (fun x h=>congr_arg (fun P:Cg=>-P) (sym_Y (G:=G) a b Y x h)); rw [yow]; funext x; change _=-(diagonal (spunZ (G:=G) Y a b) x); rw [yow]; exact spunM (G:=G) ..
noncomputable def wheel (Y: Proto j→ G.Color) : Taylor G j:=
  ⟨fun i=> (↑(j+2:ℕ):ℝ)⁻¹ •∑ k, added (spunZ (G:=G) Y k i) (compAxis k), by
       constructor
       · intro i v s; simp only [smul_apply,_root_.sum_apply,added_sym _ _ v s]
       intro z; simp only [diagonal,smul_apply,_root_.sum_apply]; simp_rw [show ∀ i k, added (spunZ (G:=G) Y k i) (compAxis k) (fun _=>z)=z k • diagonal (spunZ (G:=G) Y k i) z from fun k i => added_diag ..]; let A:=∑ i:Axis,z i • ((↑(j+2:ℕ):ℝ)⁻¹ • ∑ k, z k • diagonal (spunZ (G:=G) Y k i) z)
       change A=0; have h: A= -A:=by
           unfold A; simp_rw [Finset.smul_sum,←Finset.sum_neg_distrib,← smul_neg]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; nth_rw 1 [norm_Y]; simp only [diagonal,neg_apply,smul_smul]; congr 1; ring
       have he:(2:ℝ) • A=0:=by rw [two_smul]; nth_rw 1 [h]; simp
       exact (smul_eq_zero.mp he).resolve_left (by norm_num)⟩
lemma whirls (Y:Proto j→G.Color): Taylor.value (wheel Y) a x=(↑(j+2:ℕ):ℝ)⁻¹ • ∑ i:Axis,x i • spanM (G:=G) Y i a x:=by
     unfold Taylor.value wheel; simp only [diagonal,smul_apply,_root_.sum_apply]; congr 1; refine Finset.sum_congr rfl fun i _=> ?_ ; rw [← yow]; exact added_diag ..
noncomputable def rootLeg (A:Taylor G j) (p:Proto j):Cg:=Nat.factorial j • (takeCurl A p.1.val.1 p.1.val.2 (basis∘ p.2))
lemma scrolled (A:Taylor G j)(p:Window j): scroll (G:=G) (rootLeg A) a b p=j.factorial • takeCurl A a b (basis∘p):=by
    have ht:= closedCurl A; rcases lt_trichotomy a b with h|h|h
    · exact scroll_next (G:=G) ⟨(a,b),h⟩ (rootLeg A) p
    · subst b
      have he (c:T E4 G.Color j) (h:c= -c) : c=0:=by
                 have hu:(2:ℝ) • c=0:=by rw [two_smul]; nth_rw 1 [h]; simp
                 exact (smul_eq_zero.mp hu).resolve_left (by norm_num)
      rw [he (takeCurl A a a) (ht.antisymmetric a a)]; simp [scroll]
    rw [scroll_flip]; rw [scroll_next (G:=G) ⟨(b,a),h⟩]; unfold rootLeg; dsimp only; rw [ht.antisymmetric b a,neg_apply,smul_neg,neg_neg]
lemma lived (A:Taylor G j): spanM (G:=G) (rootLeg A) a b x=Tensor.diagonal (takeCurl A a b) x:=by
     let U:=takeCurl A a b; unfold spanM; simp_rw [scrolled (G:=G),← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (show (j.factorial:ℝ)≠0 by positivity)]; change _=U (fun _=>x)
     have hh:(∑ i:Axis,x i • basis i)=x:=by ext i; simp
     rw [show (fun _:Fin j=>x)= (fun i:Fin j=>∑ j:Axis,x j • basis j) from funext fun _=>hh.symm, U.map_sum (fun _ i=>x i • basis i)]; refine sum_congr rfl (fun i _=>(U.map_smul_univ (c:=fun j=>x (i j)) _).symm) -- syntax
lemma holdsW (A:Taylor G j): wheel (rootLeg A)=A:=by
     apply Taylor.value_ext; funext i x; conv_rhs => rw [← potential_recover A]
     rw [contracted_diag,whirls]; simp_rw [lived]
end YM.Arise.Range
