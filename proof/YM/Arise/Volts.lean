import YM.Arise.Slice
/-! # Ambient.Lin.Sym . all colors.Fibre roots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open Labels Maxwell
variable {r n m i j k d:ℕ}
variable {F M:Type*}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup M][NormedSpace ℝ M]
variable {G:Gauge}(a b:Axis)(p:PlaqAxes)(x:E4)
set_option quotPrecheck false
local notation "Cg"=>G.Color
noncomputable def wheelL (G:Gauge)(j:ℕ): (Proto j→ G.Color)→ₗ[ℝ] Taylor G j where
   toFun:=wheel
   map_add' u v := by
      apply Taylor.value_ext; funext a x
      have ht(z w:Axis)(s:Window j):scroll (G:=G) (u+v) z w s=scroll (G:=G) u z w s+scroll (G:=G) v z w s:=by
          unfold scroll; split; rfl; split; simp only [Pi.add_apply,neg_add]; exact zero_add _ |>.symm
      have hx(i): spanM (G:=G) (u+v) i a x=spanM (G:=G) u i a x+spanM (G:=G) v i a x:=by unfold spanM; simp_rw [ht,smul_add,sum_add_distrib]
      change Taylor.value (wheel _) _ _=Taylor.value (wheel _) _ _+Taylor.value (wheel _) _ _; simp_rw [whirls,hx,smul_add,sum_add_distrib,smul_add]
   map_smul' r u := by
      apply Taylor.value_ext; funext a x
      have ht(z w:Axis)(s:Window j):scroll (G:=G) (r • u) z w s=r • scroll (G:=G) u z w s:=by
          unfold scroll; split; rfl; split; simp; simp
      have hx(i) : spanM (G:=G) (r • u) i a x=r • spanM (G:=G) u i a x:=by unfold spanM; simp_rw [ht,smul_comm _ r, Finset.smul_sum]
      change Taylor.value (wheel _) _ _= r • Taylor.value (wheel _) _ _; rw [whirls,whirls]; simp_rw [hx,smul_comm _ r,← Finset.smul_sum]; exact smul_comm .. -- loops
section
-- motif assignments and read eq.S s.
variable (d G)
noncomputable def stripeJ (G:Gauge)(d i:ℕ)(X:Ink G d): Proto i →G.Color:= if hp:i ≤ d then (fun p=>WithLp.toLp 2 (fun a=> X (⟨⟨i,Nat.lt_succ_of_le hp⟩,p⟩,a))) else 0
noncomputable def scrim (G:Gauge)(d i:ℕ) : Ink G d →ₗ[ℝ] Proto i→ G.Color where
    toFun:=stripeJ G d i
    map_add' u v:= by unfold stripeJ; split; rfl; simp
    map_smul' r x:=by unfold stripeJ; split; rfl; simp
noncomputable def spinA (G:Gauge)(d:ℕ) (i:ℕ): Ink G d→ₗ[ℝ] Taylor G i:= (wheelL G i) ∘ₗ (scrim G d i)
noncomputable def phone (X:Ink G d): Jet G:= fun i=> spinA G d i X
noncomputable def pub (X : Jet G):Ink G d:=fun k=>rootLeg (X k.1.1.val) k.1.2 k.2
lemma minted (X:Jet G)(hp:i ≤ d): phone d G (pub d G X) i=X i:= by rw [phone, spinA, LinearMap.comp_apply]; rw [show scrim G d i (pub d G X)=rootLeg (X i) from (by unfold scrim; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [stripeJ,dif_pos hp]; rfl)]; exact holdsW ..
end
variable (L : G.Color→ₗ[ℝ]G.Color)
lemma strap (Y:Proto j→G.Color) (x: Window j): scroll (G:=G) (L∘Y) a b x=L (scroll (G:=G) Y a b x):=by unfold scroll; split; rfl; split; simp; simp
lemma plen(Y:Proto j→G.Color): spanM (G:=G) (L∘ Y) a b x=L (spanM (G:=G) Y a b x):=by unfold spanM; simp_rw [strap, map_sum,map_smul]
lemma pel(Y: Proto j→G.Color): Taylor.value (wheel (L∘Y)) a x=L (Taylor.value (wheel Y) a x):=by rw [whirls,whirls]; simp_rw [plen,map_smul,map_sum,map_smul]
variable (s:Signed)
noncomputable def swing (s : Signed)(p:Proto k): Proto k:= (took s p.1,s.perm ∘ p.2)
noncomputable def tiltZ (s:Signed)(Y: Proto k→ G.Color)(p:Proto k) : G.Color := petal s p.1 (List.ofFn p.2) • Y (swing s p)
lemma sw_add (u:Proto k)(i:Signed): swing s (swing i u)=swing (s*i) u:=by unfold swing; rw [took_mul]; rfl
lemma phase (w:Window k): (sways s (List.ofFn w))=List.ofFn (s.perm ∘ w):=by simp [sways]
lemma roan (w:Window j)(Y: Proto j→ G.Color): scroll (G:=G) (tiltZ s Y) a b w=(hue s a*hue s b*vane s (List.ofFn w)) • scroll (G:=G) Y (s.perm a) (s.perm b) (s.perm ∘ w):=by
     have ht (a b:Axis)(h:a<b):scroll (G:=G) (tiltZ s Y) a b w=(hue s a*hue s b*vane s (List.ofFn w)) • scroll (G:=G) Y (s.perm a) (s.perm b) (s.perm ∘ w):=by
         let p:PlaqAxes:=⟨(a,b),h⟩; let X:=s.perm a; let Z:=s.perm b; let f:=s.perm ∘ w; have he:= s.perm.injective.ne h.ne
         rw [scroll_next (G:=G) p]; unfold tiltZ; change petal s p _ • Y (swing s (p,w))= _; unfold swing petal glyphO; by_cases hp: X < Z 
         · change (vane _ _* ((if X < Z  then _ else _)*_*_)) • Y _= _ ; rw [scroll_next (G:=G) ⟨(X,Z),hp⟩ _ f, if_pos hp,one_mul,mul_comm]; exact congr_arg₂ (fun (u:ℝ)(x: G.Color)=> u • x) rfl (congr_arg Y (by change (took s p, f)=_; unfold took tw; rw [dif_pos hp]))
         have hv:Z < X := lt_of_le_of_ne (le_of_not_gt hp) he.symm
         change (vane _ _*((if X < Z  then _ else _)*_*_)) • Y _= _ ; rw [scroll_flip (G:=G) Z X Y,scroll_next (G:=G) ⟨(Z,X),hv⟩ _ f,if_neg hp,show took s p= ⟨(Z,X),hv⟩ from dif_neg hp]; simp only [neg_mul,one_mul,mul_neg,smul_neg,neg_smul]; rw [mul_comm] -- reducibility alignment
     rcases lt_trichotomy a b with h|h|h
     · exact ht a b h
     · subst b; simp [scroll]
     rw [scroll_flip b a (tiltZ s Y), ht b a h,scroll_flip]; rw [mul_comm (hue s b), smul_neg, neg_neg]
lemma s_elem (x:E4)(i:Axis): Ortho.move s.ortho x (s.perm i)=hue s i*x i:=by rw [Signed.ortho_move]; change s.act _ (s.perm i)=_; unfold hue; rw [Signed.act_at]; split<;> simp
lemma lights (u:Window k) : vane s (List.ofFn u)=∏ i,hue s (u i):=by rw [vane,List.map_ofFn,List.prod_ofFn]; rfl
lemma prose (Y:Proto k→G.Color): spanM (G:=G) (tiltZ s Y) a b x=(hue s a*hue s b) • spanM (G:=G) Y (s.perm a) (s.perm b) (Ortho.move s.ortho x):=by
     unfold spanM; rw [Finset.smul_sum]; refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin k)) s.perm) _ _ ?_
     intro i; rw [roan]; let f:=s.perm∘i; change (∏ j,x (i j)) • _= _ • (∏ j,Ortho.move s.ortho x (s.perm (i j))) • _; simp_rw [s_elem s,Finset.prod_mul_distrib, lights s i,smul_smul]; congr 1; ring
lemma signed_at (i : Axis): (s.ortho)⁻¹.val a i=if s.perm a=i then hue s a else 0:= Signed.matrix_at ..
lemma motes (Y:Proto j→G.Color): wheel (tiltZ s Y) = Taylor.turn (s.ortho)⁻¹ (wheel Y):=by
     apply Taylor.value_ext; funext a x; rw [Taylor.turn_value,inv_inv]; rw [sum_eq_single_of_mem (s.perm a) (mem_univ _) (fun i _ hi=>by rw [signed_at,if_neg (Ne.symm hi),zero_smul]),signed_at,if_pos rfl,whirls,whirls,smul_comm (hue s a)]; congr 1
     rw [smul_sum]; refine Fintype.sum_equiv s.perm _ _ ?_; intro i; rw [s_elem,prose]; simp only [smul_smul]; congr 1; ring
end YM.Arise.Range
#print axioms YM.Arise.Range.motes
