import YM.TorusPCAC.Jet.Filter

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # The color-contracted basis exhausts the sector

Use just a **sub**group for converse and *actual* su for admission earlier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet.Selector
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Set
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius

abbrev plus (a b : Hue) : ℂ := if a=b then 1 else -1
def flipM (a:Hue): Mat:= Matrix.diagonal (fun b=>plus a b)
lemma flipV (a: Hue) : star (flipM a)=flipM a:=by ext i j; by_cases h:i=j <;> by_cases he:a=j <;> simp [flipM, h, eq_comm,he, plus]
def flipColor (a:Hue) : su.El:=
 ⟨⟨flipM a, by
   have hu: flipM a*flipM a=1:=by ext i j; by_cases h:i=j <;> by_cases he:a=j <;> simp [flipM, Matrix.one_apply,plus,h,he] -- solve
   exact ⟨by change star (flipM a)*(flipM a)= (1:Mat); rw [flipV,hu], by change (flipM a)*star (flipM a)=(1:Mat); rw [flipV,hu]⟩ ⟩, by change (flipM a).det=(1:ℂ); rw [flipM,Matrix.det_diagonal]; fin_cases a <;> norm_num [plus, Hue,Fin.prod_univ_succ] <;> decide ⟩
def run (u : Hue) : Hue := u+1
def runM : Mat:= !![0,1,0;0,0,1;1,0,0]
lemma run_at (u v : Hue) : runM u v= if run u=v then 1 else 0:=by fin_cases u <;> fin_cases v <;> simp [runM, run] -- finmod
lemma run_at' (u v : Hue): star runM u v= runM v u:=by rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply, run_at v u]; split <;> simp
def runColor : su.El:=
  ⟨⟨runM, by
    constructor
    · change star runM * runM=(1:Mat); ext i j; fin_cases i <;> fin_cases j <;> norm_num [run_at',runM,Matrix.mul_apply,Fin.sum_univ_succ]
    change runM * star runM=(1:Mat); ext i j; fin_cases i <;> fin_cases j <;> norm_num [run_at',runM,Matrix.mul_apply,Fin.sum_univ_succ] ⟩, by change runM.det= (1:ℂ); simp [runM,Matrix.det_fin_three] ⟩

variable (i j : Flav) (u v : Pinor) (k l : Hue) (a b : Order)
lemma flip_eval (g:Hue) : paint (flipColor g) (element i j u v k l a b)=(plus g k*plus g l) • element i j u v k l a b:=by
  unfold element; rw [map_mul,paintL, paintR]; simp only [show su.mat (flipColor g)⁻¹=flipM g from (su.mat_inv _).trans (flipV g),show su.mat (flipColor g)=flipM g from rfl,flipM]; simp_rw [Matrix.diagonal_apply]; simp only [ite_smul,zero_smul,sum_ite_eq',sum_ite_eq,Finset.mem_univ, if_true];
  unfold plus; rw [← ite_smul,← ite_smul]; rw [smul_mul_smul_comm]
lemma run_eval : paint runColor (element i j u v k l a b)= element i j u v (run k) (run l) a b:=by
  unfold element; rw [map_mul,paintL,paintR]; simp only [show su.mat runColor⁻¹ = star runM from (su.mat_inv _),show su.mat runColor = runM from rfl,run_at',run_at]; simp [ite_smul]

def colorP : Pol →ₗ[ℂ] Pol:= (average 1 (paint (flipColor 0)).toLinearMap).comp (average 1 (paint (flipColor 1)).toLinearMap)
lemma color_eq : colorP (element i j u v k l a b)= if k=l then element i j u v k l a b else 0:=by
  let X:=element i j u v k l a b
  have hv (c : Hue) (h : plus c k*plus c l=1) : average 1 (paint (flipColor c)).toLinearMap X=X:= stays (V:=Pol) 1 1 (by norm_num) (by unfold X; rw [AlgHom.toLinearMap_apply, flip_eval,h])
  have hh (c : Hue) (h : plus c k*plus c l= -1) : average 1 (paint (flipColor c)).toLinearMap X=0:=sinks (V:=Pol) 1 (-1) (by norm_num) (by unfold X; rw [AlgHom.toLinearMap_apply, flip_eval,h])
  change colorP X = _; unfold colorP; rw [LinearMap.comp_apply]
  -- using HH
  by_cases he:k=l
  · rw [if_pos he]; rw [hv 1 (by rw [he]; unfold plus; split <;> simp),hv 0 (by rw [he]; unfold plus; split <;> simp)]
  rw [if_neg he];
  by_cases h: plus 1 k*plus 1 l= -1
  · rw [hh 1 h,map_zero]
  rw [hv 1 (by unfold plus at h ⊢; split_ifs at * <;> simp_all),hh 0 (by clear X hv hh; fin_cases k <;> fin_cases l <;> simp_all [plus])]

def closeP : Pol→ₗ[ℂ] Pol:= (3:ℂ)⁻¹ • (LinearMap.id + (paint runColor).toLinearMap +
  ((paint runColor).toLinearMap.comp (paint runColor).toLinearMap))

def coloredP := closeP.comp colorP
lemma close_eval : closeP (element i j u v k k a b)=(3:ℂ)⁻¹ • duo i j a b u v:=by
  simp only [closeP,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.smul_apply, LinearMap.id_apply,AlgHom.toLinearMap_apply,run_eval]; congr 1
  unfold duo; fin_cases k <;> simp [Fin.sum_univ_succ,Hue, run] <;> abel
lemma sector_color (g : Pol) (h : g∈invariant) : coloredP g=g:=by
  have ht: ∀ v, paint v g=g:=(paint_fixed g).1 h
  have hv (i : Hue) : average 1 (paint (flipColor i)).toLinearMap g=g:= stays (V:=Pol) 1 1 (by norm_num) (by rw [AlgHom.toLinearMap_apply,ht _,one_smul])
  simp only [coloredP,colorP, LinearMap.comp_apply, hv, closeP,LinearMap.add_apply,LinearMap.smul_apply, AlgHom.toLinearMap_apply,LinearMap.id_apply, ht]; rw [show g+g+g=(3:ℂ) • g by rw [show (3:ℂ)=2+1 by norm_num,add_smul,two_smul,one_smul],inv_smul_smul₀ (by norm_num)]
def channel (d : ℕ):= Submodule.span ℂ {x : Pol| ∃ u v a b, load a b ≤ d ∧ x=duo i j a b u v}
lemma enters {d : ℕ} (h:load a b≤d): duo i j a b u v∈channel i j d:= Submodule.subset_span (show ∃ _ _ _ _,_∧_ from ⟨u,v,a,b,h,rfl⟩)
lemma supported_color {d : ℕ} {x : Label d} (h:x.val∈sector i j d) : x.val∈channel i j d:=by
  have hp := x.property.2; rw [← sector_color _ hp]; refine Submodule.span_induction (p:=fun x _=> coloredP x∈ channel i j d) ?_ ?_ ?_ ?_ h
  · rintro z ⟨u,v,k,l,a,b,he,rfl⟩; rw [coloredP,LinearMap.comp_apply,color_eq]; split
    next ht=> subst l; rw [close_eval]; exact Submodule.smul_mem _ _ (enters i j u v a b he)
    simp
  · simp
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ _ ha
end YM.TorusPCAC.Jet.Selector

#print axioms YM.TorusPCAC.Jet.Selector.supported_color
