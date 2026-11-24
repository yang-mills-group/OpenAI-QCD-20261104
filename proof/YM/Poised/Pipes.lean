import YM.Poised.Gem
/-!
# Spin-chart actions. Matrices *into* exterior valuation, BOTH ends already AP, arbitrary actual endpoint spaces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {A J E B : Type}{d a l k n:ℕ}{c:Side}
namespace Pipes
abbrev Shell := Pairs (Lat.Fiber×Flavor 6)
abbrev Faces (A:Type):= Pairs ((A × Lat.Fiber)×Flavor 6)
abbrev VectorD (A B: Type):= Faces A → B→ℂ
abbrev Flet (B: Type):= Shell → B→ℂ
abbrev Lugs (d:ℕ)(B: Type):= UV.Multi d → Flet B
def stretch (A:Type) : (A × Shell) ≃ Faces A where
   toFun i:= Sum.elim (fun x=> Sum.inl ((i.1,x.1),x.2)) (fun x=> Sum.inr ((i.1,x.1),x.2)) i.2
   invFun i := Sum.elim (fun x=> (x.1.1,Sum.inl (x.1.2,x.2))) (fun x=> (x.1.1,Sum.inr (x.1.2,x.2))) i
   left_inv | ⟨_,.inl _⟩ | ⟨_,.inr _⟩ => rfl
   right_inv | .inl _ | .inr _ => rfl
def flats (f: A → Flet B):VectorD A B:=fun i=> let x:=(stretch A).symm i; f x.1 x.2
def asks (v:VectorD A B)(b:A): Flet B:=fun i=> v (stretch A (b,i))
lemma invers (f:A→Flet B): asks (flats f)=f:=by funext b i; simp only [asks,flats,Equiv.symm_apply_apply]
lemma jointly (f: VectorD A B): flats (asks f)=f:=by funext b; unfold asks flats; dsimp only; rw [Prod.eta,Equiv.apply_symm_apply]
lemma flat_ext {v w:VectorD A B} (he:∀ i,asks v i=asks w i): v=w:=by rw [← jointly v,← jointly w,funext he]
-- smooth row notation: use Pi norms on actual VectorD
variable [Fintype A][Fintype B]
def askCL (a:A) : VectorD A B →L[ℝ] Flet B := LinearMap.toContinuousLinearMap { toFun:=fun v=> asks v a,map_add':=fun v w=>rfl,map_smul':=fun r u=>rfl }
variable {P S: Type} [Fintype P][NormedAddCommGroup S][NormedSpace ℝ S]
-- smooth regardless truncation in application
lemma analytic_maps (Y:Alg P) : ContDiff ℝ ω (fun v:P→B→ℂ=> changeVars v Y):=by
   -- use expression factor
   rw [← write Y]; simp_rw [map_sum,map_smul]; have he(i:P): ContDiff ℝ ω (fun v:P→B→ℂ=> changeVars v (atom i)):=by simp_rw [change_atom]; fun_prop
   have h (L : List (Alg P))(H:∀ i∈L,ContDiff ℝ ω fun v:P→ B→ℂ=>changeVars v i): ContDiff ℝ ω fun v:P→B→ℂ=> changeVars v L.prod:=by
      induction L with
      | nil =>simp [contDiff_const]
      | cons p l ih=> simp_rw [List.prod_cons,map_mul]; exact (H p (by simp)).mul (ih fun i hi=>H i (by simp [hi]))
   have ht (i:Finset P): ContDiff ℝ ω (fun v:P→B→ℂ=> changeVars v (mono i)):=by
      obtain ⟨V,hV,H,hT⟩:= expression i; rw [hT]; refine h _ ?_; intro j hj; obtain ⟨q,hq⟩:= List.mem_ofFn.mp hj; rw [← hq]; exact he _
   have hh' i: ContDiff ℝ ω (fun v:P→B→ℂ=> coef i Y • changeVars v (mono i)):= (show ContDiff ℝ ω (fun _:P→B→ℂ=> coef i Y) from contDiff_const).smul (ht i)
   exact ContDiff.sum fun i _=>hh' i
lemma aperture (F:S→Alg P)(J:S→P→B→ℂ)(s:S)(r:WithTop ℕ∞)(hf:ContDiffAt ℝ r F s)(h:ContDiffAt ℝ r J s): ContDiffAt ℝ r (fun y=>changeVars (J y) (F y)) s:=by
   rw [show (fun y=>changeVars (J y) (F y))=(fun y=> ∑ i:Finset P,coef i (F y) • changeVars (J y) (mono i)) from funext fun y=>by
      conv_lhs=>arg 2; rw [← write (F y)];
      simp]
   apply ContDiffAt.sum -- name
   intro i _; exact (((coef i).restrictScalars ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp _ hf).smul ((((analytic_maps (B:=B) (mono i)).of_le le_top).contDiffAt).comp _ h)
-- statement G action
abbrev signs {c:Side}(g: Frame c) : VectorD (Site c) (Faces (Site c)):= Matrix.fromBlocks (Lat.rotates 6 g) 0 0 (star (Lat.rotates 6 g)).transpose
abbrev hailC(g:Frame c)(v:VectorD (Site c) B):VectorD (Site c) B:= let M: Matrix _ _ ℂ:=signs g;let N:Matrix (Faces (Site c)) B ℂ:=v;M*N
private abbrev table (u: su.Mat): Shell→Shell→ℂ:= Matrix.fromBlocks (copies 6 (touch (show QCD.Mat from u))) 0 0 (star (copies 6 (touch (show QCD.Mat from u)))).transpose
private lemma orbits (u v :Lat.Fiber×Flavor 6)(b i:Site c)(g:Frame c): Lat.rotates 6 g ((b,u.1),u.2) ((i,v.1),v.2) = if i=b then copies 6 (touch (Lat.colour (g b))) u v else 0:=by
   by_cases hi:i=b <;> by_cases hh:u.2=v.2 <;> simp [Lat.rotates,siteRot,copies,hh,hi,Matrix.blockDiagonal_apply,rides,eq_comm] <;> grind
private lemma sign_rows (u v: Shell)(i j: Site c)(g:Frame c): signs g (stretch (Site c) (i,u)) (stretch _ (j,v))= if j=i then table (su.mat (g i)) u v else 0:=by
   by_cases he:j=i
   · subst j; cases u <;> cases v <;> simp only [signs, table, if_pos rfl, stretch,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.star_apply, orbits]; all_goals first | rfl | (simp [Lat.colour])
   cases u <;> cases v <;> simp only [signs, table, if_neg he, stretch,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.star_apply, orbits] <;> simp [he,Ne.symm he]
def stepF (u:su.Mat)(v:Flet B):Flet B:= fun i j=>∑ k:Shell,table u i k * v k j
lemma hailF (g:Frame c)(v:VectorD (Site c) B)(b:Site c): asks (hailC g v) b=stepF (su.mat (g b)) (asks v b):=by
   funext i j; unfold hailC asks; rw [Matrix.mul_apply,← Equiv.sum_comp (stretch _), Fintype.sum_prod_type]; simp_rw [sign_rows]; rw [Finset.sum_eq_single b]; · simp [stepF]
   · intro k _ hk; simp [hk]
   simp
abbrev scaleG (q: su.Color × Flet B) :=stepF (su.mat (su.lieExp q.1)) q.2
private lemma smoothTable (i j:Shell): ContDiff ℝ ω (fun u:su.Color=> table (su.mat (su.lieExp u)) i j):=by
   -- table nonstar L linear
   let W(y:su.Mat) := copies 6 (touch (show QCD.Mat from y))
   have h(p q:Lat.Fiber×Flavor 6): ContDiff ℝ ω (fun u:su.Color=> W (su.mat (su.lieExp u)) p q):=by
      unfold W Lat.copies; simp only [Matrix.blockDiagonal_apply]; split; swap; · exact contDiff_const
      have hh(i j:Lat.Fiber) : ContDiff ℝ ω (fun u:su.Color=> touch (show QCD.Mat from su.mat (su.lieExp u)) i j):=by
          -- clm
          let L:QCD.Mat→ₗ[ℝ]ℂ:={ toFun:=fun y=> touch y i j,map_add':=fun y z=>by rw [← touch_add]; rfl,map_smul':=fun r y=>by change touch (r • y) i j=r • touch y i j; unfold touch; rw [Matrix.kronecker_smul]; rfl }
          exact L.toContinuousLinearMap.contDiff.comp su.exp_jet
      exact hh ..
   cases i <;> cases j <;> simp only [table,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.star_apply]; exact h ..; exact contDiff_const; exact contDiff_const; exact ((starL' ℝ : ℂ≃L[ℝ]ℂ).contDiff).comp (h _ _)
lemma scaleG_live : ContDiff ℝ ω (scaleG (B:=B)):=by
   apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j; unfold scaleG stepF; exact ContDiff.sum fun k _=> ((smoothTable i k).comp contDiff_fst).mul (by fun_prop)
lemma step_one (x:Flet B) : stepF 1 x=x:=by
   funext i j; have he : table 1 = (1: Matrix Shell Shell ℂ) :=by change Matrix.fromBlocks (copies 6 (touch 1)) 0 0 (star (copies 6 (touch 1))).transpose= (1:Matrix Shell Shell ℂ); rw [touch_one,copies_one,star_one,Matrix.transpose_one]; exact Matrix.fromBlocks_one
   unfold stepF; rw [he]; simp [Matrix.one_apply]
lemma step_right (u:su.Mat)(p:ℂ)(x:Flet B): stepF u (p • x)=p • stepF u x:=by
   funext i j; unfold stepF; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; exact sum_congr rfl fun k _=> mul_left_comm ..
lemma forfeit (u:su.Color): scaleG (B:=B) (u,0)=0:=by funext i j; simp [scaleG,stepF]
lemma scaleG_first (u: su.Color × Flet B) : fderiv ℝ scaleG 0 u= u.2:=by
   let L:= fderiv ℝ (scaleG (B:=B)) 0; rw [show u=(u.1,0)+(0,u.2) from by simp, map_add]
   let K := ContinuousLinearMap.inl ℝ su.Color (Flet B); let V:= ContinuousLinearMap.inr ℝ su.Color (Flet B)
   have h : L (u.1,0)=0 :=by
       have hz: scaleG ∘ K=(fun _=>0):=funext forfeit
       have hg : Differentiable ℝ (scaleG (B:=B)):=scaleG_live.differentiable (by simp)
       rw [show L (u.1,0)=(L.comp K) u.1 from rfl, show L.comp K=fderiv ℝ (scaleG ∘ K) 0 from ?_,hz]; simp
       rw [fderiv_comp (x:=0) (hg _) K.differentiableAt, K.fderiv,map_zero]
   have h1:L (0,u.2)=u.2:=by
       have hz:scaleG ∘ V=id:=funext fun i=>by change stepF (B:=B) (su.mat (su.lieExp 0)) i=i; simp [step_one]
       have hg : Differentiable ℝ (scaleG (B:=B)):=scaleG_live.differentiable (by simp)
       have he : L.comp V=fderiv ℝ (scaleG (B:=B) ∘ V) 0:=by rw [fderiv_comp (x:=0) (hg _) V.differentiableAt, V.fderiv,map_zero]
       change L (V u.2)=u.2; rw [← ContinuousLinearMap.comp_apply,he,hz, fderiv_id]; rfl
   change L (u.1,0)+L (0,u.2)=_; rw [h,h1]; simp
end Pipes
end YM.Massive.Poised
