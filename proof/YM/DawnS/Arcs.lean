import YM.DawnS.Tum
import YM.Analysis.SmoothJets
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
noncomputable def align : Y→L[ℝ] E4:=∑ i : Fin 3, (((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord i).toContinuousLinearMap.smulRight (basis (i.castSucc)))
lemma align_base (a:Fin 3) : align (base a)=basis a.castSucc:=by unfold align; simp [base] -- check
lemma coordinates (y:Y)(a:Fin 3): align y a.castSucc=y a:=by unfold align; simp [basis,Pi.single_apply,mul_ite,Fin.castSucc_inj] -- 
lemma aperture (y:Y): align y timeAxis=0:=by unfold align; simp [basis]
lemma spaces (x:Y) :‖align x‖=‖x‖:=by
     apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : 2 ≠ (0:ℕ))).mp
     rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]; simp_rw [coordinates]; simp only [show align x (Fin.last 3)=0 from aperture x,zero_pow (by norm_num : 2 ≠ 0),add_zero]
-- moment of pure spatial symbol as real T.Data
variable (n:ℕ)
noncomputable def thetaT : MultilinearMap ℝ (fun _ : Fin n=>Y) ℝ where
     toFun x:=∫ y:P, ∏ i,thetaS (x i) y ∂Ω
     map_update_add' v i x y:=by
        let f(x:Y)(a:P):=∏ j:Fin n, thetaS ((Function.update v i x) j) a
        have ht(v :Y): Integrable (f v) Ω:=by
            refine (?h:Continuous (f v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); unfold f thetaS; fun_prop
        have hv(z:P): f (x+y) z=f x z+f y z:=by
            let L:MultilinearMap ℝ (fun _ : Fin n=>Y) ℝ:=( (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).toMultilinearMap).compLinearMap (fun _ : Fin n=> (innerSL ℝ z.val).toLinearMap)
            have h(x:Y) : f x z=L (Function.update v i x):=Finset.prod_congr rfl fun j _=> real_inner_comm ..; rw [h,h,h]; exact L.map_update_add ..
        change (∫ y:P, f (x+_) y ∂Ω)=_; simp_rw[hv]; exact integral_add (ht x) (ht y)
     map_update_smul' v i p x:=by
        let f(x:Y)(a:P):=∏ j:Fin n, thetaS ((Function.update v i x) j) a
        have hv(z:P): f (p • x) z=p * f x z:=by
            let L:MultilinearMap ℝ (fun _ : Fin n=>Y) ℝ:=( (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).toMultilinearMap).compLinearMap (fun _ : Fin n=> (innerSL ℝ z.val).toLinearMap)
            have h(x:Y) : f x z=L (Function.update v i x):=Finset.prod_congr rfl fun j _=> real_inner_comm ..; rw [h,h]; exact L.map_update_smul ..
        change (∫ y:P, f (p • x) y ∂Ω)=_; simp_rw[hv]; exact integral_const_mul ..
noncomputable def wheel : T Vertex ℝ n := (thetaT n).mkContinuous (muS.real Set.univ) (fun x=>by
     let Pv(v:Y)(y:RingS):=thetaS v y; let f(y:RingS):= ∏ i,Pv (x i) y -- local P token collision clean
     suffices h: ‖∫ y, f y ∂muS‖ ≤ (muS.real Set.univ) * ∏ i,‖x i‖ from h
     have hv : ∀ y:P,‖f y‖≤∏ i, ‖x i‖:=by intro y; unfold f; rw[norm_prod]; exact Finset.prod_le_prod (fun i _=> norm_nonneg _) fun i _=> (norm_inner_le_norm (x i) y.val).trans_eq (by rw[flash,mul_one])
     exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hv)).trans_eq (mul_comm ..) -- signature
    )
lemma wired : Sym (wheel n):=by
     intro v s; change (∫ y:P, ∏ i:Fin n, thetaS (v (s i)) y ∂Ω)=∫ y:P, ∏ i:Fin n,thetaS (v i) y ∂Ω; exact integral_congr_ae (Eventually.of_forall fun z=>(Fintype.prod_equiv s _ _ (fun _=>rfl)))
lemma whirl(x:Y): wheel n (fun _=>x)=surf n x:=by change (∫ y:P, ∏ _i : Fin n, thetaS x y ∂Ω)=_; simp only[prod_const,card_univ,Fintype.card_fin]; rfl
-- pullback iteration diagonal
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma sloped (f:E→F)(x v:E)(hf:ContDiffAt ℝ n f x) : iteratedFDeriv ℝ n f x (fun _=> v)= iteratedDeriv n (fun t:ℝ=> f (x+t • v)) 0:=by
   -- recurse. translation all t at once
   suffices h : ∀ (t:ℝ),ContDiffAt ℝ n f (x+t • v)→ iteratedFDeriv ℝ n f (x+t • v) (fun _=>v)= iteratedDeriv n (fun t:ℝ=> f (x+t • v)) t by simpa using h 0 (by simpa)
   clear hf; intro t ht; induction n generalizing f t with
   | zero=>simp
   | succ n ih=>
       rw [show (fun _ : Fin (n+1) => v)=Fin.cons v (fun _=>v) by ext1 i; refine Fin.cases ?_ (fun j=> ?_) i <;> simp,Analysis.cons_inner ht]; rw [iteratedDeriv_succ'] -- peels f? need D relation
       let A(u:ℝ):=x+u • v
       have hx (t:ℝ)(hd:DifferentiableAt ℝ f (A t)): Analysis.D v f (A t)=deriv (f ∘ A) t:=by
          have he : HasDerivAt A v t:=by unfold A; simpa using (((hasDerivAt_id' t).smul_const v).const_add x)
          exact (hd.hasFDerivAt.comp_hasDerivAt t he).deriv.symm
       have h : ContDiffAt ℝ n (Analysis.D v f) (x+t • v):= dSmooth ht v (by norm_cast) -- check
       rw [ih _ t h]; refine Filter.EventuallyEq.iteratedDeriv ?he n |>.eq_of_nhds
       change (Analysis.D v f)∘A=ᶠ[𝓝 t] deriv (f∘A)
       have hz: ∀ᶠ y in 𝓝 t, DifferentiableAt ℝ f (A y):= ((show Continuous A by unfold A; fun_prop).continuousAt).tendsto.eventually ((ht.eventually (by simp)).mono fun i h=> h.differentiableAt (by norm_cast))
       exact hz.mono hx -- signature
end YM.DawnS
