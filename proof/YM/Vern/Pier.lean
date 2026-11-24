import YM.Vern.City
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Filter Set
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
variable {W:Type*}[NormedAddCommGroup W][InnerProductSpace ℂ W][FiniteDimensional ℂ W]
-- Fixed Hilbert surface. build positive cross. Any transversal skew P and signed simultaneous commute
local notation "S"=>Module.End ℂ W
local notation "G"=>inner ℂ
lemma coins(D:Tide W):∃ P:Module.End ℂ W, P.IsSymmetric ∧ ∀ v w:W,D.knot v w=inner ℂ (P v) w:=by
     let B:=stdOrthonormalBasis ℂ W
     let F(i:Fin (Module.finrank ℂ W)):W:=∑ j, star (D.knot (B i) (B j)) • B j
     let P:S:= B.toBasis.constr ℂ F
     have h(i:Fin _)(w:W) : G (P (B i)) w=D.knot (B i) w:=by
          have he(j:Fin _): G (P (B i)) (B j)= D.knot (B i) (B j):=by
               rw[show P (B i)=F i from B.toBasis.constr_basis _ _ _, show G (F i) (B j)=∑ l:Fin _,G (star (D.knot (B i) (B l)) • B l) (B j) from sum_inner ..]; have hx:= orthonormal_iff_ite.mp B.orthonormal
               rw[Finset.sum_eq_single j]; · rw [inner_smul_left,hx]; simp
               · intro v _ hv; rw [inner_smul_left,hx]; simp [hv]
               simp
          change G (P (B i)) w= D.zz _ w; rw[← B.toBasis.sum_repr w]; simp_rw[inner_sum, _root_.map_sum,map_smul, inner_smul_right]; exact Finset.sum_congr rfl fun j _=>congr_arg (fun x:ℂ=> B.toBasis.repr w j*x) (he j)
     have ht(v w:W): D.knot v w= G (P v) w:=by
          rw [← D.con w v]; change star (D.zz w v)=_; rw[← B.toBasis.sum_repr v]; simp_rw[_root_.map_sum,map_smul, star_sum,sum_inner,inner_smul_left]; apply Finset.sum_congr rfl; intro i _; change star (_ * (D.knot _ _))= _*_; rw [star_mul', D.con]; exact congr_arg (fun x:ℂ=> star (B.toBasis.repr v i)*x) (h i w).symm
     exact ⟨P,fun x y=> Eq.trans (ht x y).symm (Eq.trans (D.con y x).symm (by rw [ht]; exact inner_conj_symm _ _)),ht⟩ -- order orientation?
-- proof commuting: if P commutes R, applying unscale Q sharing eigenframes.
open LinearMap Module
lemma barG (D:Tide W)(P:S)(h:P.IsSymmetric)(hx:∀ v w:W,D.knot v w= G (P v) w):∃ E:W≃ₗ[ℂ]W, (∀ v w,D.knot (E v) (E w)=G v w)∧ (∀ F:Module.End ℂ W,(∀ x,P (F x)= F (P x)) → ∀ v,E (F v)=F (E v)):=by
     let d:=Module.finrank ℂ W
     let B:= h.eigenvectorBasis (n:=d) rfl
     let g:= h.eigenvalues (n:=d) rfl
     have he(i:Fin d):P (B i)= (g i:ℂ) • (B i):=End.mem_eigenspace_iff.mp (h.hasEigenvector_eigenvectorBasis rfl i).1
     have hO := orthonormal_iff_ite.mp B.orthonormal -- check
     have hg(i:Fin d)(j:Fin d): D.knot (B i) (B j)= if i=j then (g i:ℂ) else (0:ℂ):=by rw [hx,he,inner_smul_left,hO]; split <;> simp [*]
     have hr(i:Fin d):0<g i:=by have hh:= D.positive (B i) (show B i≠0 from B.toBasis.ne_zero i); rw [hg,if_pos rfl,Complex.ofReal_re] at hh; exact hh
     let f(i:Fin d):ℝ:=(Real.sqrt (g i))⁻¹; let F:= B.toBasis.constr ℂ (fun i=> (f i:ℂ) • (B i)); have hV(i):F (B i)= (f i:ℂ) • B i:= B.toBasis.constr_basis _ _ _
     have ht(i:Fin d)(j:Fin d): D.knot (F (B i)) (F (B j))= G (B i) (B j):=by
           rw[hV,hV,D.seals,D.sep,hg,hO]; by_cases H:i=j
           · subst j; simp only [if_pos rfl, Complex.star_def,Complex.conj_ofReal]; have hx:f i*(f i*g i)=1:=by unfold f; have he:=Real.sqrt_pos.2 (hr i); field_simp; rw [Real.sq_sqrt (hr i).le]
             simp only[↓reduceIte]; rw[← Complex.ofReal_mul,← Complex.ofReal_mul,hx,Complex.ofReal_one]
           simp only[if_neg H,mul_zero,mul_zero]
     have H(x y:W) : D.knot (F x) (F y)=G x y:=by
          have hL(i:Fin d): D.knot (F (B i)) (F y)= G (B i) y:=by change D.zz _ (F _)=_; rw[← B.toBasis.sum_repr y]; simp_rw [_root_.map_sum,inner_sum,_root_.map_smul,inner_smul_right]; apply Finset.sum_congr rfl; intro j _; exact congr_arg (fun s:ℂ=> B.toBasis.repr y j • s) (ht i j)
          rw [← D.con,← B.toBasis.sum_repr x]; simp_rw [_root_.map_sum, sum_inner]; change star (D.zz _ _)= _; simp_rw[_root_.map_sum,star_sum,_root_.map_smul,inner_smul_left]; apply Finset.sum_congr rfl; intro j _; change star (_ * D.knot _ _)= _*_; rw [star_mul', D.con]; exact congr_arg (fun s:ℂ=> star (B.toBasis.repr x j)*s) (hL j)
     have H':Injective F:= LinearMap.ker_eq_bot.mp (bot_unique fun x hx=> by have he:= H x x; rw [show F x=0 from hx, D.zero'] at he; exact (inner_self_eq_zero (𝕜:=ℂ)).mp he.symm)
     refine ⟨LinearEquiv.ofBijective F ⟨H',LinearMap.surjective_of_injective H'⟩,H,fun X hX x=>?_⟩
     have hΩ(i:Fin d): F (X (B i)) = X (F (B i)):=by
           rw[hV,_root_.map_smul]; let u:= X (B i); have hz:P u= (g i:ℂ) • u:=by unfold u; rw[hX,he,_root_.map_smul]
           change F u= (f i:ℂ) • u
           rw[←B.toBasis.sum_repr u,_root_.map_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; let q:=B.toBasis.repr u j; change F (q • B j)=(f i:ℂ) • (q • B j); rw [_root_.map_smul,hV, smul_comm q]; by_cases heq:g i=g j; rw [show f i=f j from congr_arg (fun z:ℝ=>(Real.sqrt z)⁻¹) heq]
           have hj : G (B j) u=0:=by
                have hk:= h (B j) u; rw [hz,he,inner_smul_right,inner_smul_left] at hk; have h:↑(g j)* G (B j) u=(g i:ℂ)* G (B j) u:=by simpa using hk
                by_contra hh; exact Ne.symm heq (Complex.ofReal_injective (mul_right_cancel₀ hh h))
           have ht:q=0:=by unfold q; rw [←B.repr_apply_apply _ _] at hj; exact hj
           rw[ht,zero_smul,smul_zero,smul_zero]
     change (F ∘ₗ X) x=(X ∘ₗ F) x; exact DFunLike.congr_fun (B.toBasis.ext (fun i=> hΩ i)) x
end YM.Vern
#print axioms YM.Vern.coins
#print axioms YM.Vern.barG
