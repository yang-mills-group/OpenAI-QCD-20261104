import YM.Bank.Merchant
/-! budgets cumulative rows. unopened cov both-core. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Avalon
open Matrix Wilson Lattice Precision Exterior RG Function Finset Filter
open Laurent Bloch Next.Free Learn Knot Merchant
open AnalyticBridge.LocalGaussianLaws.Current
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators ComplexConjugate InnerProductSpace
variable {c f:Side} {n m M N:Type}{i j:ℕ}
section Orbit
variable (c n) [Fintype n][DecidableEq n]
def lever (s: Axis) : Matrix (Co c n) (Co c n) ℝ:=of fun i j=>if j=(i.1+step s,i.2) then 1 else 0
def rocker : List Axis→ Matrix (Co c n) (Co c n) ℝ
   | []=> 1
   | i::l=> (lever c n i-1)*rocker l
variable {c n}
lemma lift_roller (K:Matrix (Co c n) M ℝ) (i:Axis)(x:Site c)(a:n)(v:M): ((lever c n i-1)*K : Matrix (Site c × n) M ℝ) (x,a) v = K (x+step i,a) v-K (x,a) v:= by rw [Matrix.sub_mul,Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]; simp [lever,ite_mul]
lemma stands (A:Matrix (Co c n) (Co c n) ℝ) (Q: Matrix (Co c n) M ℂ) (l: Axis): approached (((lever c n l-1)*A))*Q=approached (lever c n l-1)*(approached A*Q):=by rw [prom_mul,Matrix.mul_assoc]
lemma hops (A:Matrix (Co c n) M ℂ)(i:Axis)(x:Site c)(a:n)(j:M): (approached (lever c n i-1)* A : Matrix (Site c×n) M ℂ) (x,a) j=A (x+step i,a) j-A (x,a) j:=by rw [show approached (lever c n i-1)=approached (lever c n i)-1 by ext i j; by_cases h:i=j <;> simp [*,approached,Matrix.one_apply],Matrix.sub_mul,Matrix.one_mul, Matrix.sub_apply,Matrix.mul_apply]; simp [approached,lever,ite_mul,apply_ite ((↑):ℝ→ℂ)]
-- stencil factor on ANY plane kernels
lemma rock_formula (X:Matrix (Co c n) (Co f M) ℝ)(T: Matrix (Co f M) N ℂ) [Fintype M] [Fintype m]
     (G:N→m→Site c)(A:n→N→m→ℂ) (h: ∀ x a b,(approached X*T) (x,a) b=∑ i,cell (G b i) x*A a b i) (l:List Axis) (x:Site c)(a:n)(b:N):
      (approached (rocker c n l *X)*T) (x,a) b=∑ i,listChip (mon (G b i)) l * cell (G b i) x * A a b i:=by
      induction l generalizing x with
      | nil=>simp[rocker,listChip,h]
      | cons i l ih=> rw [rocker,Matrix.mul_assoc, prom_mul,Matrix.mul_assoc,hops]; simp_rw [ih,←sum_sub_distrib]; apply sum_congr rfl; intro w _; rw [cell_add]; have ht j: cell (n:=c) j (step i)= chip (mon j i)+1:=by rw [← wrap_step c,cell_wrap,Exterior.factor]; unfold chip; rw [sub_add_cancel]; -- check
                      rw [ht]; simp only [listChip,List.map_cons,List.prod_cons]; ring
lemma rock_same (r:List Axis) (x:Site c)(i:n)(p:Site c)(j:n): (approached (rocker c n r)*rotations c n) (x,i) (p,j) = listChip (mon p) r*rotations c n (x,i) (p,j):=by
     induction r generalizing x with
     | nil=> rw [rocker,show approached (1:Matrix (Co c n) (Co c n) ℝ)=1 by ext a b; by_cases h:a=b <;>simp [h,approached,Matrix.one_apply]]; simp [listChip]
     | cons a s ih=> rw [rocker,prom_mul,Matrix.mul_assoc,hops]; simp_rw [ih]; simp only [rotations,Matrix.of_apply,listChip,List.map_cons,List.prod_cons]; split; next _=> rw [cell_add]; rw [←wrap_step c,cell_wrap,Exterior.factor]; unfold chip; ring -- location line
                     simp
end Orbit

namespace Worth
variable {r:Ratio c f}{B F:Bed}{J Q R}
local notation "θ"=>TypeFace 2
lemma stage (x:TowerW j r F B J R Q)(hF:F.metric.safe)(hB:B.metric.safe){a b:ℝ}(hw:Numeric (F.metric.acts f) a b)(ha:0<a)(X:Site f)(i:θ)(p:Site c)(A:TypeFace 1) :
     (approached (J*d 1 c)*rotations c (TypeFace 1)) (X,i) (p,A)=∑ l:Site r.count, cell (QCD.Flume.twins r p l) X * crow j r B F (mon p) l i A:=by
   rw [show approached _ * _=readings _ _* solo _ _ from tech x hF hw ha hB,Matrix.mul_apply,Fintype.sum_prod_type]
   rw [sum_eq_single p]; · apply Eq.trans (Fintype.sum_prod_type ..); simp_rw [twin_leaf _ x.odd]; simp [solo,fiber, rot_fiber,rotations,downAlias, ite_mul]
   · intro j _ hj; simp [solo,fiber,hj]
   simp
lemma stages (x:TowerW j r F B J R Q)(hF:F.metric.safe)(hB:B.metric.safe){a b:ℝ}(hw:Numeric (F.metric.acts f) a b)(ha:0<a)(u:List Axis)(X:Site f)(i:θ)(p:Site c)(A:TypeFace 1) :
     (approached (rocker f θ u * (J*d 1 c))*rotations c (TypeFace 1)) (X,i) (p,A)=∑ l:Site r.count,listChip (aliasAt (mon p) l) u * cell (QCD.Flume.twins r p l) X * crow j r B F (mon p) l i A:=by
   simp_rw [← twin_mon r x.odd]; exact rock_formula (J*d 1 c) _ (fun (b:Co c (TypeFace 1)) i=> QCD.Flume.twins r b.1 i) (fun a b l=>crow j r B F (mon b.1) l a b.2) (fun x' a b=> stage x hF hB hw ha ..) u ..
local notation "N"=> (Fintype.card (TypeFace 1):ℝ)
lemma mother_volume (c:Side): ∑ _x: Site c, |(c.val:ℝ)^4|⁻¹ = 1:=by simp only [sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow,abs_of_pos (pow_pos (side_pos c) _), mul_inv_cancel₀ (pow_ne_zero _ (side_pos c).ne')]
lemma unit_cell (x a:Site c):‖cell a x‖=1:= mode_real _ _ (real_frequency a) -- inspect
lemma pose (a b:ℝ)(ha:0<a)(hb:0≤b)(j:ℕ)(u:List Axis)(hu:u.length+2≤j): ∃ C:ℝ,0 ≤ C∧∀ {c f:Side} (r:Ratio c f)(F B:Bed) {J Q R} (b':ℝ), TowerW j r F B J R Q→ F.metric.safe → (∃ z:ℝ,0 ≤ z∧ B.metric.strip z b)→ Numeric (F.metric.acts f) a b'→ ∀ X i p A, ‖(approached (rocker f θ u*(J*d 1 c))*rotations c (TypeFace 1)) (X,i) (p,A)‖ ≤ C*‖mon p‖/(r.count.val:ℝ)^(2+u.length):=by
   obtain ⟨C,hc,H⟩:= Merchant.currency a b ha hb j; obtain ⟨D,hD,K⟩:=decay_cost; have hs := μpos
   refine ⟨C*D*μ^u.length,by positivity,fun {c f} r F B {J Q R} b' h hF ⟨z,hz,hB⟩ ht X i p A=>?_⟩

   let w : ℝ:= r.count.val; let e:=2+u.length
   let W:= C*μ^u.length*‖mon p‖/w^e; have hw: 0 < w:=side_pos _; have hW: 0≤W:=by unfold W; positivity
   rw [stages h hF (Row.rights _ _ hB hz) ht ha u]; apply (norm_sum_le ..).trans
   calc
     _ ≤ ∑ l:Site r.count, decay 2 l * W:=by
       apply sum_le_sum; intro l _
       rw [norm_mul,norm_mul,unit_cell,mul_one]

       have hm := QCD.Cost.north (crow j r B F (mon p) l) i A|>.trans (H _ _ _ b' h.odd hF ⟨z,hz,hB⟩ ht p l)
       have hm':= Merchant.distance (mon_mem _ p) l h.odd u
       refine (mul_le_mul hm' hm (norm_nonneg _) ((norm_nonneg _).trans hm')).trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_trans (a:=grade l ^ u.length * decay j l) ?_ (absorbs l u.length 2)) hW))
       · change _ = grade l ^ u.length * decay j l * W; unfold W w e; rw [pow_add]; ring
       exact mul_le_mul_of_nonneg_left (decay_anti l (by omega)) (pow_nonneg (grade_pos l).le _)
     _ ≤ D*W:=by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (K _) hW
     _ = _:=by unfold W w e; ring
lemma column_bound {n m:Type}[Fintype m][Fintype n][DecidableEq n](A:Matrix m (Site c × n) ℂ)(a:ℝ)
    (ha:0≤a)(h : ∀ i j, ‖(A*rotations c n) i j‖ ≤ a) (i:m)(j:Site c×n) : ‖A i j‖≤ (Fintype.card n:ℝ)*a :=by
    let k := stageVolume c; let F:=rotations c n; have ht : A=k⁻¹ •(A*F*Fᴴ):=by rw [Matrix.mul_assoc,(show F*Fᴴ=k • 1 from (rotations_crew ..).2.1),Matrix.mul_smul,Matrix.mul_one,smul_smul,inv_mul_cancel₀ (stage_ne _),one_smul]
    nth_rw 1 [ht]; rw [Matrix.smul_apply,norm_smul,Matrix.mul_apply]; have hh:= norm_sum_le univ (fun x: Site c×n=>(A*F) i x*Fᴴ x j)
    apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans
    have hy v: ‖Fᴴ v j‖ ≤ 1:=by rw [conjTranspose_apply,norm_star]; unfold F rotations; rw [of_apply]; split; rw [unit_cell]; simp
    apply (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=> a) fun v _=>?_) (norm_nonneg _)).trans
    · simp [k,stageVolume, site_card]; have hh := side_pos c; field_simp; linarith
    rw [norm_mul]; exact (mul_le_mul (h i _) (hy _) (norm_nonneg _) ha).trans_eq (mul_one _)

lemma axial (a b:ℝ)(ha:0<a)(hb:0≤b)(j:ℕ)(u:List Axis)(hu:u.length+2≤j): ∃ C:ℝ,0 ≤ C∧∀ {c f:Side} (r:Ratio c f)(F B:Bed) {J Q R} (b':ℝ), TowerW j r F B J R Q→ F.metric.safe → (∃ z:ℝ,0 ≤ z∧ B.metric.strip z b)→ Numeric (F.metric.acts f) a b'→ ∀ X i, ‖(rocker f θ u*(J*d 1 c)) X i‖ ≤ C/(r.count.val:ℝ)^(2+u.length):=by
   obtain ⟨C,hc,H⟩:= pose a b ha hb j u hu
   refine ⟨N*(C*Real.pi),by positivity,fun {c f} r F B {J Q R} b' h hF hG hz X i=>?_⟩
   let M:= approached (rocker _ θ u*(J*d 1 c)); let f := (r.count.val:ℝ)
   let w:= C* Real.pi / f^(2+u.length); have hw:0 ≤ w:=by unfold w f; positivity
   have hk (i j): ‖(M*rotations c (TypeFace 1)) i j‖≤ w:= (H _ _ _ _ h hF hG hz i.1 i.2 j.1 j.2).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (QCD.Pearl.cap_base (mon_mem _ _)) hc) (pow_pos (side_pos r.count) _).le)
   rw [← Complex.norm_real]; exact (column_bound M w hw hk X i).trans_eq (by unfold w f; ring)
end Worth
end YM.Bank.Avalon
#print axioms YM.Bank.Avalon.Worth.axial
#print axioms YM.Bank.Avalon.rock_same
