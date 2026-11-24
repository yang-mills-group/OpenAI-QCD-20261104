import YM.QCD.Stew.Life
/-! # common stabilizer on SU3. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}
-- 1 U diagonal w three distinct; one cyclic
private def violet : Mat:= Matrix.diagonal (![1,Complex.I,-Complex.I])
private def rotary : Mat:= !![0,1,0; 0,0,1; 1,0,0]
private lemma plucks (A:Mat)(h:A∈unitary _)(hp:A.det=1): ∃ x:su.El, colour x=A:=by
   exact ⟨⟨⟨_,h⟩,hp⟩,rfl⟩
set_option maxHeartbeats 900000 in
lemma treasury (X:Mat)(hp:∀ i:su.El, Commute X (colour i)) : X=X 0 0 • 1 :=by
   obtain ⟨u,hu⟩:=plucks violet (by
       have he:star violet=Matrix.diagonal ![1,-Complex.I,Complex.I]:=by ext i j; fin_cases i <;> fin_cases j <;> simp [violet, Matrix.diagonal_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
       constructor <;> rw [he] <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [violet, Matrix.diagonal_apply, Matrix.mul_apply, Hue, Fin.sum_univ_succ, Matrix.one_apply]) (by rw [violet, Matrix.det_diagonal]; simp [Hue, Fin.prod_univ_succ])
   have h : X * violet = violet * X:=hu ▸ (hp u).eq
   have hh i j (hi:i≠j): X i j=0:=by
       let U:Hue→ℂ := ![1,Complex.I,-Complex.I]
       have hk : X i j* U j= U i * X i j:= by have he:= congr_fun (congr_fun h i) j; simpa only [violet,Matrix.mul_diagonal, Matrix.diagonal_mul] using he
       by_contra hn; have hz:=mul_right_cancel₀ hn ((mul_comm _ (X i j)).trans hk)
       fin_cases i <;> fin_cases j <;> first | solve | norm_num [U,Complex.ext_iff] at hz | simp at hi -- edit
   obtain ⟨v,hv⟩:=plucks rotary (by constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [rotary, Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.mul_apply,Hue,Fin.sum_univ_succ, Matrix.one_apply]) (by simp [rotary,Matrix.det_fin_three]) -- exact norm_num
   have he:X*rotary=rotary*X:=hv ▸ (hp v).eq
   have h0: X 0 0=X 1 1:=by simpa [Matrix.mul_apply,Hue,Fin.sum_univ_succ,rotary] using congr_fun (congr_fun he 0) 1
   have h1:X 1 1=X 2 2:=by simpa [Matrix.mul_apply,Hue,Fin.sum_univ_succ,rotary] using congr_fun (congr_fun he 1) 2
   ext i j; by_cases hi:i=j; · subst i; simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,mul_one]; fin_cases j <;> first | rfl| exact h0.symm | exact (h0.trans h1).symm
   rw [hh _ _ hi, Matrix.smul_apply, Matrix.one_apply_ne hi, smul_zero]
lemma rich (B: Spike)(x y: Pinor)(i j:Hue): wave B (x,i) (y,j)= B x y*(if i=j then 1 else 0):=by simp [wave,Matrix.one_apply]
def gold (D:Bundle): Spike:=Matrix.of fun i j=> D (i,0) (j,0)
lemma gilt (D:Bundle)(h:∀ k:su.El,Commute (touch (colour k)) D):D=wave (gold D):=by
   ext ⟨i,x⟩ ⟨j,y⟩; let M:Mat:=Matrix.of fun a b=> D (i,a) (j,b)
   have he(k:su.El):Commute M (colour k):=by
       change M*colour k=_; ext a b; have he:=congr_fun (congr_fun ((h k).symm.eq) (i,a)) (j,b); simpa [Matrix.mul_apply,touch,M, Fintype.sum_prod_type,Matrix.one_apply,ite_mul,mul_ite] using he
   rw [rich]; change M x y=M 0 0*_; have hp : M x y=(M 0 0 • (1:Mat)) x y:=congr_fun (congr_fun (treasury _ he) x) y; exact hp.trans (by rw [Matrix.smul_apply, Matrix.one_apply,smul_eq_mul])
lemma leafy (X:Spike): gold (wave X)=X:=by ext x y; simp [gold, rich]
def blot (u : Flavor N)(x:EvenA c N)(i j: Site c):Spike:=gold (cell (feeF u x) i j)
lemma known (x:Grid c→ EvenA c N)(h:shadeG x)(hp:Fit (x 1))(b: Flavor N)(i j:Site c) : cell (feeF b (x 1)) i j=wave (blot b (x 1) i j):=by
   apply gilt; intro k
   let p: Frame c:=fun _=>k; have hx : gauge p (1:Grid c)=1:=by ext1 e; simp [p,Lattice.gauge]
   let v:=x 1; have hV: sways (Lat.copies N (siteRot p)) v=v:=by apply Subtype.ext; have he:= h 1 p; rw [hx] at he; exact he
   let M:=feeF b v; let Q:= siteRot p; have hr : M=star Q*M*Q:=by exact (congr_arg (feeF b) hV.symm).trans (rite v b _ hp)
   have hG : Q*M=M*Q:=by nth_rw 1 [hr]; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(siteRot_u p).2, one_mul]
   have hv₁(Y: Site c→Bundle)(U:Sheet c): cell (U* rides (Equiv.refl _) Y) i j=cell U i j *Y j:=by
       nth_rw 1 [← star_star (rides (Equiv.refl _) Y)]; rw [ride_ad, cell_ride_right, star_star]; rfl
   have hm:=congr_arg (fun X=>cell X i j) hG; unfold Q siteRot at hm; rw [cell_ride_left,hv₁] at hm; exact hm
end YM.QCD.Stew
