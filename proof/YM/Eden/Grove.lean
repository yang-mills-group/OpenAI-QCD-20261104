import YM.Eden.Stake
import YM.Vest.Key
import YM.Massive.Ribbon.Charge
/-! # curvature plank. basis rotation via constant Color heat (and charge). angular slots actual.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior FreeResolvent
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius Classical
variable {G:Gauge}{d' k i m:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Next.Rank Normal
variable (L:G.Color→ₗᵢ[ℝ] G.Color)
noncomputable def laneR (k:ℕ): Matrix (Zinc G k) (Zinc G k) ℂ:= Matrix.of fun i j => if i.1=j.1 then (L (EuclideanSpace.single j.2 1) i.2:ℂ) else 0
lemma paints_eq {d:ℕ} : pigmentK (d:=d) L.toLinearMap= exchange (QCD.Bera.spool (laneR L d)):=by
     ext1 i; rw [pigmentK,MvPolynomial.aeval_X, Normal.exchange_x]; -- pay single spine.Z
     let V:= laneR L d; have h : QCD.Bera.spool V i=∑ j:G.ColorIndex,Finsupp.single (i.1,j) (V i (i.1,j)):=by
         ext j; -- compute or ext1
         simp only [Finsupp.finsetSum_apply]; rw [Vest.Tone.spi]; obtain ⟨k,v⟩:=j; by_cases ht:i.1=k
         · simp [V,laneR,ht, Finsupp.single_apply]
         simp [V,laneR,ht,Finsupp.single_apply]
     rw [h]; simp only [map_sum,Normal.glyph,Finsupp.linearCombination_single]; apply sum_congr rfl; intro j _; unfold V laneR; rw [Matrix.of_apply,if_pos rfl]; rfl
lemma law_pr (i j : G.ColorIndex): ∑ z, L (EuclideanSpace.single z 1) i * L (EuclideanSpace.single z 1) j = if i=j then 1 else 0:=by
     let f(z:G.ColorIndex):G.Color:= EuclideanSpace.single z 1; let X:Matrix G.ColorIndex G.ColorIndex ℝ:= Matrix.of fun i j=> L (f j) i; have hx:X.transpose*X=1:=by
          ext i j; have he := L.inner_map_map (f j) (f i); rw [PiLp.inner_apply,PiLp.inner_apply] at he; rw [Matrix.mul_apply,Matrix.one_apply]; refine Eq.trans ?_ (he.trans (?_))
          · apply sum_congr rfl; intro j _; rfl
          by_cases ht:i=j <;> simp [f,EuclideanSpace.single_apply,ht,Ne.symm]
     have hh:= (show X*X.transpose=1 from mul_eq_one_comm.mp hx); exact congr_fun (congr_fun hh i) j
lemma fireV (x:Cover)(k:ℕ)(n:Side)(H: Bed) : let Q:=milky (G:=G) (d':=k) x H n; laneR L k*Q*(laneR L k).transpose= Q:=by
   intro Q; ext ⟨i,u⟩ ⟨j,v⟩; change _=milky x H n _ _; rw [milk_read]; let K:= laneR L k
   have hp(t:Motif k)(z:G.ColorIndex): (K * Q) (i,u) (t,z) =K (i,u) (i,z)*(allP x H n i t:ℂ):=by
        rw[Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single i, sum_eq_single z]; rotate_left
        · intro j _ h; rw [show Q (_,j) (t,z)=0 from ?_,mul_zero]; rw [show Q=milky x H n from rfl, milk_read, if_neg]; exact h
        · simp
        · intro a _ h; apply sum_eq_zero; intro b _; rw [show K (i,u) (a,b)=0 from if_neg (show ¬i=a from Ne.symm h),zero_mul] -- underscore needs know
        · simp
        rw [show Q=milky x H n from rfl,milk_read,if_pos rfl]
   rw[Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single j]; swap; · intro a _ h; apply sum_eq_zero; intro b _; rw [transpose_apply, show laneR L k (j,v) (a,b)=0 from if_neg (show ¬j=a from Ne.symm h),mul_zero]
   swap; · simp
   change (∑ x:G.ColorIndex,(K*Q) _ (j,x)*K _ (j,x))= _; simp_rw [hp]; unfold K laneR; simp only [Matrix.of_apply, if_true]; simp_rw [mul_right_comm (b:=(allP x H n i j:ℂ)), ← Complex.ofReal_mul]; rw [← Complex.ofReal_sum,← Finset.sum_mul,law_pr]; by_cases he:u=v <;>simp [he]
-- Proof V.Reader has ext needed.Inertia.S
lemma milky_symm {d:ℕ}(u:Cover)(h:Floor H t n a b)(ha:0<a) : Matrix.IsSymm (milky u H n (G:=G) (d':=d)) :=by
    ext x y; let X:=voteP n x u; let Y:= voteP n y u; let Z:= heartP H G n; have hZ:Z.transpose=Z:=by unfold Z heartP; rw [paid,←Matrix.transpose_map, FreeResolvent.tensor_transpose,show (learned H n).transpose= learned H n from flux_symm _ _ ⟨fun v=> (h.uniform.1 v).1⟩ ha h.symmetric.1]
    change (Y*Z*X.transpose) () ()=(X*Z*Y.transpose) () (); rw [← show (X*Z*Y.transpose).transpose=Y*Z*X.transpose from ?_]; rfl
    rw [Matrix.transpose_mul,Matrix.transpose_mul, Matrix.transpose_transpose,hZ, Matrix.mul_assoc]
noncomputable def wager {k:ℕ}(x:Cover)(H:Bed)(n:Side)(h:(milky x H n (G:=G) (d':=k)).IsSymm): Normal.Symmetric (Zinc G k) where
    cov i j := -milky x H n i j
    symm i j:=congr_arg _ (h.apply j i)
-- unused d
lemma minuteR (x:Cover)(h: (milky x H n (G:=G) (d':=k)).IsSymm)(A:Lily G k): milk (wager x H n h) (pigmentK L.toLinearMap A) =pigmentK L.toLinearMap (milk (wager x H n h) A):=by
    let Q:=milky x H n (G:=G) (d':=k); rw [paints_eq,Normal.prepared]; let X:=wager x H n h; have hx: scope (QCD.Bera.spool (laneR L k)) X=X:=by
       apply Normal.Symmetric.ext; change Matrix.of (scope (QCD.Bera.spool (laneR L k)) X).cov = Matrix.of X.cov; rw [Vest.Tone.scalM]; change laneR L k*(-Q)*(laneR L k).transpose= -Q; rw [Matrix.mul_neg, Matrix.neg_mul, show laneR L k*Q*(laneR L k).transpose=Q from fireV L x k n H]
    rw[hx]
omit L
lemma shineK (s:Signed)(h:Floor H t n a b)(ha:0<a)(hu: Bid.Sworn H n G)(ht:(milky 0 H n (G:=G) (d':=k)).IsSymm)(A:Lily G k): let Q:=wager 0 H n ht; milk Q (posedK s A)= posedK s (milk Q A):=by
    intro Q; let M(i:Zinc G k):=Finsupp.single (tideK s i) (stainK s i:ℂ); rw [show posedK (G:=G) (d:=k) s=exchange M from ?_,prepared]; swap; · ext1; rw [posedK,MvPolynomial.aeval_X,exchange_x]; simp [glyph,M]
    have hz: scope M Q=Q:=by
      apply Normal.Symmetric.ext; funext i j; unfold scope M; simp only [treats,Finsupp.linearCombination_single,Pi.smul_apply,Q,wager,smul_eq_mul]; have h:=shootsK h ha s 0 i j hu; rw [Signed.act_zero] at h -- dsimp let?
      dsimp only at h; change _= -milky 0 H n _ _; rw [←h]; ring
    rw[hz]
lemma cc_milk {J:Type}(A: MvPolynomial J ℂ)(Q:Normal.Symmetric J)(hp:∀ i j: J, star (Q.cov i j)= Q.cov i j):
    MvPolynomial.map (starRingEnd _) (milk Q A)=milk Q (MvPolynomial.map (starRingEnd _) A):=by
    let I:= MvPolynomial.map (σ:=J) (starRingEnd ℂ); have hs (i:J)(A: poly J): I (slit (Q.cov i) A)= slit (Q.cov i) (I A):=by
         induction A using MvPolynomial.induction_on with
         | C s=> simp [I]
         | add x y h hp=> rw[_root_.map_add,map_add,map_add,h,hp,map_add]
         | mul_X x a h=> rw [mul_comm, slit_prod, map_mul I,map_add,map_mul I,map_mul I,h,show I (MvPolynomial.X a)=_ from MvPolynomial.map_X ..,show I (MvPolynomial.C _) = MvPolynomial.C (star (Q.cov i a)) from MvPolynomial.map_C ..,hp, slit_prod]
    change I _= milk Q (I A); induction A using MvPolynomial.induction_on with
    | C a=> simp [I]
    | add a b h hp=> rw[_root_.map_add,map_add,map_add,h,hp,map_add]
    | mul_X x a h=> rw [mul_comm, Normal.feeds, map_mul I, map_add,map_mul I,hs,h,show I (MvPolynomial.X a)=_ from MvPolynomial.map_X ..,Normal.feeds]
lemma realS (u v:Zinc G k) : star (milky 0 H n u v)=milky 0 H n u v:=by rw [milk_read]; split <;> simp
end YM.Eden
#print axioms YM.Eden.cc_milk
#print axioms YM.Eden.fireV
