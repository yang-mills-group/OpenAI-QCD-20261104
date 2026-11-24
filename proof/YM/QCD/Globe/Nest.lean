import YM.QCD.Globe.Moon
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork Laurent
variable (S h)
-- scales right from Fork.scales symmetrical
set_option quotPrecheck false
lemma scares (y:Site c)(r:Site S.L)(A:Cover→Bundle)(l:ℕ)(η C D:ℝ)(hu:∀ i:ℕ,(1+i:ℝ)^l≤ D*Real.exp (η*i))(he:0 < D)(ht:Width η C A)(T: Site c→Bundle)(hz:∀ x,HasSum (fun z=> caption S h (A z) x y r z) (T x)): ∑ x:Site c, costS l x y *‖T x‖ ≤ D*C:=by
  have hh x := (hz x).summable.norm.mul_left (costS l x y)
  refine le_trans (sum_le_sum (s:=univ) (g:=fun x=>∑' z, costS l x y* ‖caption S h (A z) x y r z‖) (fun x _=> ?_)) ?_
  · rw [tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (cost_nn ..); rw [← (hz x).tsum_eq]; exact norm_tsum_le_tsum_norm (hz x).summable.norm
  have hP:=summable_sum (s:=univ) (f:=fun x z=> costS l x y * ‖caption S h (A z) x y r z‖) (fun x _=> hh x)
  rw [← Summable.tsum_finsetSum (fun x _=>hh x)]
  apply (Summable.tsum_le_tsum ?_ hP (ht.2.1.mul_left D)).trans
  · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 he.le
  intro z; let u:=wrap c z; rw [sum_eq_single (y-u)]; rotate_left
  · intro i _ hi; unfold caption; rw [if_neg (mt (fun hh=> eq_sub_of_add_eq hh) hi),norm_zero,mul_zero]
  · simp
  unfold caption; rw [if_pos (sub_add_cancel y u),norm_smul,norm_mul]; simp_rw [Flume.pathLength]; simp only [one_mul]; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply le_trans _ (hu (size z)); unfold costS; gcongr; exact (by simpa only [show wrap c z=u from rfl, sub_add_cancel] using duration (y-u) z) -- edit
lemma wallet (P:Plan j)(m:ℕ)(hj:4≤j)(hk:4≤k): ∃ C:ℝ, 0 ≤ C∧∀ (S:Flight j k)(f c:Side)(h:f.val=c.val*S.L.val),Cent id (sliceL S h).parent m ((S.L.val:ℝ)^4*(C*Brick.cape S.L 0)) (barP S h):=by
    obtain ⟨σ,C,hσ,hC,H⟩:=pack_funds hj hk; obtain ⟨v,hv,H'⟩:=eats m σ hσ
    refine ⟨v*C,mul_nonneg hv.le hC,fun S f c h i=>?_⟩
    unfold Gan; let R:=sliceL S h
    let U t (p:Site c):=costS m p i * ‖cell (barP S h) i (R.assemble (p,t))‖
    let B:=v*C*Brick.cape S.L 0
    have hh(t:Site S.L):∑ p:Site c,U t p≤B:=by
       apply le_trans (scares S h i t (unFork S t) m σ _ v H' hv (H S t).2 (fun p=>cell (barP S h) i (R.assemble (p,t))) (fun x=>unPepper x i t P hj hk)); exact le_of_eq (by unfold B Brick.cape; ring)
    let g:=Equiv.ofBijective R.assemble R.assemble_bijective; rw [← Equiv.sum_comp g _,Fintype.sum_prod_type, sum_comm];
    have he(r:Site S.L) x: (sliceL S h).parent (g (x,r))=x:= by change R.parent (R.assemble _)=_; simp
    simp_rw [he,id_eq,cost_symm i (_ : Site c)] -- inspect
    calc
      _ ≤ ∑ _ : Site S.L,B:=by apply sum_le_sum; intro i _; exact hh i
      _ = _:=by rw [sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow]
lemma anthem (hj:4≤j)(hk:4≤k)(m:ℕ):∃ C:ℝ,0 ≤ C∧∀ (S:Flight j k)(f c: Side)(h:f.val=c.val*S.L.val),tithe (proton S h) (sliceL S h) (C*Brick.cape S.L 0) m:=by
    obtain ⟨C,hC,H⟩:= Brick.caper hj hk m; refine ⟨C,hC,fun S f c h i hi p=>?_⟩
    apply le_trans (H S _ _ h i hi p); change C * _ ≤ C* Brick.cape S.L 0*((S.L.val:ℝ)⁻¹)^i.length
    unfold Brick.cape; rw [pow_add, add_zero, pow_one]; exact le_of_eq (by ring) -- pow one order
lemma foldingP (P:Plan j)(T:ℝ)(ht:0<T)(hj:4 ≤ j)(hk:4 ≤ k)(m:ℕ)(hp:2≤ m): ∃ L₀:ℕ,∀ (S:Flight j k)(c f:Side)(h:f.val=c.val*S.L.val), L₀ ≤ S.L.val→∀ R:Sheet f,Drier R→∀ t:ℝ,0 ≤ t→ Beam R m t → Cent id id m (t*T) (barP S h * R * proton S h):=by
    obtain ⟨C,hC,H⟩:= wallet P m hj hk; obtain ⟨D,hD,G⟩:= anthem hj hk m
    let K:= 3*3^m*4^m*C*D; obtain ⟨L,hL⟩:= exists_nat_gt (K/T)
    refine ⟨L,fun S c f h hh R hR t hz hE=> ?_⟩; have hs:= G S _ _ h; let r:= (S.L.val:ℝ); have hx : 0 < r:=by unfold r; positivity
    let A:= Brick.cape S.L 0; have hA:0≤ A:=(Brick.cape_pos ..).le
    let M:=sliceL S h
    let X:=t*moldH (D*A) m S.L; have hQ:0≤ X:=by unfold X moldH; positivity
    rw [Matrix.mul_assoc]; refine Cent.up (Cent.op (H S _ _ h) (rotatedPay hR hp (mul_nonneg hD hA) hE hs) hQ) ?_
    change r^4*(C*A)*X≤_; have hZ:A^2=r⁻¹^3:= Brick.capeQ ..; unfold X moldH; rw [show r^4*(C*A)*(t*(D*A*(3*3^m*((S.L.val:ℝ)⁻¹)^2)*4^m))= t*(K/r) from ?_]; apply mul_le_mul_of_nonneg_left _ hz; rw [div_le_iff₀ hx]; have he:K/T ≤r:= le_trans hL.le (Nat.cast_le.mpr hh); rw [div_le_iff₀ ht] at he; linarith
    unfold K; change r^4*(C*A)*(t*(D*A*(3*3^m*r⁻¹^2)*4^m))=_; calc
     _ = t*(3*3^m*4^m*C*D)*(r^4*A^2*r⁻¹^2) := by ring
     _ = _:=by rw [hZ]; field_simp
end YM.QCD.Globe
