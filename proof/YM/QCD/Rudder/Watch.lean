import YM.QCD.Rudder.Tape

/-! # representing wood uniformly in Gleam fare -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric YM.Next.Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {n : Side} {I J : Type} {j : ℕ}
variable {δ c C : ℝ}
lemma letter_spin (u : ℂ) (V : Spike): onSpin n (u • V)=u • onSpin n V:=by unfold onSpin wave; rw [Matrix.smul_kronecker,ride_smul]; rfl
lemma roomTag (W : Cover→ℝ) (h : 0≤δ) (hw : Laurent.Width δ C W) : Feat δ C (fun _ t U=> deck t U W):=by
  let M (i : Cover×Lattice.Order): Gleam:= ⟨route 0 i.1 i.2,((votes:ℂ)⁻¹*(W i.1:ℂ)) • 1⟩
  have he x:∑ i:Lattice.Order,(M (x,i)).rate δ= Real.exp (δ*size x)*‖W x‖:= by
    unfold Gleam.rate M; simp_rw [Run.amounts,norm_smul, norm_mul,norm_inv, Complex.norm_natCast, Complex.norm_real,oneNorm,mul_one,sum_const,card_univ,nsmul_eq_mul]; field_simp [poll_pos.ne']
  have hp : Summable fun i=> (M i).rate δ:= by
    rw [summable_prod_of_nonneg (fun i=> (M i).valid δ)]; exact ⟨fun i=> Summable.of_finite, by simp_rw [tsum_fintype,he]; exact hw.2.1⟩
  have hb:= hp.tsum_prod; simp_rw [tsum_fintype,he] at hb
  have hh : Wages δ C M:= ⟨h,hp,hb.trans_le hw.2.2⟩
  refine ⟨_, M, hh,fun n t U=>?_⟩
  have hx x: ∑ o:Lattice.Order,(M (x,o)).dept t U=(W x:ℂ) • mote t U x:=by unfold Gleam.dept M; simp only [letter_spin,on_spin_one,Matrix.mul_smul,Matrix.mul_one, ← smul_sum, mote,smul_smul]; rw [mul_comm ((_ : ℂ)⁻¹)]
  have hf:= (hh.applied t U).of_norm
  dsimp only; rw [← show (∑' i, (M i).dept t U)=deck t U W from ?_]; exact hf.hasSum
  rw [hf.tsum_prod]; simp_rw [tsum_fintype,hx]; rfl
lemma pays_all (P : Plan j):∃ δ C : ℝ,0<δ∧0<C∧∀ v : Train j,Feat δ C (fun _ t U=> wood P t v U):=by
  obtain ⟨a,A,ha,hA,H⟩:= alpha_cash P.good (id : Train j→_)
  obtain ⟨z,Z,hz,hZ,T⟩:= P.herm_paid (fun i:Train j×Axis=> i.1) (fun i=>i.2)
  let δ:= min a z; have he:= lt_min ha hz
  let R (i:Axis): Ground:= fun _ t U=>arcL t U i
  let C:= 1+Real.exp δ
  let U i:= Gleam.mk [] (gamma i)
  let K i:= (U i).rate δ
  let w i:= P.μ*(C*C)+ (Z*C)*(Z*C) + K i * A
  have hh v i: Feat δ (w i) (fun n t U=> walls P t v U i+skewL (vein t v i U)):=by
    have h₁:=Feat.solo he.le ⟨[posDir i],1⟩; simp only [Gleam.dept,routeM,List.map_singleton,leg,posDir,Bool.false_eq_true,↓reduceIte,List.prod_singleton,Gleam.rate,List.length_singleton,Nat.cast_one,mul_one,oneNorm,on_spin_one,mul_one] at h₁
    have hr : Feat δ C (R i):=(Feat.one he.le).sub h₁
    have hp:= roomTag (P.Herm v i) he.le ((T (v,i)).mono (min_le_right a z) (show Z*1≤Z from (mul_one Z).le))
    have hy:= roomTag (alphaT v i) he.le ((H i v).mono (min_le_left a z) le_rfl)
    have ht : Feat δ (K i) (fun n _ _=> onSpin n (gamma i)):=by simpa [U,Gleam.dept,routeM,K] using! Feat.solo he.le (U i)
    have hz: Feat δ (K i*A) (fun n t U=>vein t v i U):= ht.prod hy
    have hP := hp.prod hr; have hS:= hp.prod hr.ad
    let k:ℂ:=(2:ℂ)⁻¹
    have hL:= (((hr.ad.prod hr).scale (P.μ:ℂ)).plus (((hP.ad.prod hP).plus (hS.ad.prod hS)).scale k)).plus ((hz.sub hz.ad).scale k)
    refine hL.mono he.le le_rfl (le_of_eq ?_)
    unfold k w; norm_num [Real.norm_eq_abs,abs_of_nonneg P.price.le]; ring
  refine ⟨δ,1+∑ i,w i,he,add_pos_of_pos_of_nonneg one_pos ?_,fun v=>?_⟩ -- check
  · apply sum_nonneg; intro i _; obtain ⟨_,_,h,-⟩:= hh (.top j) i; exact h.chief
  let S (i: Axis):Ground:=fun n t U=> walls P t v U i+skewL (vein t v i U)
  rw [show (fun n t U=> wood P (n:=n) t v U)=∑ i : Axis, S i from by funext n t U; simp_rw [Finset.sum_apply]; rfl]; exact (Feat.group (U:=S) (fun i _=> hh v i) he.le).mono he.le le_rfl (le_add_of_nonneg_left zero_le_one)
end YM.QCD.Rudder
