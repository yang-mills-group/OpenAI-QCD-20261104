import YM.QCD.Flume.Bow

/-! # real coefficients for skew part -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}

def alpha (v : Train j) (a : Axis) (p : Momentum) := Complex.I*(Dir v p).2 a
def alphaT (v : Train j) (a : Axis) := tape (alpha v a)
lemma alf (hj : 2≤j) (a : Axis) (v : ι→Train j): Moderate (fun _ : ι=>1) fun i=>alpha (v i) a:=by
  simpa only [alpha,one_mul] using! ((Moderate.const Complex.I).mul ((Dir_budget hj v).vector a))
lemma alphabet (a : Axis) (v : Train j) : Overlaps zone (alpha v a) := by intro p hp x hx; rw [alpha, period_dir v x hp hx]; rfl
lemma alpha_cash (hj : 2≤j) (v : ι→Train j) : ∃ η C : ℝ,0<η∧0<C∧∀ a : Axis, ∀ i, Width η C (alphaT (v i) a):=by
  apply staple
  · intro a; obtain ⟨η,C,hp,hc,h⟩:= tapes_sound (alf hj a v) zone_pos (fun i=> alphabet _ _); exact ⟨η,C,hp,hc,fun i=> by simpa [alphaT] using h i⟩
  intro i _ _ _ _ h hs hp hb j; exact (h _).mono hs hb
lemma read_al (hj : 2≤j) (v : Train j) (a p) (hp : p ∈ baseCube): RRead (alphaT v a) p=alpha v a p:=by
  have h (p : Momentum) (hp:p∈realCube zone): star (alpha v a (-p))=alpha v a p:=by rw [alpha,evenD v _ hp,star_mul]; change star (-(Dir v p).2 a)*star Complex.I=_; rw [star_neg,show star ((Dir v p).2 a)=_ from congr_fun (show star _=_ from (native_dir _ _ hp.1).2) a]; simp [alpha,mul_comm]
  obtain ⟨η,hc,H⟩:= tapes_read (alf hj a fun _ : Unit=>v) zone_pos (fun i=>alphabet _ _) (fun i=>h); exact H () p (base_subset_realCube hc hp)
lemma negative_al (hj : 2≤j) (s : Signed) (v : Train j) (a : Axis) (x : Cover) :
    alphaT v (s.perm a) (s.act x)= if s.flip a then -alphaT v a x else alphaT v a x:= by
  obtain ⟨σ,C,hp,hc,H⟩:=alpha_cash hj (fun _ : Unit=>v)
  have hh:= (Signed.actEquiv (R:=ℤ) s).toEquiv.summable_iff.mpr ((H (s.perm a) ()).unweighted hp.le).2.1
  let f (x : Cover):=alphaT v (s.perm a) (s.act x)
  have hm : Summable fun i=>‖f i‖:=hh
  have ht (p : Momentum) (h:p∈baseCube): RRead f p=if s.flip a then -RRead (alphaT v a) p else RRead (alphaT v a) p:=by
    unfold f; rw [← flash_reread s p,read_al hj _ _ _ (bank_acts _ h s), read_al hj _ _ _ h,alpha,s_dir s v p (base_subset_realCube zone_pos h)]; change _*s.act _ _= _; rw [Signed.act_at]; split <;> simp [alpha]
  have hv := ((H a ()).unweighted hp.le).2.1
  split
  next he =>
    have h : f=fun x=> -alphaT v a x:=RRead_injective hm (by simpa using hv) fun i hi=> by rw [ht i hi,if_pos he,RRead_neg]
    exact congr_fun h x
  next he=> exact congr_fun (RRead_injective hm hv fun i hi=> by rw [ht i hi,if_neg he]) x

/-- check odd. -/
lemma odd_al (hj : 2≤j) (v : Train j) (a x) : alphaT v a (-x) = -alphaT v a x:=negative_al hj ⟨1,fun _=>true⟩ v a x

lemma pole_top (j) (p : Momentum) (a): alpha (.top j) a p=(mode p (step a)-mode p (-step a))/2:=by
  unfold alpha; rw [Dir_top,mode_opposite]
  change Complex.I*Complex.sin (p a)=_; rw [sin_chip,Exterior.factor]; unfold chip; simp only [mul_neg, Complex.exp_neg]; field_simp; ring
lemma orth_coeff (hj : 2≤j) (a : Axis) (x : Cover) : alphaT (.top j) a x=(token (step a) x-token (-step a) x)/2:=by
  obtain ⟨σ,C,hp,hc,H⟩:=alpha_cash hj (fun _ : Unit=>Train.top j)
  let f (x : Cover):=(token (step a) x-token (-step a) x)/2
  have hs : alphaT (.top j) a=f:=by
    apply RRead_injective ((H a ()).unweighted hp.le).2.1 _
    · intro p h; rw [read_al hj _ _ _ h,pole_top]
      unfold f RRead; unfold Laurent.read; simp only [Complex.ofReal_div,Complex.ofReal_sub,smul_eq_mul, Complex.ofReal_ofNat,mul_div_assoc',mul_sub,tsum_div_const]
      rw [Summable.tsum_sub (real_series (((token_rate _ 0).unweighted le_rfl).2.1) h.1) (real_series (((token_rate _ 0).unweighted le_rfl).2.1) h.1)]
      change _=(RRead (token (step a)) p-RRead (token (-step a)) p)/2; rw [token_eval,token_eval]
    refine (summable_of_ne_finset_zero (s:={step a,-step a}) ?_)
    intro i hi; rw [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; simp [f,token,hi]
  exact congr_fun hs x
end YM.QCD.Flume
