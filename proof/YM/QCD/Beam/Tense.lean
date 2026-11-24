import YM.QCD.Beam.Reap
/-! # Metering on same fields. No K residual covers divided. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam.Pipe
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Tree.Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M N: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
variable {H:Cash W τ μ L Q o C T R}{ι:Type}
local notation "D" => Clump S ι
variable (Y:Pipe H F M ι)
def tenn (_Y:Pipe H F M ι)(s:D):ℕ:=∑ i∈s.toLeft,Mixed.shares S i
lemma whorls (s:D): Y.tenn s=Y.sizeP s:=by
   unfold tenn sizeP; have he:Finset.disjSum s.toLeft s.toRight=s:=by ext i; cases i <;> simp
   conv_rhs=>arg 1; rw [← he]
   simp only [Finset.sum_disjSum]; simp [shifts,Mixed.shares]; refine sum_congr rfl fun i hi=> ?_; rcases i with i|i <;> rfl
lemma pointsP (s:D)(p a:ℝ)(w:ι→ℝ):∏ i∈s,Y.dues (unitsP Q L μ R.beta τ C a p) w i = Real.exp (a*Y.sizeP s)*((∏ i∈s.toLeft,H.text i)*(∏ i∈s.toRight,w i)):=by
  let v:= unitsP Q L μ R.beta τ C a p
  have he i: Y.dues v w (Sum.inl i) = Real.exp (a*Mixed.shares S i)* H.text i:=by
    cases i with
    | inl x=>
       unfold dues; simp only [comp_apply,shifts,Equiv.sumAssoc_apply_inl_inl, Mixed.shares,Mixed.costs, Cash.text, Sum.elim_inl]; split
       next h=> unfold steamP Packets.income; simp only [v,unitsP,Target.costs,Buy.quote,one_mul]; rw [← Real.exp_add]; apply congr_arg; ring
       next _=> rw [mul_zero]
    | inr z=> change H.opt z= Real.exp (a*(0:ℕ))* H.opt z; simp
  rw [cumulate,← Y.whorls]; unfold tenn; change (∏ i∈s.toLeft,Y.dues v w (.inl i))*(∏ i∈s.toRight,w i)=_
  simp_rw [he, Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum,← Nat.cast_sum, mul_assoc]
lemma hitsP (s : D) : (roster s.toLeft).shares ≤ Y.sizeP s:=by
   rw [← Y.whorls]; unfold tenn; set t:= s.toLeft
   have he:t.toLeft.disjSum t.toRight=t:=by ext i; cases i <;> simp
   suffices hh : (roster t).shares ≤ ∑ i∈t.toLeft, i.shares by
      refine hh.trans_eq ?_; nth_rw 2 [← he]; rw [Finset.sum_disjSum]; simp only [Mixed.shares,Sum.elim,sum_const_zero,add_zero]
   rw [← Packets.seeds_card S (roster t),register]; exact Finset.card_biUnion_le.trans_eq (Finset.sum_congr rfl fun i _=> Packets.seeds_card ..)

def landP (X:Coat T F) (s:D):Prop:= ∀ i ∈Y.full s,i∈ X.seeds.place ↔ i∈ (roster s.toLeft).place
variable [NormedAddCommGroup N][NormedSpace ℝ N]
structure Merit (w:ι→ℝ) (v:ℝ) (f₀:M→L[ℝ]N) : Prop where
 costs i:0≤ w i
 sumP s X : X.x=τ→ X.width=o.K→X.manifest →Y.born s→Y.landP X s → ∀ z:Air _ _,‖f₀ (Y.averageP s.toRight X z)‖ ≤ Real.exp (v*Y.sizeP s) *∏ i∈s.toRight,w i
variable [CompleteSpace N]
lemma arena {w:ι→ℝ} (a p:ℝ) (f₀:M→L[ℝ]N) (h:Y.Merit w a f₀) (H':Y.Viable)(X:Coat T F)(v:D)(hx:X.x=τ)(ht: X.width=o.K): ‖f₀ (Y.shootsP X v)‖ ≤∏ i∈v,Y.dues (unitsP Q L μ R.beta τ C a p) w i:=by
    rw [pointsP]; let S₀:= Real.exp (a*Y.sizeP v); let T':=∏ i∈v.toRight,w i; let V₀ := ∏ i∈v.toLeft,H.text i
    have hh:0≤ T':=prod_nonneg fun _ _=> h.costs _; have hP:0<S₀:=Real.exp_pos _
    unfold shootsP; split
    swap; · rw [map_zero,norm_zero]; apply mul_nonneg hP.le; exact mul_nonneg (prod_nonneg fun _ _=> H.positive _) hh
    next hZ=>
    let U₀:=Y.full v; let Z:= planted X v.toLeft; let g:= Y.capacityP v (own v.toLeft)
    have ht' : X.x=Z.x:=rfl
    have he': Y.landP Z v:=by
       intro i hi
       have hx:i∈ RG.flags (Pressure.temp X.x) X.V ↔ i∈(roster v.toLeft).flags:= by rw [← hZ.2.2,mem_inter]; exact ⟨fun p=>⟨p,hi⟩,fun p=>p.1⟩
       simp only [Z, planted, Stores.place,preps,mem_union]; exact or_congr Iff.rfl hx
    have hp(i:S.Choices): ‖f₀ (call (Z.taggedL i) g)‖≤ S₀*(V₀*T'):=by
      let C₁:=Z.taggedL i; let V:=(F.order G).prod C₁.dice
      let f₀' (j:F.Slice G × Air f G):= g (C₁.wrapY j.1) j.2
      let u := C₁.body R Q.table W o.a (own v.toLeft) Q.halo v.toLeft
      have hc:C₁.manifest:=planted_valid X _; have hM : Integrable f₀' V:=envPlot (Y.ripeP (own v.toLeft) v H' C₁ hx ht hc) _
      have hp : (∫ j, ‖u j‖ ∂V) ≤ V₀:=H.statements C₁ hx ht hc _ v.toLeft
      change ‖f₀ (∫ j,f₀' j ∂V)‖ ≤ _; rw [← f₀.integral_comp_comm hM]; apply (norm_integral_le_integral_norm _).trans
      have hj j: ‖f₀ (f₀' j)‖ ≤ ‖u j‖*(S₀*T'):=by
         unfold f₀' g capacityP; rw [map_smul,norm_smul]; apply mul_le_mul_of_nonneg_left (h.sumP v (C₁.wrapY j.1) hx ht hc hZ.2.1 he' j.2) (norm_nonneg _)
      have hz := H.integrated C₁ hx ht hc (own v.toLeft) v.toLeft
      apply (integral_mono (f₀.integrable_comp hM).norm (((show Integrable u V from hz).norm).mul_const _) hj).trans; rw [integral_mul_const]; exact (mul_le_mul_of_nonneg_right hp (mul_nonneg hP.le hh)).trans_eq (by ring)
    change ‖f₀ (draws Z g)‖ ≤ _; unfold draws choiceS; rw [map_smul,map_sum,norm_smul,Real.norm_of_nonneg (by positivity : 0≤ ((Fintype.card S.Choices:ℝ)⁻¹))]
    apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>hp i))) (by positivity)).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ,← mul_assoc, inv_mul_cancel₀ (by positivity),one_mul]

-- Near `Y` anomalous bills per anchor controlled by actual local landP. multiplier uniform. Speak restrict statuses before estimating hom M output. 
lemma seedPop {m:ℕ}{s:D}{X:Coat T F}(h: Y.landP X s) (x:Finset ι) (p:ι→Site c)(n:ℕ)(hx:∀ y,(x.filter (fun i=>p i=y)).card ≤ m)(hs:∀ i∈x,∃ k∈ X.seeds.place, k∈Y.full s∧ separation k (p i) ≤ n):x.card ≤ Y.sizeP s*Animals.ballCost (n+1)*m :=by
    let U:= (roster s.toLeft).dome n
    have hf i (hi:i∈x):p i∈U:=by obtain ⟨k,hk,hg,hx⟩:=hs i hi; exact halo_spec.mpr ⟨k,(h k hg).1 hk,hx⟩
    have hh : U.biUnion (fun j=>x.filter fun i=> p i=j)=x:=by ext i; simp only [mem_biUnion, mem_filter]; exact ⟨fun ⟨_,_,h,_⟩=>h,fun h=>⟨_,hf i h,h,rfl⟩⟩
    have he : U.card ≤ Y.sizeP s* Animals.ballCost (n+1):=(Mask.dome_count ..).trans (Nat.mul_le_mul_right _ (Y.hitsP s))
    exact (hh ▸ Finset.card_biUnion_le (s:=U)).trans ((Finset.sum_le_sum (s:=U) (fun i _=>hx i)).trans (by rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ he)) -- type
end YM.QCD.Beam.Pipe
