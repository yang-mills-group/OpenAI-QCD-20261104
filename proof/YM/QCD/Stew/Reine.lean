import YM.QCD.Stew.Yacht
/-! # stencil permutation for signed frames. Keep chart parity at winding -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset

def tide (x:Signed): Equiv.Perm SampleX:=Equiv.optionCongr (Equiv.prodCongr x.perm (Equiv.refl _))
def skySig (s:Signed)(a:SampleX):ℂ:= a.elim 1 (fun i=>if s.flip i.1 then -1 else 1)
lemma realSS (i j: Site c): star (shine i j)=shine i j:=by rcases shines i j with h|h<;> rw [h]<;> simp
lemma g_mark (i j k: Site c)(s:SampleX):star (mark i s j k)=mark i s j k:=by unfold mark; cases s <;> simp
lemma tideM (v:Strut c)(o x y: Site c)(i:SampleX)(h:10*separation x o < c.val)(he:10*separation y o < c.val): mark (act v o) (tide v.1 i) (act v x) (act v y)=skySig v.1 i *mark o i x y:=by
    cases i with
    | none=> simp [mark,tide,skySig]
    | some i=>
      rcases i with ⟨a,_|_⟩ <;> simp only [tide, mark,skySig,Equiv.optionCongr_apply,Equiv.prodCongr_apply, Option.map_some,Option.elim_some,Prod.map,Bool.false_eq_true,Equiv.refl_apply,↓reduceIte] <;> first| rw [show lift (act v _-_) =_ from heels v o x h,Signed.act_at]| rw [show lift (act v _-_) =_ from heels v o y he,Signed.act_at]
      all_goals split<;>simp [heel]
lemma sluice (v:EvenA c N)(b: Flavor N)(i:SampleX)(D:Support c) (o)(h:Gated D v) : shape o (feeF b v) i=∑ x∈D,∑ y∈D,(shine o x*shine o y*mark o i x y) • blot b v x y:=by
    symm; apply Eq.trans (b:=∑ x∈D,∑ y:Site c,(shine o x*shine o y*mark o i x y) • blot b v x y) (sum_congr rfl fun x _=> Finset.sum_subset (subset_univ _) fun y _ hh=>?_) (sum_subset (subset_univ _) fun x _ he=>sum_eq_zero fun y _=>?_)
    · unfold blot; rw [colour_room v h b (Or.inr hh),gold0,smul_zero]
    unfold blot; rw [colour_room v h b (Or.inl he),gold0,smul_zero]
lemma pos_h (b: Flavor N)(x:Grid c→EvenA c N)(h:Fit (x 1))(hf:shadeG x)(p:SampleX)(hp:Warrant v g k)(D:Support c)(o)(he:Nonwrapping D o)(hv:Gated D (x 1)):
    shape (act v o) (feeF b (Diode N v k g (x 1))) (tide v.1 p)=skySig v.1 p • (k*shape o (feeF b (x 1)) p*star k):=by
    let T:=D.image (act v); rw [sluice _ b _ T _ (gateS _ _ _ _ _ hv),sluice _ b _ D _ hv]
    unfold T; rw [sum_image (act v).injective.injOn]; simp only [Finset.smul_sum, Matrix.sum_mul,Matrix.mul_sum,Finset.smul_sum]; refine sum_congr rfl (fun i hi=>?_); rw [sum_image (act v).injective.injOn]; refine sum_congr rfl fun j hj=>?_ ; rw [rollsL hp h hf, Matrix.mul_smul] -- order
    simp_rw [Matrix.smul_mul, smul_smul]; congr 1; rw [tideM v o i j p (he i hi) (he j hj),← booth hp o i j (he i hi) (he j hj)]; ring
lemma starM (b:Flavor N)(x:Grid c→EvenA c N)(h: Fit (x 1))(hf: shadeG x)(hr: Regal c N (x 1)=x 1)(p:SampleX)(o): shape o (feeF b (x 1)) (invert p)=g5*star (shape o (feeF b (x 1)) p)*g5:=by
   unfold shape; simp only [star_sum, Matrix.sum_mul, Matrix.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   change _ • blot b (x 1) _ _ =g5*star (_ • blot b (x 1) _ _) * _
   rw [star_smul,Matrix.mul_smul, Matrix.smul_mul]; apply congr_arg₂ (· • ·)
   · simp only [star_mul,realSS,g_mark]; rw [mul_comm]; unfold mark invert; cases p; rfl; next p=> rcases p with ⟨i,_|_⟩ <;> rfl
   apply realK b h hf hr
lemma Δ_comm (o:Site c)(i:Axis)(hp: Warrant v g k)(U:Grid c) : delta (sky v U) i*haze v k g=skySig v.1 (some (i,true)) • (haze v k g * delta U (v.1.perm i)):=by
    let S:= haze v k g; let d:=sky v U; let t (s:Signed):= s.perm i
    have hu := turned_leg hp.1 k U (posDir i)
    have hv := turned_leg hp.1 k U (negDir i)
    unfold delta; change ((2:ℂ)⁻¹ • (leg _ _ (posDir _) - leg _ _ (negDir _)))*_=_; rw [Matrix.smul_mul, sub_mul, Strut.sky,Strut.haze,hu,hv, Matrix.mul_smul]; cases he : v.1.flip i
    · simp [Step.rotate,posDir,negDir,leg,he,shiftE,mul_sub,↓reduceIte, Bool.xor_false,Bool.false_xor,skySig,Option.elim,one_smul]
    rw [smul_comm]; simp [skySig,Step.rotate,posDir,negDir,leg, he, Bool.true_xor,Bool.xor_true,Bool.not_true,Bool.not_false,ite_true,ite_false, mul_sub]
end YM.QCD.Stew
