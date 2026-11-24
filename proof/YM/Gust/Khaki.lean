import YM.Gust.Arc
set_option maxHeartbeats 650000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d:ℕ}(T:Pollens P K)(hK:K.Domestic) {t:K.W} (a b:Axis)
local notation "Ξ" i:arg=> UV.tauMod i
noncomputable def Col (p:Bool):Submodule ℂ K.W:=LinearMap.ker (T.parity.toLinearMap-(tauMod p) • LinearMap.id)
lemma hue (v:K.W)(p:Bool): v∈Col T p↔ T.parity v= (Ξ p) • v:=by change T.parity v- (Ξ p) • v=0 ↔ _; exact sub_eq_zero
noncomputable abbrev flipC(a:Axis):EuPin:= (EuPin.optic a).choose
lemma couture(a:Axis): (flipC a).Lifts (Signed.mirror a):= (EuPin.optic a).choose_spec.1
lemma weave(a:Axis): (flipC a).matrix.val=(-Complex.I) • (gamma a*g5):= (EuPin.optic a).choose_spec.2
lemma twiceR(a:Axis): flipC a*flipC a=1:=by
    let X:= flipC a; have hp := EuPin.life_mul (couture a) (couture a); have he : Signed.mirror a* Signed.mirror a=1:=inv_mul_cancel _
    apply Subtype.ext; apply Prod.ext; · rw [he] at hp; exact hp.trans (map_one Signed.inclusionO)
    apply Units.ext; have hh:(flipC a).matrix.val=(flipC a).matrix⁻¹.val:= ((chaos a _ (weave a)).symm.trans (Oriole.E_star _).symm)
    change X.matrix.val*X.matrix.val=1; nth_rw 1 [show X.matrix.val= X.matrix⁻¹.val from hh]; exact X.matrix.inv_val
noncomputable abbrev Ch(r:Axis): K.W≃ₛₗ[starRingEnd ℂ] K.W:= (T.adj r).trans (T.spin (flipC r))
include hK
lemma candles: Ch T a=Ch T b:=by
      ext1 x; obtain ⟨d,t,rfl⟩:=hK.absorbs x; change T.spin _ (T.adj _ _) = T.spin _ (T.adj _ _); rw [T.a,T.a,T.w _ _ (couture a),T.w _ _ (couture b)]; apply congr_arg (K.focus none _); apply Subtype.ext; rw [RawSym.pinActs,RawSym.pinActs,RawSym.adjActs,RawSym.adjActs,rooted _ _ (couture a) (weave a),rooted _ _ (couture b) (weave b)]
variable (p:EuPin)(s:Signed)(hp:p.Lifts s)
lemma eyeP(x:K.W) : T.parity (T.adj a x)= T.adj a (T.parity x):=by
    obtain ⟨d,x,rfl⟩:= hK.absorbs x; rw [T.a,T.p,T.p,T.a,Patria.Hub.graded_eye]
include hp
lemma spinClamp(x:K.W):T.parity (T.spin p x)=T.spin p (T.parity x):=by
     obtain ⟨d,t,rfl⟩:=hK.absorbs x; rw [T.w _ _ hp,T.p,T.p,T.w _ _ hp]; apply congr_arg; apply Subtype.ext; rw [RawSym.parityActs,RawSym.pinActs,RawSym.pinActs,RawSym.parityActs]
     induction t.val using TensorProduct.induction_on with
     | zero=> simp
     | add x y h k=> simp only [map_add,h,k]
     | tmul x y=> unfold parityAct pinAct; simp_rw [TensorProduct.map_tmul]; congr 1; exact exterior_parity _ _ -- check
lemma tinted : ∃ b:Bool,∀ x:K.W, Ch T a (T.spin p x)=if b then T.parity (T.spin p (Ch T a x)) else T.spin p (Ch T a x):=by
    obtain ⟨u,h⟩:= chi_spec p s hp; refine ⟨u,fun x=>?_⟩; obtain ⟨d,v,rfl⟩:= hK.absorbs x
    change T.spin _ (T.adj _ _) = ite _ (T.parity _) _; simp only[Ch,LinearEquiv.trans_apply]; rw [T.w _ _ hp, T.a,T.a, T.w _ _ (couture a), T.w _ _ (couture a),T.w _ _ hp,T.p]; have ht:= rotateC p u h v.val
    cases u <;> simp only[Bool.false_eq_true,↓reduceIte] at * <;> apply congr_arg (K.focus none _) <;> apply Subtype.ext <;> simp only [RawSym.pinActs, RawSym.adjActs, RawSym.parityActs, rooted _ _ (couture a) (weave a), ht]
lemma spinWay {u_:Bool} (hv:t∈ Col T u_) : T.spin p t∈ Col T u_:=by
      rw [hue,spinClamp T hK p s hp,(hue T _ _).1 hv,map_smul]
omit hp
variable (u:Bool)
lemma litWay (hv:t∈Col T u):T.adj a t∈ Col T u:=by
      rw [hue, eyeP T hK a,(hue T _ _).1 hv,map_smulₛₗ]; cases u <;> simp [tauMod]
lemma chai (hv:t∈Col T u):Ch T a t∈Col T u:= spinWay T hK _ _ (couture a) (litWay T hK a u hv)
lemma twiceW(x:K.W): T.spin (flipC a) (T.spin (flipC a) x)=x:=by
     change (T.spin (flipC a)*_) _=_
     rw [← T.spine hK _ _ _ _ (couture a) (couture a),twiceR,T.spurs hK]; rfl
lemma steal(x:K.W) : T.spin (flipC a) (Ch T a x)=T.adj a x:= twiceW T hK a _
lemma blush : ∃ i:Bool,∀ x:K.W, Ch T a (Ch T a x)= if i then T.parity x else x:=by
      obtain ⟨i,hi⟩:= tinted T hK a _ _ (couture a); refine ⟨i,fun x=>?_⟩; have ht:= hi (T.adj a x); simp_rw [steal T hK a, T.reflex hK a x] at ht; exact ht
variable (q:EuPin)
include hp
lemma tolerates (hq:q.Lifts s) : T.spin p=T.spin q ∨ T.spin p=T.parity*T.spin q:=by
      let G:= MassiveTwoEstimates.SpinGeometry.geometry
      obtain h|h:= G.euFiber p q (hp.trans hq.symm); · exact Or.inl (h ▸ rfl)
      have hk:p*q⁻¹=(p*q⁻¹):=rfl
      have hu:(p*q⁻¹).coord=1:=by change p.coord*q.coord⁻¹=_; rw [hp.trans hq.symm, mul_inv_cancel]
      have he:(p*q⁻¹).matrix= -1:=by change p.matrix*q.matrix⁻¹=_; rw [h, neg_mul,mul_inv_cancel]
      have ht:=T.spine hK (p*q⁻¹) q 1 s (hu.trans (map_one Signed.inclusionO).symm) hq; rw [T.signs hK _ hu he, mul_assoc, inv_mul_cancel,mul_one] at ht; exact Or.inr ht
omit hp
-- ensure derivative preserves parity from exact invariance of same moments.
variable (hf:Foil P K T)
include hf
lemma arcing (a:Axis)(x:K.W): T.parity (K.arc a x)= K.arc a (T.parity x):=by
     refine detected hf _ _ fun n q r hr=> ?_
     let p:= T.parity ∘ q; have H : T.parity ∘ p=q:= funext fun i=>T.even hK (q i)
     have hc(u:K.W): T.parity ∘ Fin.cons u p=Fin.cons (T.parity u) q:=by rw[Fin.comp_cons,H]
     let W(t:K.W)(q:Fin n→K.W)(u):= K.total _ (Points.cons u (Points.tail r)) (Fin.cons t q)
     have hr₀: Points.cons (r 0) (Points.tail r)=r:=by ext i; refine Fin.cases ?_ (fun i=>?_) i <;> simp [Points.cons,Points.tail]
     have hℓ:Points.cons (r 0) (Points.tail r)∈conf _:= hr₀ ▸ hr -- check
     have heq: W x p=ᶠ[𝓝 (r 0)] W (T.parity x) q:=by
          have hX:Continuous fun y=>Points.cons y (Points.tail r):= Work.A02.continuous_cons.comp (continuous_id.prodMk continuous_const)
          filter_upwards [hX.continuousAt (x:=r 0)|>.eventually ((conf_open _).eventually_mem hℓ)] with y hy; unfold W; rw [← hc,hf.parity _ _ hy]
     have ht₁:= D_cons_ hK x p hℓ a; have ht₂:= D_cons_ hK (T.parity x) q hℓ a
     rw [heads,heads]; have hX:= heq.fderiv_eq (𝕜:=ℝ)
     calc
       _=K.total _ r (Fin.cons (K.arc a x) p) := by rw [←hc,hf.parity _ _ hr]
       _=Analysis.D (basis a) (W x p) (r 0) := by unfold W; rw [ht₁,hr₀]
       _=_ := by unfold W at *; rw [show D _ _ _= Analysis.D (basis a) (W (T.parity x) q) (r 0) from congr_arg (fun l:E4 →L[ℝ]ℂ=> l (basis a)) hX]; unfold W; rw[ht₂,hr₀]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.tinted
#print axioms YM.Massive.Gust.blush
#print axioms YM.Massive.Gust.tolerates
#print axioms YM.Massive.Gust.arcing
