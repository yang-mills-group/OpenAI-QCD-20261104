import YM.DawnS.Mar
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder ENNReal
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Y"=>Vertex
local notation "Ω"=>muS
variable {d:ℕ}(a b:Peak d→ℂ) (c:Bool)(r:ℝ)(hr:0<r)(i:Pinor)
noncomputable def twins (x:PR) :ℂ:=priceK r x.1 * (star (bandIT a x r c i) * bandIT b x r c i)
lemma twist (x:PR): twins a b c r i x=∑ p:Peak d,∑ q:Peak d,(star (a p)* b q) * sparksT p q c r i x:=by
    unfold twins bandIT; rw[star_sum, sum_mul,mul_sum]; simp_rw [mul_sum]; apply Finset.sum_congr rfl fun j _=> ?_; apply Finset.sum_congr rfl; intro p _; unfold sparksT; rw [star_mul]; ring
lemma urge : Integrable (twins a b c r i) wa ∧ ∫ z:PR, twins a b c r i z ∂wa=∑ p:Peak d, ∑ q:Peak d,star (a p)* b q* ∫ z:PR,sparksT p q c r i z ∂wa:=by
    let f(p q:Peak d)(x:PR):=(star (a p)*b q)* sparksT p q c r i x
    have h(p q:Peak d):Integrable (f p q) wa:=(flows p q r c i).1.const_mul _; have hx(p): Integrable (fun z=> ∑ q,f p q z) wa:=integrable_finsetSum _ fun q _=> h p q
    rw [funext (twist a b c r i)]; refine ⟨integrable_finsetSum _ fun p _=> hx p,?_⟩; rw[integral_finsetSum _ (fun p _=> hx p)]; apply Finset.sum_congr rfl; intro j _; rw [integral_finsetSum _ (fun q _=> h j q)]; exact Finset.sum_congr rfl fun _ _=> integral_const_mul _ _
lemma sparkSum(k: Flavor 6)(t: Hue)(hr:0<r) :let A : (Peak d →ℂ)→ beam d :=fun a => ∑ i,a i • UAtom k t c i; (2:ℂ)*sigL r (A a) (A b) = ∑ i:Pinor,∫ z:PR,twins a b c r i z ∂wa:=by
    intro A; unfold A; simp only [map_sum,map_smul,map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply, smul_eq_mul]; rw [Finset.mul_sum];
    simp_rw [Finset.mul_sum,(urge a b c r _).2,(show ∀ i j:Peak d,(2:ℂ)*(b j*((starRingEnd ℂ) (a i)* sigL r (UAtom k t c i) (UAtom k t c j)))= ∑ s:Pinor,(star (a i)* b j)* ∫ z:PR,sparksT i j c r s z ∂wa from fun i j=>by rw[←mul_sum,←ricket i j t k r hr c]; change (2:ℂ)*(b j*(star (a i)*_))=_; ring)]
    rw[Finset.sum_comm, Finset.sum_comm (f:=fun (i:Pinor) p=>_)]; refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]
noncomputable def chargeP (a:Peak d→ℂ)(c:Bool)(r:ℝ)(i:Pinor)(z:PR):=priceK r z.1 * ‖bandIT a z r c i‖^2
lemma twinsP : twins a a c r i=fun z:PR=> (↑(chargeP a c r i z):ℂ):=by
     ext1 z; unfold twins chargeP; let x:= bandIT a z r c i; push_cast; rw [show (↑‖x‖:ℂ)^2=star x*x from ?_]
     rw[←Complex.ofReal_pow,Complex.sq_norm,x |> mul_comm (star x),Complex.star_def, Complex.mul_conj]
lemma aura(h:0≤r): ∀ᵐ z∂wa,0< (Prod.fst z):=by
     unfold wa; rw [Measure.ae_prod_iff_ae_ae (show MeasurableSet {z:PR|0<z.1} from measurable_fst measurableSet_Ioi)]; filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact Eventually.of_forall fun y=> hx
lemma zeal : Integrable (chargeP a c r i) wa:=by have h:=(urge a a c r i).1; rw [twinsP] at h; exact h.re
lemma ahead (hr:0<r) : 0 ≤ ∫ z,chargeP a c r i z ∂wa:= integral_nonneg_of_ae (Eventually.mono (aura (r:=r) hr.le) fun z h=> mul_nonneg (prices_pos _ _ h hr).le (_root_.sq_nonneg _))
lemma shading (hr:0<r)(h:(∫ z, chargeP a c r i z ∂wa)=0) (x:PR)(hx:x.1>0): bandIT a x r c i=0:=by
    let Z:=chargeP a c r i; let S:Set PR:=Set.Ioi (0:ℝ) ×ˢ Set.univ; have hf: IsOpen S:= isOpen_Ioi.prod isOpen_univ
    have ht : Continuous Z:=(((show Continuous (priceK r) by unfold priceK; fun_prop).comp continuous_fst).mul ((hazed a r c i).norm.pow _)); by_contra hv; have hZ: x∈ S:= ⟨hx, Set.mem_univ _⟩;
    let U:= Z⁻¹'(Set.Ioi 0); have hu : x∈U:=mul_pos (prices_pos _ _ hx hr) (pow_pos (norm_pos_iff.mpr hv) _);
    let V:= (volume:Measure ℝ).prod muS; have hw :0<V (U∩ S):=((ht.isOpen_preimage _ isOpen_Ioi).inter hf).measure_pos V ⟨x,hu,hZ⟩
    have hK : V.restrict S=wa:=by unfold V S; rw [← Measure.prod_restrict,Measure.restrict_univ]
    have hA:=((integral_eq_zero_iff_of_nonneg_ae (show (0:PR→ℝ)≤ᵐ[wa] Z from (aura _ hr.le).mono fun z h=> mul_nonneg (prices_pos _ _ h hr).le (_root_.sq_nonneg _)) (zeal a c r i)).mp h)
    have hU : wa U=0:= MeasureTheory.measure_mono_null (t:={z:PR| ¬ (Z z=0)}) (fun z h=> (show 0<Z z from h).ne') (ae_iff.mp hA)
    rw[← hK, Measure.restrict_apply ((ht.isOpen_preimage _ isOpen_Ioi).measurableSet)] at hU; exact hw.ne' hU
end YM.DawnS
