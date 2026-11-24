import YM.Mural.Lipid
/-! # Ex ante ratios for carriage. Polynomial costs after P choices.
 Choose any fixed affordability ratio C for both Log and Hard K on reset.
 r>1/2 ensures. v residual envelope bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
lemma gapsR (j:ℕ)(C:ℝ)(hC:0<C) :∃ l:ℕ,∀ L:Side, l ≤ L.val → C* (Kit.scale L)^2*(strideL j L) ≤1:=by
    let N:=2*(4*(j+3))+1; let hv(L:Side):0<(L.val:ℝ):= sidePrice _; let c:ℕ:=N^4*(berthD j+berthD j+1)^4; let r:= C*c
    refine ⟨⌈r⌉₊,fun L hl=>?_⟩; have ht:(strideL j L:ℕ)≤ c* L.val ^4:=by
       let Q:= (2*(4*(j+3))*L.val+1); have h: (arctic L j+arctic L j+1)=Q:=by unfold Q arctic; ring
       have hp:Q ≤ N*L.val:=by unfold Q N; rw [add_mul,one_mul]; have h:0<L.val:= L.property; omega
       unfold strideL c; rw [h]
       calc _ ≤ ((N*L.val)^4 * (berthD j+berthD j+1)^4) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp 4)
            _=_:=by rw [mul_pow]; ring
    let l:ℝ:= L.val; have hh:0<l:=hv _; have hc:r≤l:= (Nat.le_ceil _).trans (Nat.cast_le.mpr hl); have hS: Kit.scale L^2=(l^5)⁻¹:=by unfold Kit.scale Kit.slope; rw [div_pow,inv_pow,Real.sq_sqrt hh.le]; field_simp [hh.ne']; ring -- sqrt syntax.show.
    calc _ ≤ C* (Kit.scale L)^2*(c*l^4):=mul_le_mul_of_nonneg_left (by have h:(strideL j L:ℝ) ≤ (↑(c*L.val^4:ℕ):ℝ):= Nat.cast_le.mpr ht; exact h.trans_eq (by simp only [Nat.cast_mul,Nat.cast_pow]; rfl)) (mul_nonneg hC.le (sq_nonneg _))
         _=C*c/l:=by rw [hS]; field_simp
         _ ≤1:=(div_le_one hh).mpr hc
lemma leasesR (j:ℕ)(C p:ℝ)(hp:0 ≤ p)(h:0<C) : ∃ (n:ℕ),∀ L:Side,n ≤ L.val→∀ (R:TokenP)(w D F r v:ℝ), 0<w → 0≤D → 0≤F → R.v ≤ C*D → R.s ≤ C*F → (1:ℝ)/2 ≤ r → 0≤v → 4*(strideL j L)*(8*p) ≤ w*v/2 → TollG R L j r w D F (8*p) v p:=by
   obtain ⟨A,hA,hx⟩:= place_limit; let t:ℝ:= Fintype.card Rank; have ht:0<t:=by unfold t; positivity
   let k:= (t*C)⁻¹; have he: 0<k:= inv_pos.mpr (mul_pos ht h); obtain ⟨n₁,h₁⟩:= gapsR j 8 (by norm_num); obtain ⟨n₂,h₂⟩:=gapsR j (8*(A^2*k⁻¹)) (by positivity)
   refine ⟨n₁+n₂,fun L hL R w D F r v hw hD hF hv he' hr ht' h'=>?_⟩
   let f:= k*(A*Kit.scale L)⁻¹^2; let s:= Kit.scale L; have hs:0<s:=Kit.scale_pos _; have hf:0<f:=by unfold f; change _*(A*s)⁻¹^2>0; positivity
   have hh:f=s⁻¹^2*k*(A^2)⁻¹:=by unfold f; change k*(A*s)⁻¹^2=_; field_simp
   have hh₁ : (4:ℝ)*s^2*(strideL j L) ≤ 1/2:=by have hp:=(h₁ L (by omega)); change 8*s^2 * _ ≤ _ at hp; linarith only [hp]
   have hh₂: 4*f⁻¹*(strideL j L) ≤1/2:=by rw [hh]; have hK:=h₂ L (by omega); change 8*(A^2 * k⁻¹)*s^2 * _ ≤ _ at hK; simp only [mul_inv_rev,inv_inv,←inv_pow]; nlinarith only [hK]
   have hr0:0<r:=by linarith
   have hy: ‖(r:ℂ)⁻¹^2‖ ≤4:=by
         rw [norm_pow,norm_inv,Complex.norm_real, Real.norm_of_nonneg hr0.le]; calc _ ≤ (((1/2:ℝ))⁻¹)^2:= pow_le_pow_left₀ (inv_pos.mpr hr0).le (inv_anti₀ (by norm_num) hr) _
                                                                                   _= _:=by norm_num
   refine ⟨A,f,w,k,hx,hA.le,Complex.ofReal_ne_zero.mpr hf.ne',Complex.ofReal_ne_zero.mpr hw.ne',by rw [Complex.norm_real,Real.norm_of_nonneg hw.le],?_, ?_,?_, ?_,?_⟩
   · rw [Complex.norm_real, Real.norm_of_nonneg hf.le, show f*(A*s)^2=k from (by unfold f; change k*(A*s)⁻¹^2*(A*s)^2=k; field_simp)] -- rw closes?
   · have h':=(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv he.le) ht.le); apply h'.trans_eq; unfold k; field_simp
   · have h':=(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' he.le) ht.le); apply h'.trans_eq; unfold k; field_simp
   · have hV:(4:ℝ)*s^2*(strideL j L)*(8*p)≤(1/2)*(8*p):=mul_le_mul_of_nonneg_right hh₁ (mul_nonneg (by norm_num) hp)
     apply (mul_le_mul_of_nonneg_right hy (by positivity : (0:ℝ) ≤ p+strideL j L*(8*p*s^2))).trans; nlinarith only [hV]
   simp only [norm_inv, Complex.norm_real, Real.norm_of_nonneg hf.le, Real.norm_of_nonneg hw.le]; have hx':4* (strideL j L:ℝ)*(8*p)*w⁻¹≤v/2:=by rw [← div_eq_mul_inv]; exact (div_le_iff₀ hw).mpr (h'.trans_eq (by ring))
   apply (mul_le_mul_of_nonneg_right hy (by positivity : 0 ≤ (strideL j L:ℝ)*(8*p*w⁻¹+v*f⁻¹))).trans; nlinarith only [hx',mul_le_mul_of_nonneg_right hh₂ ht']
end YM.QCD.Comet
#print axioms YM.QCD.Comet.leasesR
