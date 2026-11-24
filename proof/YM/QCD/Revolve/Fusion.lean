import YM.QCD.Revolve.Paint

/-!
# convergence of the symmetry projectors. Blends at widths specified after birth stations
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Revolve
open Lat Function Lattice Wilson Kit Pine Cost Eyrie Quarry Rudder RG Finset Filter Stationary Sparks
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n : Side}{k : ℕ}{I J: Type}{P : I→Bloom k}{V : J→ Bloom k}{r t u b C:ℝ}
lemma reserves (u:ℝ)(ht:0≤u)(hP:Fractal P r C)(he:u*(1+k) ≤ r): Fractal (clover∘P) u C:=by
  have h i: ((clover∘P) i).paid u ≤ (P i).paid r:=(clover_le (P i) u ht).trans (thinner _ he)
  have hv:= hP.bills.of_nonneg_of_le (fun i=> (clover (P i)).price_nn.trans ((clover (P i)).paidUp ht)) h
  exact ⟨ht,fun i=>clover_s _ (hP.sect i),hv,(hv.tsum_le_tsum h hP.bills).trans hP.bill⟩
lemma hex (h : Fractal P r C) (U:Grid n) : dust (clover ∘ P) n U=newborn n (dust P n U):=by
  unfold dust; have he i:(clover (P i)).tonic 0 U=newbornL n ((P i).tonic 0 U):=clover_chi (P i) (h.sect i) 0 U
  simp only [Function.comp_apply, he]; exact ((newbornL n).map_tsum (h.tonics ..).of_norm).symm

def frost (P : I→Bloom k)(i : I⊕I):Bloom k:= shape (Sum.elim P (clover∘P) i) (↑((2:ℝ)⁻¹))
lemma forrest (u:ℝ)(ht:0≤u)(hP:Fractal P r C)(he:u*(1+k)≤r):Fractal (frost P) u C := by
  have hb : u≤r:= (le_mul_of_one_le_right ht (by simp)).trans he
  have hp:= shape_ok (joins (reduction hP ht hb le_rfl) (reserves _ ht hP he)) (↑((2:ℝ)⁻¹)); exact reduction (P:=frost P) hp ht le_rfl (le_of_eq (by norm_num; ring))
lemma icicle (h : Fractal P r C)(U:Grid n) : dust (frost P) n U=occult (dust P n) U:=by
  have ht:=reserves 0 le_rfl h (by rw [zero_mul]; exact h.degree)
  unfold frost; rw [lit,gemini U h ht,hex h]; rfl

abbrev Fruited (I:Type):= (Signed × I)⊕(Signed×I)
def frosting (P : I→Bloom k):Fruited I→Bloom k:= frost (feast P)
def ceiling (r:ℝ)(k:ℕ)(C:ℝ):= Real.exp (r*(2*k))*C
lemma coined (u:ℝ)(ht:0≤u)(h:Fractal P r C)(he:u*(1+k)≤r):Fractal (frosting P) u (ceiling r k C):=forrest _ ht (invested h) he
-- operates on germ after matching
lemma coined_inv (h:Fractal P r C) : dust (frosting P) n=occult (hearth (dust P n)):=by
  unfold frosting; funext x; rw [icicle (invested h),funext (routed h)]
structure Majestic (A:LegInk n):Prop where
 port : MirrorF A
 lane (x):A x=newborn n (A x)
lemma coined_port (h:Fractal P r C):Majestic (dust (frosting P) n):=by rw [coined_inv h]; exact ⟨fire_m _ (roaring _),fun x=>(occult_t ..).symm⟩
-- syntax for comparing birth test
variable {W:LegInk n}{B F:trackG n}
def Tender (F B:trackG n)(k:ℕ):Prop:= EmptyThrough (F-B) k ∧ ContDiffAt ℝ ω F 0 ∧ ContDiffAt ℝ ω B 0
def castF (W: LegInk n) : trackG n:= W∘input su n

lemma orbitPay (h:Noble F)(H:Tender F (castF W) k)(s:Signed):
    Tender F (castF (inverted W s)) k:=by
  let g:= castF W; let P:= orderTurn (m:=n) (G:=su) s
  let B:= scaleA s n
  obtain ⟨L,hl⟩:= auraCL (star B)
  have hp : F =ᶠ[𝓝 0] L ∘ F ∘ P:=by
    filter_upwards [h.praised s] with x hx
    change _=L (F (orderTurn s x)); rw [hl,hx]; unfold B; rw [show aura (scaleA s n)= aura (star (star (scaleA s n))) by rw [star_star]]; exact (inverse_aura _ (B:=star B) (Unitary.star_mem (colour_wheel (gems s n) (fleetLeft s)))).symm
  have h':castF (inverted W s)=L ∘ g ∘ P:=by
    funext x; simp only [Function.comp_apply, castF,inverted,g]; rw [hl]; erw [flip_links s x]; rfl
  have ha : ContDiffAt ℝ ω F (P 0):=by rw [map_zero]; exact H.2.1
  have hr : ContDiffAt ℝ ω g (P 0):=by rw [map_zero]; exact H.2.2
  rw [h']; refine ⟨fun i hi=> ?_, H.2.1,L.contDiff.contDiffAt.comp _ (hr.comp _ P.contDiff.contDiffAt)⟩
  have he : F - (L ∘ g ∘ P)=ᶠ[𝓝 0] L ∘ (F-g) ∘ P:= (hp.sub (@EventuallyEq.refl _ _ _ (L ∘ g ∘ P))).mono (fun i hi => by
    change _= L (F _ - g _); rw [map_sub]; exact hi)
  rw [(he.iteratedFDeriv ℝ i).eq_of_nhds,L.iteratedFDeriv_comp_left ((show ContDiffAt ℝ ω (F-g) (P 0) from ha.sub hr).comp _ P.contDiff.contDiffAt) le_top, Push.Uniform.iter_lin_at (L:=P) (by rw [map_zero]; exact (H.2.1.sub H.2.2).of_le le_top),map_zero,show iteratedFDeriv ℝ i (F-g) 0=0 from H.1 i hi]; ext; simp

lemma agree_test (hp : Noble F)(hc : Tender F (castF W) k) : Tender F (castF (hearth W)) k:=by
  let A i:= (castF (inverted W i)); let D := (↑(Fintype.card Signed):ℝ)⁻¹
  have hK : (↑(Fintype.card Signed):ℝ)≠0:=by exact_mod_cast Fintype.card_pos.ne'
  have ht : castF (hearth W)=D • ∑ i,A i:=by funext i; rw [Pi.smul_apply,Finset.sum_apply]; rfl
  have hg : F-castF (hearth W)=D • ∑ i:Signed,(F-A i):=by
    have h (u:trackG n): D • Fintype.card Signed • u=u:=by rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; unfold D; rw [inv_mul_cancel₀ hK,one_smul]
    rw [ht,sum_sub_distrib,smul_sub,sum_const, card_univ,h]
  have hu i:= orbitPay hp hc i
  have hh i : ContDiffAt ℝ ω (A i) 0:= (hu i).2.2
  have he i : ContDiffAt ℝ ω (F-A i) 0:= hc.2.1.sub (hh i)
  refine ⟨fun i hi=>?_,hc.2.1,?_⟩
  · have hS: ContDiffAt ℝ i (∑ i:Signed,(F-A i)) 0:=by rw [show (∑ i:Signed,(F-A i)) = (fun x=> ∑ i:Signed,(F-A i) x) from funext fun i=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> (he i).of_le le_top
    rw [hg, iteratedFDeriv_const_smul_apply hS, iteratedFDeriv_sum_apply (fun i _=> (he i).of_le le_top), sum_eq_zero (fun j _=> (hu j).1 i hi),smul_zero]
    -- check hs
  rw [ht]; have hS:ContDiffAt ℝ ω (∑ i,A i) 0 := by rw [show (∑ i,A i)=(fun x=>∑ i,A i x) from funext fun i=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> hh i
  exact hS.const_smul D
end YM.QCD.Revolve
