import YM.Elix.Push
/-! Tensor family convergence and curl capsule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx.Gourd
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper SourceRead Oriole Patria.Rolls Tawny Cast Carnal
variable {C: Sequence}(T: TaperHol)(sym:RawSym)(B:Bore 6)(H:Bore 8)(hT:Rubric sym B)(hH:Rubric sym H)(F:ℕ→PatchMix 6)(hψ:∀ᶠ i in atTop,OrderMix (C.A i) T sym B (i:=0) (F i) ∧∃ W,Wager (C.A i) T H W 0)
variable (f:Flavor 6)(P: BudgetPoint)(n m:ℕ)(v a:ℝ)(hv:0<v)(hm:2 < m)(hn:3 ≤ n)
variable {β e:ℝ}(hp:C.Path β e)(hr:Tendsto (fun i=> ↑((C.S.side (C.R i) 0).val):ℕ→ℝ) atTop atTop)
variable (hQ:∀ᶠ i in atTop,∀ j k p:Axis,Tutor 0 P (Canvas.foil ((C.A i).density 0) (twig (C.A i) B (F i) f j k p 0)) v n m a)
include hp hT hH hm hn hψ hv hQ hr
set_option quotPrecheck false
local notation "ℓ" a:arg=> UV.first a
local notation "Ω"=> RawTensor (-1) 8
local notation "U"=> (0:Multi 8)
local notation "Gt"=> arcS f
lemma cuspDance (p:ℕ→Axis→Axis→Axis→Label 8)(H':∀ᶠ i in atTop,∀ j k l:Axis,Tally T 0 (p i j k l) ((C.A i).density 0) (trolley (C.A i) (branch (C.A i) B (F i) f j k l) (shelS k l) 0 0)):∀ i j:Axis,Tendsto (fun K=>∑ a:Axis,p K a i j) atTop (𝓝 ((arcS f).val (i,j))):=by
    let y(i:ℕ)(b: Axis × Axis) := ∑ j:Axis,p i j b.1 b.2; have hY:∀ᶠ i in atTop,y i ∈ Ω :=by
         filter_upwards [H',hψ] with i hi hx; obtain ⟨hv,W,hW⟩:=hx; exact bunch _ T sym B hT H hH W hW (hp.normalized _) _ hv f _ hi
    let D(i:ℕ):Ω := if h:y i ∈ Ω then ⟨y i,h⟩ else 0; have hD:∀ᶠ i in atTop,(D i).val=y i:=hY.mono fun i hi=>by unfold D; rw[dif_pos hi]
    have he(z:Flavor 6)(k l w:Axis) : let L(X:Ω):= prism0 z U (ℓ w) (X.val (k,l)).val; Tendsto (fun i=> L (D i)) atTop (𝓝 (L (arcS f))):=by
          intro L; apply tendsto_pi_nhds.mpr; intro x; apply tendsto_pi_nhds.mpr; intro y'; apply tendsto_iff_norm_sub_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) _ (g:=fun i=> 4*port a (C.S.side (C.R i) 0) v); swap
          · filter_upwards [hD,H',hψ,hQ] with i hi H he hQ; unfold L; rw [hi]; exact matters _ T sym B hT (hp.normalized _) _ he.1 _ k l _ H P n m v a hQ hm hn hv z x y' w
          simpa only [Function.comp_apply, port,div_eq_mul_inv,mul_zero,zero_mul] using ((((tendsto_inv_atTop_zero.comp hr).const_mul 80).mul_const (a * (v^2)⁻¹)).const_mul 4)
    letI :FiniteDimensional ℂ ↥Ω:=FiniteDimensional.finiteDimensional_submodule (K:=ℂ) (V:=Axis × Axis→ Label 8) Ω
    have ht': Tendsto D atTop (𝓝 (Gt)):=by
          apply (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr alternate)).isEmbedding.tendsto_nhds_iff.mpr; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; fin_cases j
          · refine ((feeP [0,1,0]).toContinuousLinearMap.continuous.continuousAt.tendsto.comp (he i 0 1 0)) -- top discrepancy matrix!
          refine ((feeP [0,1,2]).toContinuousLinearMap.continuous.continuousAt.tendsto.comp (he i 0 1 2))
    intro i j; refine (((continuous_apply (i,j)|>.comp continuous_subtype_val).continuousAt (x:=Gt)).tendsto.comp ht').congr' (hD.mono fun k hk=> congr_fun hk (i,j))
open Tarn Tarn.Choir Needle
variable (Q:Choir){Z:Calibration C}{K:∀ d,Cottage Z d}{φ:ℕ→ℕ}(hS:Sway C.S)(hφ:Tendsto φ atTop atTop)(h:Q.Harmony Z φ)(L:ℕ→ℕ)(hL:∀ i:ℕ,i ≤ L i)(hq:∀ i a b c,stemV Z 6 i (shelC a b c) (gamma6 f a b c)=skyH (C.A i) B (F i) f a b c)(hw:∀ a b c:Axis,∃ p:ℕ→Label 8, Needle.Weave Z L T 0 (shelS b c) (fun i=>branch (C.A i) B (F i) f a b c) p)
include h hS K hφ hq hw hL
lemma upright(i j:Axis): (∑ k:Axis,Q.arc k (Q.focus (shelC k i j) 6 (gamma6 f k i j)))= Q.focus (shelS i j) 8 ((arcS f).val (i,j)):=by
     choose p hP using hw; have ht:= cuspDance T sym B H hT hH F hψ f P n m v a hv hm hn hp hr hQ (fun i a b c=> p a b c i) (eventually_all.mpr fun i=>eventually_all.mpr fun j=>eventually_all.mpr fun k=> (hP i j k).sees) i j
     let z:=∑ a:Axis,p a i j; let A:= C.A; let x:=(arcS f).val (i,j); let v':=fun a:Axis=> shelC a i j
     have he :Tendsto z atTop (𝓝 x):=by convert! ht using 1
     apply Measures.coupled hp hS hφ h x z he L 6 (shelS i j) v' (fun a:Axis=> gamma6 f a i j) 0 T (fun a=>can_go a [i,j] (by simp)) hL _ (G:=K); have hc(a:Axis):Weave Z L T 0 (shelS i j) (fun s=> Rolls.nick (C.S.spacing (C.N s))⁻¹ a (stemV Z 6 s (shelC a i j) (gamma6 f a i j))) (p a i j):=by simp_rw[hq]; exact hP a i j
     exact Weave.graduated (hc 0) _ _ _ (fun i _=>hc i)
end YM.Massive.Patria.Gall.Onyx.Gourd
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.upright
