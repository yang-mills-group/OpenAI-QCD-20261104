import YM.Lust.Leaf
/-! Quantitative frame inversion for ALL averaging conventions on common kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} {P:Calibration C} {d:ℕ}{E:Hub.Invest P d}{H:Rack E} (h:Wealthy H)(hS:Spring P d)(G:Capital P d 1)
namespace GaugeP
variable {Z: Laurel d}{J: Landing P.sym Z}(K:GaugeP P Z J){β ν:ℝ}(hC:C.Path β ν)(hr:Sway C.S)
namespace LensZ
variable {u:Averaging}(L: LensZ P Z J u)
local notation "a" i:arg=>C.S.spacing (C.N i)
local notation "T₀"=> Stokes d
local notation "Ψ" i:arg=>stemV P d i u
local notation "F₀" i:arg=>L.g i
noncomputable def mat (i:ℕ)(z:stalk C i): Stokes d →ℂ:=fun t=> L.checkP i (stemV P d i u (L.g i t)) z
lemma bill2 (i:ℕ)(j:ℕ)(ht: j+1≤ C.N i)(hu:L.ℓ ≤ C.N i)(hs:∀ t w:↥(Lattice.box (CardsT.flex C.S L.ℓ (C.N i))), seaM C i j (![t.val, ratioTo C.S (C.N i) L.ℓ • L.x+w.val]:Fin 2→ Cover))(hr:6*2<(C.S.step j).L.val)(hC:C.Path β ν)(X Y:stalk C i)(A B:ℝ)(hX:GreenP C i j X A)(hY: GreenP C i j Y B): ‖checkP L i X Y‖ ≤ A *B:=by
    let f : Fin 2→ stalk C i := ![X,Y]; let h :Fin 2→ℝ:=![A,B]; have hp(k:Fin 2) : GreenP C i j (f k) (h k):=by fin_cases k; exact hX; exact hY
    apply bill L hu X Y; intro t w; have he:= reapS i j f h hC hp _ (hs t w) hr ht; simpa only [readS,List.ofFn_zero,List.ofFn_succ,List.prod_nil,List.prod_cons,mul_one,h,f,Fin.prod_univ_succ,Finset.univ_eq_empty,Finset.prod_empty, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using he
-- lower stability on ALL rows vs candles via authentic checks.
noncomputable def spur (i:ℕ):(Stokes d→ℂ)→ₗ[ℂ]Label d where
   toFun p:=∑ j,p j • L.h i j
   map_add' p q:=by simp only [Pi.add_apply,add_smul,sum_add_distrib]
   map_smul' p q:=by simp only [Pi.smul_apply,smul_smul,smul_eq_mul,RingHom.id_apply,smul_sum]
lemma leaves(i:ℕ)(h:L.ℓ ≤ C.N i)(x y:stalk C i): checkP L i x y=L.checkLinear i x h y:=rfl
include hC
lemma heightQ :∀ᶠ i in atTop,∀ p:Stokes d→ ℂ, ‖p‖ ≤ J.J*‖L.mat i ((Ψ i) (L.spur i p))‖:=by
   filter_upwards [L.sees,hC.uv.tendsto_atTop.eventually_ge_atTop L.ℓ] with i hi ht p
   let f (j k:Stokes d):= L.mat i ((Ψ i) (L.h i k)) j
   apply (J.warmth (show nearG P.sym Z J.ε f from hi) p).trans_eq; apply congr_arg; apply congr_arg Norm.norm; ext1 j
   change ∑ k, f j k*p k= checkP L i _ ((Ψ i) (∑ k,p k • L.h i k)); rw [leaves L i ht,map_sum, map_sum]; apply Finset.sum_congr rfl; intro k _; rw [map_smul,map_smul]; exact mul_comm ..
omit hC
lemma pricingW : ∃ C:ℝ,0≤C∧∀ᶠ i in atTop,∀ p:T₀ →ℂ, ‖L.spur i p‖ ≤ C*‖p‖:=by
    let n:ℝ:=Fintype.card T₀; refine ⟨n*L.T,mul_nonneg (by unfold n; positivity) L.pos,?_⟩; filter_upwards [L.tallest] with i hi p; change ‖∑ j,p j • L.h i j‖ ≤ _; apply (norm_sum_le ..).trans; have ht(j:T₀): ‖p j • L.h i j‖ ≤‖p‖*L.T:=by rw[norm_smul]; exact mul_le_mul (norm_le_pi_norm p j) (hi j).2 (norm_nonneg _) (norm_nonneg _)
    exact (sum_le_sum (fun i _=> ht i)).trans_eq (by simp only [Finset.sum_const, card_univ,nsmul_eq_mul]; unfold n; ring)
include h hS hC G hr
lemma checksW : ∃ C:ℝ,0 ≤ C∧∀ᶠ i in atTop,∀ p:T₀→ℂ, ‖p‖ ≤ C* ‖(glean (E:=E) K u i) (L.spur i p)‖:=by
    obtain ⟨e,he,hf⟩:=L.fore hC
    obtain ⟨Q,hQ,Hq⟩:= L.pricingW
    obtain ⟨N,hN⟩:=eventually_atTop.mp (((card h hS G K hC hr u).and (K.vine G)).and (hr.high.eventually_gt_atTop (6*2)))
    obtain ⟨j,hj,hJ⟩:= shyness hC e he N; obtain ⟨⟨⟨A,M,hA,hM,F,hF,H⟩,B,hB,H'⟩,hx⟩:= hN j hj
    let C:= J.J; let T:= L.T*A; have hp:0≤T:=mul_nonneg L.pos hA
    let f(i):= C*(T* (Q* F i)); have ht:Tendsto f atTop (𝓝 0):=by simpa only[f,mul_zero] using ((hF.const_mul Q).const_mul T).const_mul C
    refine ⟨2*C*(T*B),mul_nonneg (mul_nonneg (by norm_num) J.fee) (mul_nonneg hp hB),?_⟩; filter_upwards [Hq,hf,H,H',hC.uv.tendsto_atTop.eventually_ge_atTop L.ℓ,hC.uv.tendsto_atTop.eventually_ge_atTop (j+1),ht.eventually_le_const (show (0:ℝ)<1/2 from by norm_num),L.tallest,L.heightQ hC] with i hi hz h hh hu hm hI hT hK p
    let x:= L.spur i p; let q:=(glean (E:=E) K u i) x; let k:=stem P d i (K.ridge i q); let X:= (Ψ i) x; let Z:=X-k
    have hg(s:T₀) : GreenP _ i j ((Ψ i) ((F₀ i) s)) T:= GreenP.mono (h.2 (L.g i s)).1 (mul_le_mul_of_nonneg_right (hT s).1 hA) -- naming C shadow
    have h'V:= (mul_nonneg (norm_nonneg p) hB); have hv := h.1
    have hw:GreenP _ i j Z (Q*‖p‖ * F i):= GreenP.mono (h.2 x).2.2 (mul_le_mul_of_nonneg_right (hi p) h.1)
    let V(i':T₀):= checkLinear L i ((Ψ i) (L.g i i')) hu
    have ha : ‖p‖ ≤ C*(T*(‖q‖*B)+T*(Q*‖p‖*F i)):=by
         apply (hK p).trans; apply mul_le_mul_of_nonneg_left _ J.fee; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun v=>?_; change ‖V v X‖≤_; rw [show X=k+Z from (by unfold Z; abel), map_add]; apply (norm_add_le ..).trans
         have hz(t w):= tide j i _ (hz t w) (le_trans (Nat.le_succ _) hm) hJ
         exact add_le_add (bill2 L i j hm hu hz hx hC _ _ T _ (hg _) (hh q)) (bill2 L i j hm hu hz hx hC _ _ T _ (hg _) hw)
    have h : C*(T*(Q*F i))≤1/2:= hI; change _ ≤ _*‖q‖; nlinarith only [ha,mul_le_mul_of_nonneg_right h (norm_nonneg p)]
end LensZ
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.LensZ.checksW
