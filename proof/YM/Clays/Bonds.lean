import YM.Clays.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c:Side}{N:ℕ}{I D:Type}[Fintype I]{a C t b w x v θ m:ℝ}
variable (o:I→Site c)(p:I→Lat.Fields c 6→L[ℂ]Lat.Fields c 6) (H:∀ i,Veins (o i) (p i) C) (s:List I)(d:I→ℂ)
local notation "P"=> Patio (Keys c 6⊕Spine I)
local notation "T"=> traceI I
local notation "Λ"=> Keys c 6
local notation "K"=> actE o p H d s
local notation "Γ"=> effect o p H d
local notation "amt" j:arg=> (s.filter (fun i=> i∈ (j:Finset I)))
variable (F: Reel c 6 I D) {U:BudgetPoint}
set_option quotPrecheck false
local notation "B!"=> U.B
-- W debit formula.Hit.Φ_F.e of E with gap.I.Blue
variable (f:D→Site c)(g:D→ℝ)(h:ValidX o F f g U t)
local notation "E"=> Oper o s F
local notation "Ψ"=> clayR o p H s d F
open ConnectedActivityE6 Blaze King Reserves
omit [Fintype I] in
lemma income (v:ℝ)(hv:0≤v)(Z: Finset I): (∑ i∈ Z.powerset with i.Nonempty, v^i.card) ≤ (Z.card:ℝ)*v*Real.exp ((Z.card:ℝ)*v):=by
     let i:= Z; let W:=∑ i∈Z.powerset.erase ∅,v^i.card; have h:∀ Z:Finset I,(∑ i∈Z.powerset,v^i.card)=(1+v)^Z.card:=by
          intro Z; induction Z using Finset.induction_on with
          | empty=> simp
          | insert i Z hi ih=> rw [sum_powerset_insert hi,card_insert_of_notMem hi,pow_succ',add_mul,one_mul, ←ih]; refine congr_arg (fun x=> _+x) ?_; rw [mul_sum]; refine sum_congr rfl fun j hj=>?_ ; rw [card_insert_of_notMem (fun he=> hi ((mem_powerset.mp hj) he)),pow_succ']
     let k:ℝ:=(Z.card:ℝ)*v; have hh: W+1 ≤ Real.exp k:=by
          have hW: W+ v^(∅:Finset I).card=∑ i∈Z.powerset,v^i.card:= sum_erase_add _ (fun i:Finset I=> v^i.card) (by simp); simp only [card_empty,pow_zero] at hW; rw [hW,h]; rw [show Real.exp k=(Real.exp v)^Z.card from Real.exp_nat_mul ..]; exact pow_le_pow_left₀ (by linarith) ((add_comm 1 v).le.trans (Real.add_one_le_exp _)) _
     rw [show Finset.filter _ Z.powerset=Z.powerset.erase ∅ from ?_]; rotate_left
     · ext y; simp [nonempty_iff_ne_empty, and_comm]
     have he: (-k+1)*Real.exp k ≤ 1:= (mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-k)) (Real.exp_pos _).le).trans_eq (by rw [Real.exp_neg]; exact inv_mul_cancel₀ (Real.exp_ne_zero _)); linarith only [hh,he] -- W delta
noncomputable def kingP (n k:ℕ):=2+n*k +2
noncomputable def roy (B n k:ℕ):ℝ:=(4*(B:ℝ)+2)^(kingP n k) -- bound 2B+1 ≤4B+2.
lemma taste_eq (S:Support c): taste U S= (1+(wag S U.B:ℝ))^(kingP U.order U.power):=by unfold taste Plate.reFee kingP; rw [Nat.mul_comm U.order, ←pow_add]; -- edit
lemma taste_le (S:Support c): taste U S ≤ roy U.B U.order U.power*(1+(coverNumber U.B S:ℝ))^(kingP U.order U.power):=by
      rw [taste_eq]; unfold roy; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); unfold wag; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) U.B]
noncomputable def hullP (B Fi:ℕ):ℝ:= ((B:ℝ)+B+1)^4 * Fi
noncomputable def absP (B n k M:ℕ)(ε v:ℝ):ℝ:= roy B n k *hullP B M*polyPrice ε (kingP n k+1)*v
variable (hr: ∀ i:I, ‖d i‖≤a)(ha:0≤a)(hC:0 ≤ C)(ht:0<t)(hs:s.Nodup)
include ha hr hC ht hs H h
local notation "ψ"=> extreme o s F g U a C
-- charge on all nonempty including new singles. reach Anchor.Light.By exterior words ∑.
variable (Ft:ℕ) (hf:Fires o Ft)(ε:ℝ)(he:0<ε)(u T':ℝ)(hV:Ac.Hit (fun i=>(F.addr i).support) U.B g (v+2*ε) T')
local notation "A₀"=> absP U.B U.order U.power Ft ε (C*a)*T'
include hV he hf
set_option maxHeartbeats 720000 in
lemma pricing (hX:hullP U.B Ft*(C*a) ≤ ε) : Ac.Hit (fun i:E=> ((Ψ).addr i).support) U.B ψ v A₀:=by
      let Q:= C*a; have hQ:0≤Q:=mul_nonneg hC ha; let R:= polyPrice ε (kingP U.order U.power+1); let M:= hullP U.B Ft; let Z:= roy U.B U.order U.power; let C':=absP U.B U.order U.power Ft ε Q; have hm:0≤ M:=by unfold M hullP; positivity
      have hz:0≤ Z:=by unfold Z roy; positivity
      have hr':0 ≤ R:=by unfold R polyPrice; positivity
      have hx:0≤ C':=by change 0≤ Z*M*R*Q; positivity
      intro j; let S i:=(F.addr i).support; let w i:=coverNumber U.B (S i); let X i:= if j∈S i then g i * Real.exp ((v+2*ε)*w i) else 0; let τ(i:E):= (ψ i); let f(i:E):= if j∈S i.fst then τ i*Real.exp (v*w i.fst) else 0
      have h1(i:E):0≤τ i:= (prize o p H s d F _ _ h hr ha hC ht hs i _ (F.addr _).anchor).travels; have hn(i:E):0 ≤ f i:=ite_nonneg (mul_nonneg (h1 i) (Real.exp_nonneg _)) le_rfl
      refine budget_fiberwise (f:=f) (fun i:E=>i.fst) hn ?_ (budget_scale hx (hV j)); intro i u huh; let L:= matings o s F i; let it:= Sigma.mk i (β:=fun i=>↥(matings o s F i)); have hh:u ⊆ Finset.univ.image it:=by rintro ⟨k,y⟩ h; have he:k=i:=huh _ h; subst k; exact mem_image_of_mem _ (mem_univ _)
      refine (sum_le_sum_of_subset_of_nonneg hh (fun i _ _=>hn i)).trans ?_; rw [sum_image (show Set.InjOn it _ from fun i _ j _ h=> (Sigma.mk.inj_iff.mp h).2|>eq_of_heq)]
      change ∑ j:↥L,f (it j) ≤ C'*X i; unfold X; split
      swap; next hp=> rw [sum_eq_zero (fun i _=> if_neg hp),mul_zero]
      next h0=>
          let k:ℝ:= w i; let P':= taste U (S i); let A:= Z*M; let F':=P'*g i*Real.exp (v*k); let D:=barn o (S i); have hp(z: ↥L): f (it z)=F'*Q^z.val.card:=by unfold f; rw [if_pos (show j∈ _ from h0)]; unfold F'; change P'* (Q^z.val.card*g i) * Real.exp (v*k)= _; ring
          simp_rw [hp]; rw [← mul_sum,sum_coe_sort L (fun i=> Q^i.card)]; have hh1:L⊆ D.powerset.filter (fun i=>i.Nonempty):=fun i hi=> by obtain ⟨hh,h⟩:=mem_filter.mp hi; exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hh).trans inter_subset_right),h.1⟩
          have hn':(D.card:ℝ)≤ k*M:=by unfold k M hullP; rw [← mul_assoc]; exact_mod_cast (barncard o (S i) Ft U.B hf)
          have hKI:0 ≤ k:= Nat.cast_nonneg _; have hg0:0≤g i:=(h.fee i).travels; have h':0 ≤ P':=by unfold P' taste Plate.reFee; positivity
          apply le_trans (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hh1 (fun i _ _=> pow_nonneg hQ _)).trans (income Q hQ D)) (show 0≤F' by unfold F'; positivity))
          have hδ: D.card*Q ≤ ε*k :=by have heϑ:= mul_le_mul_of_nonneg_left (show M*Q≤ ε from hX) hKI; apply (mul_le_mul_of_nonneg_right hn' hQ).trans; linarith only [heϑ]
          let t:= (1+k)^(kingP U.order U.power); have hl:P'≤ Z*t:=taste_le _
          have hP:(D.card:ℝ)*Q≤ (1+k)*(M*Q):=(mul_le_mul_of_nonneg_right hn' hQ).trans ((le_of_eq (mul_assoc ..)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)))
          let x:=Real.exp (v*k+ε*k)
          have hK: Z*t*g i*Real.exp (v*k)*((1+k)*(M*Q)*Real.exp (ε*k)) ≤ C'*(g i*Real.exp ((v+2*ε)*k)):=by
                    let C₁:= Z *g i*(M*Q)*x; have he':0 ≤ C₁:=by unfold C₁ x; positivity
                    have hv' :(1+k)^(kingP U.order U.power+1) ≤ R * Real.exp (ε*k):=polynomial_cost he hKI _; refine le_trans (le_of_eq (b:=C₁*(1+k)^(kingP U.order U.power+1)) ?_) ((mul_le_mul_of_nonneg_left hv' he').trans_eq ?_); · unfold C₁ t x; rw [Real.exp_add,pow_succ]; ring
                    change Z*g i*(M*Q)*x*(R*Real.exp (ε*k))= Z*M*R*Q*(g i*Real.exp _); have he'':x*Real.exp (ε*k)= Real.exp ((v+2*ε)*k):=by unfold x; rw [← Real.exp_add]; congr 1; ring
                    rw [←he'']; ring
          change F' * _ ≤ _; apply le_trans _ hK; refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hg0) (Real.exp_pos _).le) (mul_le_mul hP (Real.exp_monotone hδ) (Real.exp_pos _).le (by positivity)) (by positivity) (by unfold t; positivity)
-- proof shell
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.pricing
