import YM.Massive.Brush.Comet
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
namespace Brave
open Finset NormedSpace Loft Globe.HalfMass QCD.Globe QCD.Revolve
open MeasureTheory
open scoped Kronecker
variable (a b:Flavor F)(X:Spike)
local notation "d"=> (Fintype.card Lat.Fiber:ℝ)
local notation "S"=> (Fintype.card (Site c):ℝ)
local notation "g"=> Lat.g5
local notation "p"=> Run.plane
local notation "Y"=> flavorW g5 a b c
local notation "cell"=> QCD.Run.cell
-- generic structure for relative certificate of both polarization estimates.Holds on one run endpoint as supplied.
variable (i j:ℕ)
open Cove Stew Reggae QCD.Run Acre QCD.Acre.Rails QCD.Flume QCD.Finch High.PrismT
local notation "Ω"=> Modes c F
local notation "Z"=> Fintype.card (Site c)
structure LocalPrice (P:Density c F) (u v:ℝ):Prop where
  source : ∃ (W:EvenA c F)(z:ℂ)(t:Flavor F→ Sheet c), P 1 = z • exp W.val ∧ z≠0 ∧ coef ∅ W.val=0 ∧
    Stew.panel 2 W.val=form (Matrix.blockDiagonal t) ∧ (∀ i, t i= (Stiffness.body P 1)⁻¹ • (piece i i (traceP (P 1))))∧‖panel 4 W.val‖ ≤ ↑(Fintype.card (Site c))*u ∧ ∀ i, Tempo (t i) ∧ Beam (t i) 6 v

-- triple with same flavors. diagonal blockD exactly. Allows projecting each ledger charge before volume factors.
lemma triple (t:Flavor F→ Sheet c)(X:Spike) : let D:= Matrix.blockDiagonal t
    piece a b (D*flavorW X a b c*D)= t a*onSpin c X*t b:=by
   intro D; let u:Sheet c:=t a; let v:= t b; have ht(j:Flavor F): piece j j D=t j:=by ext k i; simp [piece,D]
   ext i j; rw [piece, Matrix.of_apply, Matrix.mul_apply,Fintype.sum_prod_type]; have he(k:Lat.Row c): ∑ j':Flavor F,(D*flavorW X a b c) (i,a) (k,j') * D (k,j') (j,b)= (piece a a D*onSpin c X) i k * t b k j:=by
         rw [← cutsRight X a b D]; unfold D; simp [piece,Matrix.blockDiagonal_apply]; -- sums,D blockDiag times W.Maybe simp too aggressive
   rw [Matrix.mul_apply]; exact sum_congr rfl fun i hi=> (he _).trans (by rw [ht])
lemma triple_empty (t:Flavor F→ Sheet c)(X:Spike)(he:a≠b): let D:= Matrix.blockDiagonal t; (flavorW X a b c * D).trace=0:=by
   intro D; unfold Matrix.trace; apply sum_eq_zero; rintro ⟨i,w⟩ _ ; unfold Matrix.diag; rw [Matrix.mul_apply, Fintype.sum_prod_type]; unfold D flavorW; apply sum_eq_zero; intro z _; simp [Matrix.blockDiagonal_apply,spot,show ¬(w=a ∧ w=b) from fun h=> he (h.1.symm.trans h.2)] -- orientation
lemma pack_add (A B:Sour Ω) : piece a b (A+B)=piece a b A+piece a b B:=rfl
lemma pack_scale (w:ℂ)(A:Sour Ω): piece a b (w • A)=w • piece a b A:=rfl
lemma panel_body (x:Dirac A) (h:coef ∅ x=0): x ∈ Loft.floor (Pairs A) 1:=test.mpr fun s hv=>by rw [card_eq_zero.mp (show s.card=0 from by omega)]; exact h
noncomputable def quartic (X:Spike):ℝ:= spinPrice X^2 * (4:ℕ).factorial
lemma quartic_pos :0 ≤ quartic X:=by unfold quartic; positivity
-- norm of unnormalized relative diagnostic independent of scalar z ≠0. Sharp outputs in Rig have $s prudence.
set_option maxHeartbeats 450000 in
lemma beamAt (X:Spike) (x:EvenA c F)(t:Flavor F→ Sheet c)(w K:ℝ)(z:ℂ)(hz:z ≠0) (he:a≠b) (hC:coef ∅ x.val=0)(hM: Stew.panel 2 x.val=form (Matrix.blockDiagonal t))
    (hp:Tempo (t a)) (ht: ∀ i j:Site c,‖stalk (t a) i‖ ≤ K ∧ ‖stalk (t b) j‖ ≤ K)(hv: ‖panel 4 x.val‖ ≤ (Z:ℝ)*w) : let E:= z • exp x.val; let V:=flavorW X a b c
      ‖horn X a b (coef ∅ E) (lap V E)‖ ≤ productTariff X*K^2+quartic X*w:=by
    intro E V; let D:= Matrix.blockDiagonal t; let W:=x.val-form D; let S' := traceP (lap V W); let T:= traceP (lap V (gauss D)); let τ:= artPrice X (c:=c); 
    have hZ: coef ∅ E=z:=by unfold E; rw [map_smul, body_exp (panel_body _ hC),smul_eq_mul,mul_one];
    have hs: 0 ≤ K:=(norm_nonneg _).trans (ht 0 0).1; have h₁: (1:ℝ)≤Z:=by exact_mod_cast Fintype.card_pos (α:=Site c)
    have he':(Z:ℝ) * d ≠0:=by positivity
    have hF: traceP (lap V E)=z • (T+ S'):=by unfold E; rw [map_smul, basic, quarter D _ (ray_body _ x.val hC x.property hM) V]
    have hh: horn X a b (coef ∅ E) (lap V E)= artPrice X (piece a b (T+ S')) :=by rw [art_horn,hF,pack_scale,hZ,art_mul,inv_smul_smul₀ hz]
    rw [hh,pack_add,art_sub]; apply (norm_add_le ..).trans; apply add_le_add
    · rw [show T=D*V*D from gaussian V D (triple_empty a b t X he),triple a b t X]; exact summer X _ _ hp K hs (fun i=> (ht i 0).1) (fun i=>(ht 0 i).2)
    have hW₀: ‖panel 4 W‖ ≤ (Z:ℝ)*w:=by unfold W; rw [map_sub,Stew.past (n:=2) _ (form_two _),if_neg (by decide: (4:ℕ)≠2),sub_zero]; exact hv
    have hW:=(summit X a b S');
    have hX:=spinPrice_nn X
    have hV:= account V W (spinPrice X) hX (sizeL X a b)
    apply le_of_mul_le_mul_left _ (show 0<(Z:ℝ)*d from by positivity)
    unfold quartic; apply (hW.trans (mul_le_mul_of_nonneg_left hV hX)).trans; have h:‖panel 4 W‖ ≤ (Z:ℝ)*d*w:=by
        have hd:(1:ℝ)≤d:=by exact_mod_cast Fintype.card_pos (α:=Lat.Fiber)
        have hw:0≤w:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hv) (show 0<(Z:ℝ) from by positivity); exact hW₀.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hd) hw)
    nlinarith only [mul_le_mul_of_nonneg_left h (show 0 ≤ spinPrice X^2*(4:ℕ).factorial from quartic_pos X)]
end Brave
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Brave.beamAt
