import YM.QCD.Globe.Wax
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Nola Brick Trees
variable (P:Plan 4) (i:Flavor N){R A C g t:ℝ}
include i
lemma rails (kT T:ℝ)(h:0 < kT)(hp:0<T): ∃ L₀ B:ℕ,∀ L:Side,L₀ ≤ L.val→∃ r z a:ℝ, 0<r ∧ r≤ kT ∧ 0 < z ∧ z ≤ T ∧ 0 < a ∧ ∀ v:ℝ,0<v→ v ≤ a →∀ᶠ t:ℝ in atTop,∃ W:ℝ,0 ≤ W∧ ∀ (S:Flight 4 4)(c f:Side)(h:f.val=c.val*S.L.val)(X:EvenA f N)(K:Sheet f), B≤ c.val → S.L=L → |mass K| ≤ z → Fused X K (2*(Real.exp 2*t)) r v → TrailS P P S h X K (2*(Real.exp 2*t)) r v T W :=by
    obtain ⟨δ,hδ,hδ',hx⟩:= choose₀
    obtain ⟨b,hb,hF⟩:= bounces P 6; obtain ⟨K,hK,H⟩:=intoA i 6
    obtain ⟨B,H'⟩:=candy P
    let R:= b; let A:ℝ:=(8*(4*b+2))⁻¹; have hA :0 < A:=by unfold A; positivity
    obtain ⟨D,hD⟩:= foldingP (k:=4) P A hA le_rfl le_rfl 6 (by decide)
    obtain ⟨C,hC,hP⟩:= anthem (k:=4) (j:=4) le_rfl le_rfl 6
    obtain ⟨L₀,hL⟩:= tackle hδ (show 0<C+1 by linarith) N
    refine ⟨max D L₀,B,fun L he=> ?_⟩
    have hD':D≤L.val:= le_trans (le_max_left ..) he; have hL':L₀≤L.val:= le_trans (le_max_right ..) he
    obtain ⟨W,hW,H₀⟩:= choiceH P 4 6 L
    let V:= W+1; have hV : 1≤V:=le_add_of_nonneg_left hW
    let u:= (C+1)*cape L 0; have hu:0<u:=by unfold u; have ht:=cape_pos L 0; positivity
    obtain ⟨r,hr1,hr⟩:= ((asks hu (zero_lt_one.trans_le hV) hp h A R hA hb).and self_mem_nhdsWithin).exists
    have hr:0<r:=hr; obtain ⟨h1,h2,h3,h4,h5,h6⟩:= hr1
    let z:=min (min r T) ((A*r)/(2^6*V^2)); have hz: 0<z:= lt_min (lt_min hr hp) (div_pos (mul_pos hA hr) (by positivity)); have hz0:z≤T:=le_trans (min_le_left ..) (min_le_right ..); have hz1:z≤r:= le_trans (min_le_left ..) (min_le_left ..)
    refine ⟨r,z,δ/2,hr,h6,hz,hz0,half_pos hδ,fun v hv he=>?_⟩
    let G:=spoolM δ v; let X:=coastW L δ v; let y:=riderW (C+1) L N; have hg:0<G:=by unfold G spoolM; positivity
    have hg' : G≤1:= (div_le_one hδ).2 (by linarith)
    have hz2:2^6*(V^2*z) ≤ A*r:=by have ht : z≤((A*r)/(2^6*V^2)):= min_le_right ..; rw [le_div_iff₀ (by positivity)] at ht; linarith only [ht]
    have hY := hL L hL' v hv
    have hX:0 ≤ X:=by unfold X coastW; have hx': 0≤ Real.exp δ-1:=sub_nonneg.mpr (Real.one_le_exp hδ.le); have hu:0≤ spoolM δ v:=hg.le; positivity
    let U:=2*V; let q:=whiskey N U X; have hh : 1≤ U:=by unfold U; linarith
    let J:ℝ:= Real.exp 4*((Fintype.card (Brick.Note N):ℝ)^2*(2*U)); obtain ⟨M,hM,H_M⟩:=heft (C:=J) (by unfold J; positivity) (show 0 < δ/2 by linarith); obtain ⟨d,hd,H_d⟩:=heft (C:=K*X) (by positivity) (show 0 < A*r by positivity)
    filter_upwards [eventually_ge_atTop d,eventually_ge_atTop M] with t ht ht'
    have he':0<t:=zero_lt_one.trans_le (hd.trans ht)
    have hqy:0 ≤ q:=by unfold q whiskey; positivity [Real.log_nonneg hh]
    refine ⟨q,hqy,fun S c f h X' K' hB hh' hk hv'=>?_⟩; obtain ⟨hA',hT',hR',hg0⟩:= H₀ S _ _ h hh'; have hT := hP S _ _ h [] (by simp); rw [List.length_nil,pow_zero, mul_one, show oldDiff (proton S h) []=_ from (show _=proton S h from rfl), hh'] at hT -- dependent simp
    refine feastQ (δ:=δ) (t:=z) (A:=2*r) (r:=r) (w:=V) (v:=y) (u:=G) (η:=4*A*r) (b:=2*u) S h P P i H (hA'.up (by unfold V; linarith)) (hT'.up (by unfold V;linarith)) (hR'.up (by unfold V; linarith)) (hD S c f h (hh'.symm ▸ hD')) (Cent.up hT (show _ ≤ u from mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (cape_pos ..).le)) (hF _ c) (H' _ c hB) hv' (by positivity) hz.le hr.le hg hg' hδ hδ' hx hk (by linarith) h1 (by positivity) he' ?_ ?_ hY.1 hA.le hV (by linarith) (by positivity) ?_ ?_ hX hY.2 ?_ h4 hb ?_ h5
    · have hq:G⁻¹*v=δ/2:=by unfold G spoolM; field_simp
      rw [hq]; have ht := H_M t ht'; change (t:ℝ)⁻¹^2*_ ≤ _ at ht; unfold J U at ht; linarith
    · change 0 ≤ riderW _ _ _; unfold riderW titanic stemF Jets.Sun.fingers; unfold u at hu; positivity
    · unfold y riderW titanic u; exact le_of_eq (by ring)
    · unfold X coastW; rw [hh']
    · have hl:=Real.one_le_exp (by norm_num : 0 ≤ (2:ℝ)); have ht'' : t≤2*(2*(Real.exp 2*t)):=by nlinarith
      have he:= H_d _ (ht.trans ht''); linarith only [h3,hz2,he]
    have he0:0<8*(4*b+2):=by positivity
    change 2* dimeZ b (4*((8*(4*b+2))⁻¹)*r)≤ _; exact le_of_eq (by unfold dimeZ; field_simp; ring)
end YM.QCD.Globe
