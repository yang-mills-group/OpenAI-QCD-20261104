import YM.Roan.Sura
import YM.Roan.Priory
import YM.Roan.Nol
import YM.Roan.Rule
import YM.Clink.Brass
import YM.Kwick.Vale
import YM.Roan.Ode
import YM.Lapin.Spark
/-! End read at reference upper Hop boot.Several charts transfer.X near arbitrary.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Pane Tawny.BendR
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
/- Need Shelf.Guru.Bind at references. Keep full Tally + price lower.S
-/
variable {S:Scheme}{R:Side} (A:Run S N R 6) (q:ℕ)(T:TaperHol)
variable (W:Axis→ℕ→ℝ)(v w:ℕ→ℝ)(B:ℕ→BudgetPoint)(d ℓ:ℕ)
variable (u α a κt K b δ H:ℝ)(P:Axis → Cover → Insertion (S.side R q) 6)(f:ℕ→RawVec 10)
variable (a₂ C' D θ e x b' ξ' g t₀ L E E' H':ℝ)
open QCD.Entr.Goals Next.Free QCD.Flume
variable (nZ:ℕ)(t:ℝ)(G:QCD.Flume.Plan nZ)(U:Train nZ)
open QCD.Entr.Goals Next.Free Seals
local notation "Z"=> RawVec 10
variable (hP:Pueblo u a α δ L a₂ E C' D θ e x b' ξ' g t₀ q)
variable (hV: Twist q B v w L u θ) -- order Pt...
-- payload not before projection. B target ≤ funds.Beat.C "E" watch shadow.AK.
variable (hD:4*a*u≤1/2)(hL:3≤ L)(hl:L*u^2=1) (hv:∀ i,0 < v i)(hS:(B 0).threshold≤t₀)(hS': (B q).threshold≤ t₀)(hK:0≤K)
local notation "Fℓ"=>Flavor 6
local notation "s"=> S.side R q
local notation "Sx0"=> S.side R 0
local notation "tN"=> (B q).threshold
local notation "Bφ"=> (v q)^2
local notation "Bq"=> (B q).threshold*(v q)^2
local notation "Aκ" p:arg f:arg m:arg=> Regiment A q T m v w B d ℓ u α a K b δ H p f
local notation "Bκ" p:arg f:arg m:arg=> Regiment A q T m v w B d ℓ u α a K E' δ H' p f
variable (Pz Zz Vz Kz:Flavor 6 → ℕ→Z)
variable (hA:A.Actual)(hk:q ≤ N)(hq:0<q)
local notation "Sℓ" y:arg=> corm (i:=q) A nZ G U t y
local notation "F0" y:arg=> marque (i:=q) A false y
local notation "F1" y:arg=> marque (i:=q) A true y
local notation "Z0" y:arg=> sprigs (i:=q) A y
-- helper between currency holds.Em Stage.
local notation "g_"=>Gpick
local notation "Qp" i:arg V:arg => Canvas.foil (A.density i) (report A (V (0:Axis)) (shelV 0) i 0)
local notation "Ψ" p:arg G:arg=>Tally T 0 p (A.density 0) (report A G (shelV 0) 0 0)
local notation "pa"=> (B 0).order
local notation "pn"=> (B q).order
variable (he:b ≤ E*(v q)^2)(hz:E'≤ E*((B q).threshold*(v q)^2))
local notation "M₁" S_:arg=> ((cashR (L^4) S_ q 0)⁻¹ * (E+ (2*((L^4)*a+1))*a₂))
local notation "K₁" S_:arg=> (K*(M₁ S_)/(v 0)^2)
variable (F F':Axis → Cover → Insertion (S.side R q) 6)(p':ℕ→Z)
variable (hC0:10 ≤ (B 0).order)(hc:10 ≤(B q).order)(hDu:2 ≤ d)(hDu':2 < ℓ)
variable (Sμ Hγ:ℝ)
open Plans.Stamp
variable (ν0 ν1 ν2 ν3:Flavor 6 → Axis → ℕ → ℝ)
variable (X₁ X₂:ℝ)(hX:WealthR T (B q) X₁ X₂)
variable (hΩ:ProofK A q T v w B d ℓ u α a K b δ H E' H' nZ t G U Pz Zz Vz Kz ν0 ν1 ν2 ν3)
local notation "C★" v:arg=> (S.side R q)
local notation "Qz" x:arg=> rayC (A.density q) x
variable (C₁ εA :Flavor 6 → ℝ)
local notation "ep" i:arg=> C₁ i/((S.side R q).val:ℝ)+εA i
local notation "Nκ"=> H/Bφ
local notation "EH"=> H'/Bφ
local notation "BT" i:arg=> cashR (L^4) Bφ q i
local notation "Q₁"=> compass (BT 0) (v 0)
local notation "vδ"=> torque (BT 0) (v 0)
local notation "Q₂"=> point (B 0).threshold (BT 0) (v 0)
local notation "Qκ" i:arg=> point (B i).threshold (cashR (L^5) Bq q i) (v i)
local notation "Tt" i:arg=> compass (cashR (L^5) Bq q i) (v i)
local notation "Dδ"=> D*(C'*a₂)
local notation "Δe"=> D*(C'*e)
-- record outputs bound all at 0. transfer residual exact in limit by mult. Candidate supplies.ALL
variable (Y' Yz:ℝ)(hΦ: WealthR T (B 0) Y' Yz)
local notation "qΨ"=> Pz
local notation "pv" p:arg i:arg=> p i 0
local notation "ef" X:arg=> fun i:Flavor 6=> X i 0
local notation "V★"=> 2*t₀*Dδ + Δe + 3*e + 2*(6*(2*Dδ)*g)
local notation "TA"=> K₁ Bφ
local notation "TB"=> K₁ Bq
open Plans.Stamp
variable (N₀:ℕ→ℕ)(Rn:ℕ→Side)(Cq:∀ i, Run S (N₀ i) (Rn i) 6)
local notation "W✫"=> Flavor 6→ RawVec 10
local notation "Pc"=> point
variable (QK:Tarn.Choir)(Kn:ℝ)(g₀:ℕ→ℕ)
variable (SE:ℝ)
local notation "κR4"=> cashR (L^4) Bφ q 0
local notation "κR5"=> cashR (L^5) Bq q 0
variable (ht:Tendsto (fun i=>((S.side (Rn i) 0).val:ℝ)) atTop atTop)(hTg:Tendsto g₀ atTop atTop)
local notation "P0"=>Flavor 6
abbrev MintStem := (Flavor 6 → ↥(RawVec 10)) × (Flavor 6 → ↥(RawVec 10)) ×(Flavor 6 → ↥(RawVec 10)) × (Flavor 6 → ↥(RawVec 10)) × (Flavor 6 → Flavor 6→ℂ)× (Flavor 6 → Flavor 6 →ℂ) -- tuple.Product. measure
variable (p:ℕ→MintStem)(J1 J2:ℝ)
abbrev Ruler (p:MintStem)(i:ℕ) : Prop := MonthZ (Cq i) q T v B a K a₂ C' D e g t₀ L E Yz J1 J2 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2
#print Ruler
local notation "Ro" i:arg => Ruler q T v B a K a₂ C' D e g t₀ L E Yz N₀ Rn Cq J1 J2 (p i) i
lemma locate (i:ℕ)(p:MintStem)(h:Ruler q T v B a K a₂ C' D e g t₀ L E Yz N₀ Rn Cq J1 J2 p i) : ‖p‖≤ max (max J1 J2) 1:=by
        rcases p with ⟨a₁,k₂,a₃,a₄,f,z⟩; unfold Ruler at h; dsimp only at h; have hh:=h.rest; let m:= max (max J1 J2) 1; have h1:J1 ≤ m:= le_trans (le_max_left ..) (le_max_left ..); have h2:J2 ≤ m:= le_trans (le_max_right ..) (le_max_left ..); have ht:1 ≤ m:=le_max_right ..; have hT:0≤ m:=zero_le_one.trans ht; let C:=q
        have he: ∀ i:Flavor 6,‖(f i,z i)‖ ≤1:=fun i=>(h.kinetics i).2.2.1
        apply max_le; exact (pi_norm_le_iff_of_nonneg hT).mpr fun i=> ((h.rest i).1).trans h1
        apply max_le; exact (pi_norm_le_iff_of_nonneg hT).mpr fun i=>(hh i).2.1.trans h1
        apply max_le; exact (pi_norm_le_iff_of_nonneg hT).mpr fun i=>(hh i).2.2.1.trans h1
        apply max_le; exact (pi_norm_le_iff_of_nonneg hT).mpr fun i=>(hh i).2.2.2.trans h2
        apply max_le <;> apply (pi_norm_le_iff_of_nonneg hT).mpr <;> intro i
        · exact le_trans (le_max_left ..) ((he i).trans ht)
        exact le_trans (le_max_right ..) ((he i).trans ht)
-- strict extraction proof tuple.P
variable (z:MintStem)(ξ:ℕ→ℕ)(htξ:StrictMono ξ)(hz': Tendsto (p ∘ g₀ ∘ ξ) atTop (𝓝 z)) -- scope.
variable (hB:Blurs (S:=S) q T v B L N₀ Rn Cq QK g₀ SE)(hE: D*(v 0)^2* SE ≤ ξ')
include hB hE -- shadow hpZ.Needs hP not
open Tarn Tarn.Choir Onyx
include hz' hTg ht hP htξ hL hv hS
set_option maxHeartbeats 1620000 in
lemma ranksX (hh:∀ᶠ i in atTop, Ro i): Onyx.Worth QK :=by
        let f:=g₀∘ξ; have hf:=hTg.comp htξ.tendsto_atTop; obtain ⟨p1,p2,p3,p4,f₁,f₂⟩:=z; let U₁:=Q₁; let U₂:=Q₂; let W₁:= Tt 0; let W₂:= Qκ 0; let V:=p ∘ f
        let m(i):=S.side (Rn i) 0
        let q0(i):=V i|>.1; let q1(i):=V i|>.2.1; let q2(i):=(V i).2.2.1; let q3(i):=(V i).2.2.2.1; let xκ(i):=(V i).2.2.2.2.1; let y(i):=(V i).2.2.2.2.2 -- xκ shadow!
        have hε':0 < L:=lt_of_lt_of_le (by norm_num) hL; have hL0:0 < κR4:=(cash_κ (L^4) Bφ (by positivity) (pow_pos (hv _) _) q).1 0; have hT0:0<κR5:= (cash_κ (L^5) Bq (by positivity) (mul_pos (B q).threshold_pos (sq_pos_of_pos (hv _))) q).1 0
        have hx(i:Flavor 6):let X1:=p1 i; let X2:=p2 i; let X := p2 i + knotW p1 (f₁ i); ‖U₁ X1-Pi.single i 1‖ ≤ Δe+e ∧ ‖U₂ X1‖≤2*Dδ∧ W₁ X=0∧ ‖W₂ X-Pi.single i 1‖ ≤ V★ ∧ ‖f₁ i‖ ≤1∧∃ (a b c:Z), a∈ (bits QK).ker∧b∈ (bits QK).ker∧ c∈(bits QK).ker∧ ‖(κR4:ℂ) • X1-a‖ ≤SE∧ ‖(κR5:ℂ) • X1-b‖ ≤SE ∧ ‖(κR5:ℂ) • X2-c‖ ≤SE:=by
            dsimp only
            have hu:=hf.eventually hh; have hq(k:Flavor 6): Tendsto (fun j=> q0 j k) atTop (𝓝 (p1 k)):= ((tendsto_pi_nhds.mp hz'.fst_nhds k)); have h₁(k:Flavor 6): Tendsto (fun j=> q1 j k) atTop (𝓝 (p2 k)):= tendsto_pi_nhds.mp hz'.snd_nhds.fst_nhds k; have h₂(k:Flavor 6): Tendsto (fun j=> q2 j k) atTop (𝓝 (p3 k)):= tendsto_pi_nhds.mp hz'.snd_nhds.snd_nhds.fst_nhds k
            have h₃(i:Flavor 6): Tendsto (fun j=> q3 j i) atTop (𝓝 (p4 i)):= tendsto_pi_nhds.mp hz'.snd_nhds.snd_nhds.snd_nhds.fst_nhds i
            have hxV:Tendsto (fun j=>xκ j i) atTop (𝓝 (f₁ i)):= tendsto_pi_nhds.mp hz'.snd_nhds.snd_nhds.snd_nhds.snd_nhds.fst_nhds i; have hyV:Tendsto (fun j=>y j i) atTop (𝓝 (f₂ i)):= tendsto_pi_nhds.mp hz'.snd_nhds.snd_nhds.snd_nhds.snd_nhds.snd_nhds i
            have hℓ(C:Z→ₗ[ℂ] (Flavor 6→ℂ)) {g:ℕ→Z}{r:Z}(h:Tendsto g atTop (𝓝 r)): Tendsto (fun j=>C (g j)) atTop (𝓝 (C r)):= (C.toContinuousLinearMap.continuous.tendsto _).comp h
            let qQ(j:ℕ):= q3 j i +doubleW (q0 j) (q2 j) (xκ j i, y j i); let KzX:=p4 i+doubleW p1 p3 (f₁ i,f₂ i); have hhK:Tendsto qQ atTop (𝓝 KzX):=by
                  have hK:Tendsto (fun j=> knotW (q0 j) (xκ j i)) atTop (𝓝 (knotW p1 (f₁ i))):= tendsto_finsetSum _ fun k _=> (tendsto_pi_nhds.mp hxV k).smul (hq k)
                  exact (h₃ i).add (hK.add (show Tendsto (fun j=> knotW (q2 j) (y j i)) atTop (𝓝 (knotW p3 (f₂ i))) from tendsto_finsetSum _ fun k _=> (tendsto_pi_nhds.mp hyV k).smul (h₂ k)))
            have hW₁: W₁ KzX=0:= tendsto_nhds_unique (hℓ W₁ hhK) (tendsto_const_nhds.congr' (hu.mono fun j hi=> (MonthZ.kinetics hi i).2.2.2.1.symm)) -- h_t implicit Ruler h defined; hi type def not an abbrev. projection unknown.Need unfold
            have hW₂: ‖W₂ KzX-Pi.single i 1‖≤ V★:= le_of_tendsto (((hℓ W₂ hhK).sub_const (Pi.single i 1)).norm) (hu.mono fun j hi=> (MonthZ.kinetics hi i).2.2.2.2)
            have hM0(k:Flavor 6): prismA (p4 k)=prismA (p2 k)∧ prismB (p4 k)=prismB (p2 k)∧ prismA (p3 k)=0 ∧ prismB (p3 k)=0:=by
                have hf':=ht.comp hf -- tends f∘ with Nat finite
                -- norm inequalities
                have h:Tendsto (fun j=> taxP (m (f j)) TB+ taxP (m (f j)) TA) atTop (𝓝 0):=by simpa only [zero_add] using ((dimA (fun i=>m (f i)) hf' TB).add (dimA _ hf' TA)); -- let KzX shadow parameter `TB` references.
                have hV:Tendsto (fun j=>billR Yz (m (f j)) TB+billR Yz (m (f j)) TA) atTop (𝓝 0):=by simpa only [zero_add] using ((dimB (fun i=>m (f i)) hf' TB Yz).add (dimB _ hf' TA Yz))
                have hm0 : ‖prismA (p4 k)-prismA (p2 k)‖ ≤ 0:= le_of_tendsto_of_tendsto (((hℓ _ (h₃ k)).sub (hℓ _ (h₁ k))).norm) h (hu.mono fun q h=> (MonthZ.conduce h k).1)
                have hm1 : ‖prismB (p4 k)-prismB (p2 k)‖ ≤ 0:= le_of_tendsto_of_tendsto (((hℓ _ (h₃ k)).sub (hℓ _ (h₁ k))).norm) hV (hu.mono fun q h=> (MonthZ.conduce h k).2.1)
                have hz₁: ‖prismA (p3 k)‖≤0:= le_of_tendsto_of_tendsto ((hℓ _ (h₂ k)).norm) (dimA (fun i=>m (f i)) hf' TA) (hu.mono fun q h=>(MonthZ.conduce h k).2.2.1)
                have hz₂: ‖prismB (p3 k)‖≤0:= le_of_tendsto_of_tendsto ((hℓ _ (h₂ k)).norm) (dimB (fun i=>m (f i)) hf' TA Yz) (hu.mono fun q h=>(MonthZ.conduce h k).2.2.2)
                exact ⟨sub_eq_zero.mp (norm_le_zero_iff.mp hm0),sub_eq_zero.mp (norm_le_zero_iff.mp hm1), norm_le_zero_iff.mp hz₁,norm_le_zero_iff.mp hz₂⟩
            let X:=p2 i+knotW p1 (f₁ i); have hPhi(F:Z→ₗ[ℂ] (Flavor 6→ℂ)) (hp:F (p4 i)=F (p2 i))(hz:∀ i,F (p3 i)=0) : F KzX=F X:=by unfold KzX X; rw [map_add,map_add F (p2 i),hp]; change _+ F (knotW _ _+ knotW _ _)=_; simp [map_add,knotW,hz]
            have he: W₁ KzX=W₁ X:=congr_arg (fun Y:Flavor 6→ℂ => (↑(κR5*(v 0)^2:ℝ):ℂ) • Y) (hPhi prismA (hM0 i).1 fun i=>(hM0 i).2.2.1); have he':W₂ KzX=W₂ X:=congr_arg (fun Y:Flavor 6→ℂ => (↑((B 0).threshold*(κR5*(v 0)^2):ℝ):ℂ) • Y) (hPhi prismB (hM0 i).2.1 fun i=>(hM0 i).2.2.2)
            let S₁(j:ℕ):=(p j).1 i; let S₂(j:ℕ):=(p j).2.1 i
            have hBq:∀ᶠ j:ℕ in atTop,∀ a:Axis,Tally T 0 ((S₁ j).val a) ((Cq j).density 0) (report (Cq j) (marque (i:=q) (Cq j) false i a) (shelV a) 0 0):=hh.mono fun k hk=>MonthZ.lowerP hk i
            obtain ⟨X0,h0,hD0⟩:= hB κR4 hL0.le (scalesGE q v B L hv hL) i false S₁ ξ htξ hBq (p1 i) (hq i); obtain ⟨Y0,h1,hD1⟩:= hB κR5 hT0.le le_rfl i false S₁ ξ htξ hBq (p1 i) (hq i); obtain ⟨Xt,h2,hD2⟩:= hB κR5 hT0.le le_rfl i true S₂ ξ htξ (hh.mono fun k hk=>MonthZ.sober hk i) (p2 i) (h₁ i)
            rw [he] at hW₁; rw[he'] at hW₂; refine ⟨le_of_tendsto (((hℓ U₁ (hq i)).sub_const _).norm) (hu.mono fun q h=>(MonthZ.kinetics h i).1),le_of_tendsto ((hℓ U₂ (hq i)).norm) (hu.mono fun q h=>(MonthZ.kinetics h i).2.1),hW₁,hW₂, le_of_tendsto hxV.norm (hu.mono fun q h=> le_trans (le_max_left ..) ((MonthZ.kinetics h i).2.2.1)), X0,Y0,Xt,h0,h1,h2,hD0,hD1,hD2⟩
        -- combine
        refine ranks_p QK (v 0) ((B 0).threshold) (Stair.progress u a α δ L a₂ E C' D θ e x b' ξ' g t₀ q B v hP hv hL (bits QK) p1 p2 f₁ SE (le_trans (B 0).threshold_pos.le hS) (fun i=>(hx i).1) (fun i=> (hx i).2.1) (fun i=> (hx i).2.2.1) (fun i=> (hx i).2.2.2.2.1) (fun i=> (hx i).2.2.2.1) hE (fun i=>?_) (fun i=>?_) (fun i=>?_))
        · obtain ⟨x,y,p,h,_,_,hz,_⟩:= (hx i).2.2.2.2.2; exact ⟨x,h,hz⟩ -- hu hudentials rest
        · obtain ⟨x,y,p,_,h,_,_,hz,hV⟩:= (hx i).2.2.2.2.2; exact ⟨y,h,hz⟩
        obtain ⟨x,y,p,_,_,h,_,_,hz⟩:=(hx i).2.2.2.2.2; exact ⟨p,h,hz⟩
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.ranksX
