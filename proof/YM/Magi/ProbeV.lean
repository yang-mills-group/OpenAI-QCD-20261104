import YM.Magi.Glow
import YM.Magi.Vault
import YM.Next.SCHEDULE.Support
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open Function Lattice RG Pressure MeasureTheory Finset QCD Kites Kit Port Flume
open Grass Lat Play QCD.Bera
open Stitch Plate Loom Loom.Fleet Sway OrbitG Ribbon Rebus Creek Cove Apron Apron.Grove Cupola QCD.Acre QCD.Acre.Rails
open Anomaly
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N:ℕ}{I D Z U J R:Type} [Fintype I] {l φ k B P A A':ℕ} {v α s t:ℝ}
local notation "F0"=> (Keys c N)
open QCD.Brick QCD.Dust -- edit
-- payload color for actual evaluator. does not insert new face handshake.
namespace LampV
variable (L:Side)(N:ℕ){z t' d s Λ ξ κ' ε α' τ:ℝ}{n m l b k':ℕ}
open Bera QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby QCD.Acre.Stratum.MarchQ.Suburb
open Suburb.Melt.Lobby.LeaseV LeaseV.Advent Suburb.Affair.Nimbus
variable (Y:Advent.RouteV L n (refuge l+20) z) (p:I→Site c)(q:I→Bool) (T: Finset (Finset I)) (E: Reel c N I J)(S₇:Finset J)(P:BudgetPoint)(F:Film c N I D)
variable (Φ:Quince c N I)
variable (hM:Bearing p q T E S₇ L l m v τ Λ P d F)(hm:Moor p T E S₇ Φ P.B l k' m P.threshold s κ' ξ ε)
local notation "v1"=> freshS L 5 z
include hM Y
lemma grazingV (hp0:∀ i∈T,i.card ≤ l)(he : τ=MintV.riseV L z b) (hz:b≤ MintV.distV L n z)(hb:P.B= radiusB (run L τ))(hF:P.threshold=fiery su τ L)
    (i:J)(hp:i ∈ S₇)(hv:2*(refuge l*P.B+9+1)<c.val)(V:Grid c)(h:Healthy P.threshold (E.addr i).support V) :
    ∃ g: Site c→ su.El, ∃ B: Directions su c,
       E.mark i (gauge g V) = E.mark i (increment 1 B) ∧ Healthy P.threshold (cups p (innerT l * P.B) (E.z i)) (increment 1 B) ∧ ‖B‖≤ freshS L 5 z :=by
       obtain ⟨j,hj⟩:= hM.boost.book.stays i
       let t:=refuge l; let B0:=t*P.B+9; have ha:=P.B_pos
       have hi: ∃ g: Site c→su.El,∃ B:Directions su c, ‖B‖≤ freshS L 5 z ∧ Next.Fluctuations.AgreeNear id (p j) B0 (gauge g V) (increment 1 B):=by
            have hv₁:=hM.rise.shield _ hp j hj; have hc:B0 ≤ (refuge l+20)*P.B:=by unfold B0 t; nlinarith
            rw [hb,he] at hc; apply Y.act b hz _ _ _ _ _ hc _ hv₁ hv; rw [←he, ← hF]; exact h
       let W:=halo B0 {p j}
       obtain ⟨g,B,hH,hA⟩:=hi; let R:= increment (1:Grid c) B; have hr :Agrees (↑W : Set _) (gauge g V) R:=by intro i hi _; obtain ⟨k,hk,h⟩:=halo_spec.mp hi; rw [mem_singleton.mp hk] at h; exact hA _ h
       let u:= innerT l * P.B; let Q:= cups p u (E.z i)
       have hmk : u ≤ t*P.B:=by unfold u t refuge; nlinarith -- product
       have hl:= hM.rise.arcs _ hp
       have hx : Q⊆ halo (t*P.B) {p j}:=by
           rw [show Q=_ from cups_eq ..]; refine biUnion_subset.mpr ?_; intro j' he'
           have hG := Play.Camp.ridgeSpan p (E.z i) (baseTZ P.B) hl.2 j j' hj he'
           refine subray (l*(110*P.B)) _ _ _ _ (?_) (?_)
           · refine hG.trans ?_; unfold baseTZ; have he:=hp0 _ hl.1; nlinarith
           unfold u t refuge innerT; nlinarith
       have hH0 : Healthy P.threshold Q (gauge g V):= (by rw [Healthy,gauge_flags]; exact Disjoint.mono_left (hx.trans (Subset.trans (Corona.halo_mono (by unfold t; omega : t*P.B ≤ refuge l*P.B+10) (Finset.Subset.refl _)) (hM.rise.shield _ hp _ hj))) h)
       have hT : Q∩flags P.threshold R=∅:=by
           have h0:inspected Q ⊆ W:=by
               apply Subset.trans (Next.Scheduling.flag_layer _) ?_; intro i hp; obtain ⟨k,hM,h'⟩:=halo_spec.mp hp; obtain ⟨y,hy,h''⟩:=halo_spec.mp (hx hM); exact halo_spec.mpr ⟨y,hy,(separation_triangle ..|>.trans ((Nat.add_le_add h'' h').trans (show _ ≤ B0 from by omega)))⟩
           rw [← RG.flags_agree P.threshold _ R Q (agrees_mono hr h0)]; exact disjoint_iff_inter_eq_empty.mp hH0
       refine ⟨g,B,hM.rise.domain _ hp j hj _ _ (?_),disjoint_iff_inter_eq_empty.mpr hT,hH⟩ -- hM collision
       apply agrees_mono hr; exact Finset.coe_subset.mpr (Corona.halo_mono (hmk.trans (by omega)) (Finset.Subset.refl _))
local notation "z₁"=> v1
include hm
-- pointwise CREDIT across WALL.E.Pay.U can issue Ball stroke reading amplitude bound.L.M reflection after Ledger.P & Query. Theta r.O.P same. Λ Pel.Health. Credits τ not sharpen δ after radius? paid weights.
lemma lucidityV (hp0:∀ i∈T,i.card ≤ l)(he:τ=MintV.riseV L z b)(hz:b≤ MintV.distV L n z)(hb:P.B= radiusB (run L τ))(hF:P.threshold=fiery su τ L)(hd:1 ≤ v)(hC:2*(refuge l*P.B+9+1)<c.val)
    (hw:freshS L 5 z ≤ s)(i:J)(hp:i∈ S₇)(hf:0≤α')(hε:0≤ε) (hR:∀ B:Directions su c, ‖B‖≤ freshS L 5 z→ Healthy P.threshold (cups p (innerT l*P.B) (E.z i)) (increment 1 B) → ‖Oce.rose (Dh c N I) (karm κ' (increment 1 B)) (Φ (E.z i))‖≤ α') (U:Grid c):
     let t0:=(E.z i).card*m; Tablet.credits v ((Reel.mist E P.threshold i) U)≤v^t0*(fuelColor N^t0*(α'+ε)):=by
        intro t0; unfold Reel.mist; have he0:0≤fuelColor N:=zero_le_one.trans (le_max_left ..); have hv:0 ≤v:= zero_le_one.trans hd
        by_cases h:Healthy P.threshold (E.addr i).support U; swap
        · rw [masked_ne _ _ _ _ h]; have hU(v):Tablet.credits v (0: Patio (Keys c N⊕Ribbon.Spine I))=0:=by unfold Tablet.credits Creek.load wscale; change ‖changeVars _ (0:Alg _)‖=0; rw [map_zero,norm_zero]
          change Tablet.credits v (0: Patio (Keys c N⊕Ribbon.Spine I))≤ _; rw [hU]; positivity
        rw [masked_eq _ _ _ _ h]
        obtain ⟨g,B,hg,hK,hB⟩:= grazingV L N Y p q T E S₇ P F hM hp0 he hz hb hF i hp hC U h
        let V:=E.mark i (gauge g U); let d:=E.z i; let W:= increment 1 B
        have heQ:= (hM.rise.arcs _ hp).1
        have hf:= hm.mirrors d heQ (hM.boost.book.stays i) B (hB.trans hw) hK
        have ht: sled E S₇ d W=V:=by
             unfold sled; rw [sum_eq_single i]; exact hg.symm
             · intro j hj h; obtain ⟨he,hj⟩:=mem_filter.mp hj; exact (h (hM.rise.mug he hp hj)).elim
             intro ha; exact (ha (mem_filter.mpr ⟨hp,rfl⟩)).elim
        have hz' : ‖V‖≤ α'+ε:=by
                   let X:=Oce.rose (Dh c N I) (karm κ' W) (Φ d); have hh:‖V-X‖≤ε:= ht ▸ hf -- fix
                   exact (norm_le_norm_sub_add ..).trans ((add_le_add hh (hR B hB hK)).trans_eq (add_comm ..))
        refine (warmP N t0 _ (hM.rise.degree _ hp U) hd).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hv _))
        calc ‖E.mark i U‖ = ‖parcelColor N g I V‖:= congr_arg _ (hM.boost.book.tint i U g).symm
             _≤ _ := (stamped N t0 g V (hM.rise.degree _ hp _)).trans (mul_le_mul_of_nonneg_left hz' (pow_nonneg he0 _))
end LampV
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.LampV.grazingV
#print axioms YM.MassiveQCD.Cape.LampV.lucidityV
