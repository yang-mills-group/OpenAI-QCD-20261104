import YM.Fir.Bells
/-! Rank and genuine spacetime productions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Sash
variable (s:Sash G φ)
variable {Z:SpaceZ}(H:Ability P φ Z)
-- genuine all-slot Detection in each rank space
variable (d:ℕ)
noncomputable abbrev sea (G:∀ d,Cottage P d) (d:ℕ):Points 2:= points ![0,(G d).K.coast]
noncomputable abbrev duetS (Z:SpaceZ) (d:ℕ)(x:Points 2)(p q:Label d):ℂ:= Z 2 (fun _=>d) x ![p,q]
lemma stage (G:∀ d,Cottage P d)(d:ℕ):sea G d∈ conf 2:=by
     let K:=(G d).K; have hz:K.coast ≠ 0:= fun h=> by apply K.reach; exact h ▸ (Metric.mem_closedBall_self K.breadth.le)
     intro i j h; change (![_ ,_] i:E4)= ![_,_] j at h -- maybe
     by_contra ht; fin_cases i <;> fin_cases j <;> first | contradiction | exact hz h | exact hz h.symm
noncomputable abbrev prism (Z:SpaceZ) (z:CellF d): CellF d:= fun j=> duetS Z d (sea G d) (s.L d j) (s.R d z)
-- exact bounds
include hp H hφ
set_option maxHeartbeats 490000 in
lemma sparkle (z:CellF d): ‖z‖ ≤ (G d).J.J*‖prism s d Z z‖ :=by
     let S:=sea G d; let K:= (G d).K; let c:=C.S; let Y(i:ℕ):=bead (C.S.spacing (C.N i)) K.coast; let X(i:ℕ): CellF d:= K.heightH i (Y i) (stem P d i (K.ridge i z))
     have ht:Tendsto (fun i=> X (φ i)) atTop (𝓝 (prism s d Z z)):=by
        apply tendsto_pi_nhds.mpr; intro i; let W(j):=(![K.g (φ j) i, (K.ridge (φ j)) z]); let V:=( ![s.L d i,s.R d z]); have hs:Tendsto W atTop (𝓝 V):=by
             apply tendsto_pi_nhds.mpr; intro j; fin_cases j; exact tendsto_pi_nhds.mp (s.prices d) i; exact voiceL (s.pearls d) tendsto_const_nhds
        let F(j:ℕ):Fin 2 → Cover:=![0,Y (φ j)]; have hf:Tendsto (fun j=> pollF C 2 (φ j) (F j)) atTop (𝓝 S):=by
            -- unwrap PiLp
            let Z:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2=> E4)
            have hU:Tendsto (fun j=> Z (pollF C 2 (φ j) (F j))) atTop (𝓝 (Z S)) :=by
                 apply tendsto_pi_nhds.mpr; intro k; fin_cases k
                 · change Tendsto (fun j=> digit (C.S.spacing (C.N (φ j))) 0) atTop (𝓝 0); simp only [digit_zero]; exact tendsto_const_nhds
                 exact (approaches hp K.coast).comp hφ
            have h:= (Z.symm.continuous.tendsto _).comp hU; rw [Z.symm_apply_apply] at h; exact h
        have hh:=Ability.turns (fun _:Fin 2=>d) V H W hs S (stage G d); apply (hh.comp (ride (fun i:ℕ=>i) F tendsto_id hf)).congr; intro j
        let U:= (C.A (φ j)).regulator.average; change U (List.ofFn (fun k: Fin 2=> stem P d (φ j) (W j k) (F j k))).prod = U ((K.heads (φ j) i 0)*(stem P d (φ j) (K.ridge (φ j) z) (Y (φ j)))); simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]; rfl
     have hy :∀ᶠ i in atTop, ‖z‖ ≤ (G d).J.J * ‖X i‖:=by filter_upwards [vision K,(approaches hp K.coast).eventually (closedBall_mem_nhds _ K.breadth)] with i hi hh; exact hi _ hh z
     exact le_of_tendsto_of_tendsto tendsto_const_nhds (ht.norm.const_mul _) (hφ.eventually hy)
lemma known {v:CellF d}(hx:∀ j, prism s d Z v j=0): v=0:= by apply norm_le_zero_iff.mp; simpa only [show prism s d Z v=0 from funext hx,norm_zero,mul_zero] using sparkle hp hφ s H d v
end Sash
end YM.Massive.Fir
#print axioms YM.Massive.Fir.Sash.known
